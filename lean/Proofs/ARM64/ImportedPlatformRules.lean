import Proofs.ARM64.ImportedStackBound
import Proofs.ARM64.ImportedCallerEntry
import Proofs.ARM64.ImportedLabeledCode

/-!
Finite platform rules for the exact SHA-256 image. The operand scanner covers
all explicit scalar data, destination, address and writeback registers and
fails closed on unsupported forms. Kernel checks establish that all 151 decoded
function words use neither X18 nor X29 and stay in the ordinary leaf vocabulary
without FP/SIMD, system instructions, software calls or atomics.

Actual observations are split at the 416-byte allocation and restoration. Those
instructions and RET have no data accesses; every data access in the middle
occurs with SP at the allocated frame bottom. Consequently a byte classified
inside this callee stack is never accessed below current SP. Heap/global
addresses numerically below SP are not prohibited.

The target/caller profile supplies frame-chain validity, asynchronous-handler
stack headroom, unwind registration, alias interpretation and stack ownership.
-/

namespace Crypto.ARM64.Imported

/-- All explicit GPR operands of supported scalar forms, including data,
destination and address/writeback operands. Unsupported forms fail closed. -/
def platformOperands : Arm64.Instr → Option (List Arm64.Reg)
  | .adr _ dst _ | .moveWide _ _ dst _ _ => some [dst]
  | .addSubImm _ _ dst src _ _ | .logicalImm _ _ dst src _
  | .bitfield _ _ dst src _ _ | .dataProc1 _ _ dst src => some [dst, src]
  | .extr _ dst src src2 _ | .logicalShift _ _ dst src src2 _ _
  | .addSubShift _ _ dst src src2 _ _ | .addSubExt _ _ dst src src2 _ _ => some [dst, src, src2]
  | .b .. | .bCond .. => some []
  | .cbz _ _ reg _ | .ret reg => some [reg]
  | .ldr _ _ _ reg addr | .str _ reg addr => some (reg :: platformAddressOperands addr)
  | .ldp _ _ reg reg2 addr | .stp _ reg reg2 addr => some (reg :: reg2 :: platformAddressOperands addr)
  | _ => none
where
  platformAddressOperands : Arm64.AddrMode → List Arm64.Reg
    | .Offset base _ | .UnscaledOffset base _ | .PreIndex base _ | .PostIndex base _ => [base]
    | .RegOffset base index _ _ => [base, index]

def platformInstruction (instruction : Arm64.Instr) : Bool :=
  permittedInstruction instruction &&
    ((platformOperands instruction).map (fun operands =>
      operands.all (fun reg => decide (reg ≠ Arm64.Reg.x18 ∧ reg ≠ Arm64.Reg.x29)))).getD false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_platform_rules : ∀ index : Fin 151,
    ((Arm64.decode imageWords[index.val]!).map platformInstruction).getD false = true := by
  decide +kernel

theorem decoded_platform_rules (index : Fin 151) (instruction : Arm64.Instr)
    (decoded : Arm64.decode imageWords[index.val]! = some instruction) :
    permittedInstruction instruction = true ∧ ∃ operands,
      platformOperands instruction = some operands ∧
      ∀ reg ∈ operands, reg ≠ Arm64.Reg.x18 ∧ reg ≠ Arm64.Reg.x29 := by
  have checked : platformInstruction instruction = true := by
    simpa only [decoded, Option.map_some, Option.getD_some] using image_platform_rules index
  simp only [platformInstruction, Bool.and_eq_true] at checked
  refine ⟨checked.1, ?_⟩
  cases scan : platformOperands instruction with
  | none => simp [scan] at checked
  | some operands =>
    have all : operands.all (fun reg => decide (reg ≠ Arm64.Reg.x18 ∧ reg ≠ Arm64.Reg.x29)) = true := by
      simpa only [scan, Option.map_some, Option.getD_some] using checked.2
    refine ⟨operands, rfl, ?_⟩
    intro reg member
    exact of_decide_eq_true (List.all_eq_true.mp all reg member)

theorem whole_call_platform_rules (count : BitVec 64) (word : BitVec 32)
    (member : word ∈ wholeCallCode count) (instruction : Arm64.Instr)
    (decoded : Arm64.decode word = some instruction) :
    permittedInstruction instruction = true ∧ ∃ operands,
      platformOperands instruction = some operands ∧
      ∀ reg ∈ operands, reg ≠ Arm64.Reg.x18 ∧ reg ≠ Arm64.Reg.x29 := by
  rw [← wholeCallIndices_words count] at member
  obtain ⟨index, present, same⟩ := List.mem_map.mp member
  subst word
  exact decoded_platform_rules ⟨index, wholeCallIndices_bounded count index present⟩ instruction decoded

set_option maxRecDepth 16384 in
theorem platform_allocate_no_accesses (s out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved [imageWords[0]!] s = some (out, observations)) :
    ∀ observation ∈ observations, observation.accesses = [] := by
  obtain ⟨state, values⟩ := stack_single_observation _ _ s out observations stack_allocate_decode observed
  intro observation member
  rw [values] at member
  have same : observation = instructionObservation (.addSubImm .W64 .SUB .sp .sp 416#12 false) s := by simpa using member
  subst observation
  rfl

set_option maxRecDepth 16384 in
theorem platform_restore_no_accesses (s out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved [imageWords[149]!, imageWords[150]!] s = some (out, observations)) :
    ∀ observation ∈ observations, observation.accesses = [] := by
  let restore : Arm64.Instr := .addSubImm .W64 .ADD .sp .sp 416#12 false
  let restored := Arm64.execInstWithSvc Arm64.noSyscalls restore s
  have result : Arm64.execInstWithSvc Arm64.noSyscalls (.ret .x30) restored = out ∧
      [instructionObservation restore s, instructionObservation (.ret .x30) restored] = observations := by
    simpa only [runWordsObserved, stack_restore_decode, stack_return_decode, Bind.bind, Option.bind,
      Option.bind_some, pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] using observed
  intro observation member
  rw [← result.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | last
  · subst observation; rfl
  · subst observation; rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem whole_call_accesses_allocated_sp (count : BitVec 64) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode count) s = some (out, observations)) :
    ∀ observation ∈ observations, ∀ access ∈ observation.accesses, observation.sp = entryStack s := by
  have executed : runWords (wholeCallCode count) s = some out := by
    rw [← runWordsObserved_erases _ s, observed]
    rfl
  have expanded := runWords_code_cast (wholeCallCode count)
    ([imageWords[0]!] ++ (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!])) s out
    (whole_call_stack_shape count) executed
  obtain ⟨allocated, allocateExec, suffixExec⟩ := runWords_append_split [imageWords[0]!]
    (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!]) s out expanded
  obtain ⟨middle, middleExec, restoreExec⟩ := runWords_append_split (stackMiddleCode count)
    [imageWords[149]!, imageWords[150]!] allocated out suffixExec
  obtain ⟨allocateObs, allocateObserved⟩ := runWords_observed [imageWords[0]!] s allocated allocateExec
  have allocateEmpty := platform_allocate_no_accesses s allocated allocateObs allocateObserved
  have allocatedSP := (stack_allocate_observations s allocated allocateObs allocateObserved).1
  obtain ⟨middleObs, middleObserved⟩ := runWords_observed (stackMiddleCode count) allocated middle middleExec
  have allMiddleSP := (runWordsObserved_stack_preserved (stackMiddleCode count) allocated middle middleObs
    (stack_middle_preserving count) middleObserved).2
  obtain ⟨restoreObs, restoreObserved⟩ := runWords_observed [imageWords[149]!, imageWords[150]!] middle out restoreExec
  have restoreEmpty := platform_restore_no_accesses middle out restoreObs restoreObserved
  have suffix := runWordsObserved_append_success (stackMiddleCode count) [imageWords[149]!, imageWords[150]!]
    allocated middle out middleObs restoreObs middleObserved restoreObserved
  have combined := runWordsObserved_append_success [imageWords[0]!]
    (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!]) s allocated out
    allocateObs (middleObs ++ restoreObs) allocateObserved suffix
  have whole := runWordsObserved_code_cast _ _ s out _ (whole_call_stack_shape count).symm combined
  have same : allocateObs ++ (middleObs ++ restoreObs) = observations :=
    (Prod.mk.inj (Option.some.inj (whole.symm.trans observed))).2
  intro observation member access present
  rw [← same] at member
  rcases List.mem_append.mp member with allocation | suffix
  · rw [allocateEmpty observation allocation] at present
    contradiction
  · rcases List.mem_append.mp suffix with middleMember | restoration
    · exact (allMiddleSP observation middleMember).1.trans allocatedSP
    · rw [restoreEmpty observation restoration] at present
      contradiction

/-- Only bytes classified inside the callee stack are constrained by SP.
This predicate intentionally does not reject heap/global addresses below SP. -/
def StackAccessNotBelowSP (before : Arm64.State) (observation : InstructionObservation) : Prop :=
  ∀ access ∈ observation.accesses, ∀ i, i < access.bytes →
    (callerStack before).Contains (access.address + BitVec.ofNat 64 i) →
    observation.sp.toNat ≤ (access.address + BitVec.ofNat 64 i).toNat

theorem whole_call_stack_not_below_sp (count : BitVec 64) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode count) s = some (out, observations)) :
    ∀ observation ∈ observations, StackAccessNotBelowSP s observation := by
  intro observation member access present i bound inside
  have sp := whole_call_accesses_allocated_sp count s out observations observed observation member access present
  rw [sp]
  exact inside.1

end Crypto.ARM64.Imported
