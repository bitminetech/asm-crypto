import Proofs.ARM64.ImportedAccess
import Proofs.ARM64.ImportedHashBodyFetch
import Proofs.ARM64.ImportedCallBounds

/-!
Stack-pointer trace bound for the exact SHA-256 instruction tape. A closed
kernel check identifies the image instructions that preserve SP; the only
changes are the recorded 416-byte allocation and restoration. The actual
imported execution observations therefore use exactly the caller SP or that
SP minus 416, and both endpoints of every step stay within the allocated frame
and remain aligned when the caller satisfies the stated bounds.
This is an SP trace result, separate from data-access footprints, concurrency,
confidentiality and the full architecture equal baseline.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local irreducible] runWords runWordsObserved

@[simp] theorem stack_sp_set_status (s : Arm64.State) (status : Arm64.ExecStatus) :
    (s.setStatus status).sp = s.sp := by cases s; rfl
@[simp] theorem stack_sp_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[simp] theorem stack_sp_set_pstate (s : Arm64.State) (p : Arm64.PState) :
    (s.setPState p).sp = s.sp := by cases s; rfl
@[simp] theorem stack_sp_write_reg64 (s : Arm64.State) (r : Arm64.Reg) (v : BitVec 64)
    (h : r ≠ .sp) : (s.writeReg64 r v).sp = s.sp := by
  cases r <;> simp_all [Arm64.State.writeReg64]
@[simp] theorem stack_sp_write_reg (s : Arm64.State) (w : Arm64.RegWidth) (r : Arm64.Reg) (v : BitVec 64)
    (h : r ≠ .sp) : (s.writeReg w r v).sp = s.sp := by
  simp only [Arm64.State.writeReg, stack_sp_write_reg64 s r _ h]

def stackNoWriteback : Arm64.AddrMode → Bool
  | .Offset .. | .UnscaledOffset .. | .RegOffset .. => true
  | _ => false

def stackPreservingInstruction : Arm64.Instr → Bool
  | .adr _ rd _ | .addSubImm _ _ rd _ _ _ | .logicalImm _ _ rd _ _
  | .moveWide _ _ rd _ _ | .bitfield _ _ rd _ _ _ | .extr _ rd _ _ _
  | .logicalShift _ _ rd _ _ _ _ | .addSubShift _ _ rd _ _ _ _
  | .addSubExt _ _ rd _ _ _ _ | .dataProc1 _ _ rd _ => decide (rd ≠ .sp)
  | .ldr _ _ _ rd addr => decide (rd ≠ .sp) && stackNoWriteback addr
  | .str _ _ addr | .stp _ _ _ addr => stackNoWriteback addr
  | .ldp _ _ rd1 rd2 addr => decide (rd1 ≠ .sp) && decide (rd2 ≠ .sp) && stackNoWriteback addr
  | .b .. | .bCond .. | .cbz .. | .ret .. => true
  | _ => false

theorem stack_ldr_sp (w : Arm64.RegWidth) (size : Arm64.MemWidth) (signed : Bool)
    (rd : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State)
    (h : rd ≠ .sp) (ha : stackNoWriteback addr = true) :
    (Arm64.execLdr w size signed rd addr s).sp = s.sp := by
  cases addr <;> simp only [stackNoWriteback, Bool.false_eq_true] at ha
  all_goals simp only [Arm64.execLdr, Arm64.evalAddrMode]
  all_goals repeat' split
  all_goals simp_all

theorem stack_str_sp (size : Arm64.MemWidth) (rd : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State)
    (ha : stackNoWriteback addr = true) : (Arm64.execStr size rd addr s).sp = s.sp := by
  cases addr <;> simp only [stackNoWriteback, Bool.false_eq_true] at ha
  all_goals simp only [Arm64.execStr, Arm64.evalAddrMode]
  all_goals repeat' split
  all_goals simp_all

theorem stack_ldp_sp (w : Arm64.RegWidth) (signed : Bool) (rd1 rd2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State)
    (h1 : rd1 ≠ .sp) (h2 : rd2 ≠ .sp) (ha : stackNoWriteback addr = true) :
    (Arm64.execLdp w signed rd1 rd2 addr s).sp = s.sp := by
  cases addr <;> simp only [stackNoWriteback, Bool.false_eq_true] at ha
  all_goals simp only [Arm64.execLdp, Arm64.evalAddrMode]
  all_goals repeat' split
  all_goals simp_all

theorem stack_stp_sp (w : Arm64.RegWidth) (rd1 rd2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) (ha : stackNoWriteback addr = true) :
    (Arm64.execStp w rd1 rd2 addr s).sp = s.sp := by
  cases addr <;> simp only [stackNoWriteback, Bool.false_eq_true] at ha
  all_goals simp only [Arm64.execStp, Arm64.evalAddrMode]
  all_goals repeat' split
  all_goals simp_all

theorem stack_preserving_sp (instruction : Arm64.Instr) (s : Arm64.State)
    (h : stackPreservingInstruction instruction = true) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).sp = s.sp := by
  cases instruction <;> simp only [stackPreservingInstruction, Bool.false_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift, Arm64.execAddSubShift,
    Arm64.execAddSubExt, Arm64.execDataProc1]
  all_goals try exact stack_ldr_sp _ _ _ _ _ _ h.1 h.2
  all_goals try exact stack_str_sp _ _ _ _ h
  all_goals try exact stack_ldp_sp _ _ _ _ _ _ h.1.1 h.1.2 h.2
  all_goals try exact stack_stp_sp _ _ _ _ _ h
  all_goals repeat' split
  all_goals simp_all

def StackPreservingWords (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ instruction, Arm64.decode word = some instruction → stackPreservingInstruction instruction = true

theorem StackPreservingWords.tail {word : BitVec 32} {rest : List (BitVec 32)}
    (h : StackPreservingWords (word :: rest)) : StackPreservingWords rest := by
  intro w member i decoded
  exact h w (by simp [member]) i decoded

theorem StackPreservingWords.append {xs ys : List (BitVec 32)}
    (left : StackPreservingWords xs) (right : StackPreservingWords ys) : StackPreservingWords (xs ++ ys) := by
  intro word member instruction decoded
  rcases List.mem_append.mp member with hl | hr
  · exact left word hl instruction decoded
  · exact right word hr instruction decoded

theorem StackPreservingWords.repeated {code : List (BitVec 32)} (h : StackPreservingWords code) (n : Nat) :
    StackPreservingWords (List.replicate n code).flatten := by
  induction n with
  | zero => intro word member; simp at member
  | succ n ih => simpa only [List.replicate_succ, List.flatten_cons] using h.append ih

theorem stack_preserving_words_of_all (words : List (BitVec 32))
    (h : (words.all fun word => ((Arm64.decode word).map stackPreservingInstruction).getD false) = true) :
    StackPreservingWords words := by
  intro word member instruction decoded
  have good := List.all_eq_true.mp h word member
  simpa only [decoded, Option.map_some, Option.getD_some] using good

theorem runWordsObserved_stack_preserved (words : List (BitVec 32)) (s out : Arm64.State)
    (observations : List InstructionObservation) (h : StackPreservingWords words)
    (observed : runWordsObserved words s = some (out, observations)) :
    out.sp = s.sp ∧ ∀ observation ∈ observations, observation.sp = s.sp ∧ observation.nextSP = s.sp := by
  induction words generalizing s observations with
  | nil =>
    simp only [runWordsObserved, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨rfl, rfl⟩ := observed
    exact ⟨rfl, by simp⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at observed
    | some instruction =>
      let after := Arm64.execInstWithSvc Arm64.noSyscalls instruction s
      cases tail : runWordsObserved rest after with
      | none => simp [runWordsObserved, decoded, after, tail] at observed
      | some result =>
        rcases result with ⟨actualOut, tailObs⟩
        have tailExec : runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some (actualOut, tailObs) := tail
        have equal : actualOut = out ∧ instructionObservation instruction s :: tailObs = observations := by
          simpa only [runWordsObserved, decoded, Bind.bind, Option.bind, tailExec, pure, Pure.pure,
            Option.some.injEq, Prod.mk.injEq] using observed
        rcases equal with ⟨rfl, rfl⟩
        have stepSP : after.sp = s.sp := stack_preserving_sp instruction s (h word (by simp) instruction decoded)
        obtain ⟨outSP, all⟩ := ih after tailObs h.tail tail
        refine ⟨outSP.trans stepSP, ?_⟩
        intro observation member
        rcases List.mem_cons.mp member with head | restMember
        · subst observation
          exact ⟨rfl, stepSP⟩
        · obtain ⟨sp, nextSP⟩ := all observation restMember
          exact ⟨sp.trans stepSP, nextSP.trans stepSP⟩

theorem runWordsObserved_append (xs ys : List (BitVec 32)) (s : Arm64.State) :
    runWordsObserved (xs ++ ys) s = (runWordsObserved xs s).bind (fun first =>
      (runWordsObserved ys first.1).map (fun last => (last.1, first.2 ++ last.2))) := by
  induction xs generalizing s with
  | nil => simp [runWordsObserved]
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded]
    | some instruction =>
      simp only [List.cons_append, runWordsObserved, decoded, Bind.bind, Option.bind]
      rw [ih]
      cases first : runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) with
      | none => simp
      | some pair =>
        rcases pair with ⟨mid, left⟩
        cases last : runWordsObserved ys mid with
        | none => simp [last]
        | some pair =>
          rcases pair with ⟨out, right⟩
          simp [last]

theorem runWordsObserved_append_success (xs ys : List (BitVec 32)) (s mid out : Arm64.State)
    (left right : List InstructionObservation)
    (hl : runWordsObserved xs s = some (mid, left)) (hr : runWordsObserved ys mid = some (out, right)) :
    runWordsObserved (xs ++ ys) s = some (out, left ++ right) := by
  rw [runWordsObserved_append, hl]
  simp only [Option.bind_some, hr, Option.map_some]

theorem runWordsObserved_code_cast (left right : List (BitVec 32)) (s out : Arm64.State)
    (observations : List InstructionObservation) (equal : left = right)
    (observed : runWordsObserved left s = some (out, observations)) :
    runWordsObserved right s = some (out, observations) := by
  cases equal
  exact observed


theorem stack_image_preserving : ∀ i : Fin 151, i.val ≠ 0 → i.val ≠ 149 →
    ((Arm64.decode imageWords[i.val]!).map stackPreservingInstruction).getD false = true := by
  decide +kernel

def stackMiddleCode (count : BitVec 64) := imageSlice 1 3 ++ (preparePaddingCode count ++
  (hashInitCode ++ (hashPhasesCode (count.toNat / 64) (if count.toNat % 64 < 56 then 1 else 2) ++ imageSlice 131 18)))

theorem stack_middle_preserving (count : BitVec 64) : StackPreservingWords (stackMiddleCode count) := by
  have headerTail : StackPreservingWords (imageSlice 1 3) := stack_preserving_words_of_all _ (by decide +kernel)
  have zero : StackPreservingWords (zeroPadCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have setup : StackPreservingWords (paddingSetupCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have tailCycle : StackPreservingWords (tailCopyCycleCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have tailEnd : StackPreservingWords (tailCopyEndCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have marker : StackPreservingWords (markerCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have length : StackPreservingWords (lengthCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have init : StackPreservingWords (hashInitCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have word : StackPreservingWords (wordCycleCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have schedule : StackPreservingWords (scheduleCycleCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have round : StackPreservingWords (roundCycleCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have initial : StackPreservingWords (initialLoadCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have feed : StackPreservingWords (feedForwardCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have blockGate : StackPreservingWords (blockGateCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have advance : StackPreservingWords (blockAdvanceCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have skip : StackPreservingWords (blockSkipCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have phase : StackPreservingWords (paddingPhaseCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have digestGate : StackPreservingWords (digestGateCode) := stack_preserving_words_of_all _ (by decide +kernel)
  have exitPrefix : StackPreservingWords (imageSlice 131 18) := stack_preserving_words_of_all _ (by decide +kernel)
  have paddingCount (small : Bool) : StackPreservingWords (paddingCountCode small) := by
    cases small <;> exact stack_preserving_words_of_all _ (by decide +kernel)
  have tail (rem : Nat) : StackPreservingWords (tailCopyCode rem) := (tailCycle.repeated rem).append tailEnd
  have prepareTail (rem : Nat) : StackPreservingWords (prepareTailCode rem) := zero.append (setup.append (tail rem))
  have padSuffix (rem : Nat) : StackPreservingWords (paddingSuffixCode rem) := marker.append ((paddingCount _).append length)
  have padding : StackPreservingWords (preparePaddingCode count) := (prepareTail _).append (padSuffix _)
  have compression : StackPreservingWords compressionCode := initial.append ((round.repeated 64).append feed)
  have block : StackPreservingWords blockCode := (word.repeated 16).append ((schedule.repeated 48).append compression)
  have iteration : StackPreservingWords blockIterationCode := blockGate.append (block.append advance)
  have outer (n : Nat) : StackPreservingWords (outerLoopCode n) := (iteration.repeated n).append skip
  have phases (full pad : Nat) : StackPreservingWords (hashPhasesCode full pad) :=
    (outer full).append (phase.append ((outer pad).append digestGate))
  exact headerTail.append (padding.append (init.append ((phases _ _).append exitPrefix)))

theorem stack_header_shape : headerCode = [imageWords[0]!] ++ imageSlice 1 3 := by decide +kernel

theorem stack_exit_shape : exitCode = imageSlice 131 18 ++ [imageWords[149]!, imageWords[150]!] := by decide +kernel

theorem whole_call_stack_shape (count : BitVec 64) : wholeCallCode count =
    [imageWords[0]!] ++ (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!]) := by
  simp only [wholeCallCode, hashBodyCode, stackMiddleCode, stack_header_shape, stack_exit_shape, List.append_assoc]

theorem stack_allocate_decode : Arm64.decode imageWords[0]! = some (.addSubImm .W64 .SUB .sp .sp 416#12 false) := by decide +kernel

theorem stack_restore_decode : Arm64.decode imageWords[149]! = some (.addSubImm .W64 .ADD .sp .sp 416#12 false) := by decide +kernel

theorem stack_return_decode : Arm64.decode imageWords[150]! = some (.ret .x30) := by decide +kernel

theorem stack_allocate_sp (s : Arm64.State) :
    (Arm64.execInstWithSvc Arm64.noSyscalls (.addSubImm .W64 .SUB .sp .sp 416#12 false) s).sp = s.sp - 416#64 := by
  simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg,
    Arm64.State.writeReg, BitVec.truncate_eq_setWidth, subtract416]

theorem stack_restore_sp (s : Arm64.State) :
    (Arm64.execInstWithSvc Arm64.noSyscalls (.addSubImm .W64 .ADD .sp .sp 416#12 false) s).sp = s.sp + 416#64 := by
  simp [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg,
    Arm64.State.writeReg, BitVec.truncate_eq_setWidth, addWithCarry64_add]

def StackPositions (top : BitVec 64) (observation : InstructionObservation) : Prop :=
  (observation.sp = top ∨ observation.sp = top - 416#64) ∧
    (observation.nextSP = top ∨ observation.nextSP = top - 416#64)

theorem stack_single_observation (word : BitVec 32) (instruction : Arm64.Instr) (s out : Arm64.State)
    (observations : List InstructionObservation) (decoded : Arm64.decode word = some instruction)
    (observed : runWordsObserved [word] s = some (out, observations)) :
    out = Arm64.execInstWithSvc Arm64.noSyscalls instruction s ∧ observations = [instructionObservation instruction s] := by
  have result : Arm64.execInstWithSvc Arm64.noSyscalls instruction s = out ∧ [instructionObservation instruction s] = observations := by
    simpa only [runWordsObserved, decoded, Bind.bind, Option.bind, Option.bind_some, pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] using observed
  exact ⟨result.1.symm, result.2.symm⟩

theorem stack_allocate_observations (s out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved [imageWords[0]!] s = some (out, observations)) :
    out.sp = s.sp - 416#64 ∧ ∀ observation ∈ observations, StackPositions s.sp observation := by
  obtain ⟨state, obs⟩ := stack_single_observation _ _ s out observations stack_allocate_decode observed
  refine ⟨?_, ?_⟩
  · rw [state]; exact stack_allocate_sp s
  · intro observation member
    rw [obs] at member
    have equal : observation = instructionObservation (.addSubImm .W64 .SUB .sp .sp 416#12 false) s := by simpa using member
    subst observation
    exact ⟨Or.inl rfl, Or.inr (stack_allocate_sp s)⟩

theorem stack_restore_observations (top : BitVec 64) (s out : Arm64.State) (observations : List InstructionObservation)
    (sp : s.sp = top - 416#64)
    (observed : runWordsObserved [imageWords[149]!, imageWords[150]!] s = some (out, observations)) :
    ∀ observation ∈ observations, StackPositions top observation := by
  let restore : Arm64.Instr := .addSubImm .W64 .ADD .sp .sp 416#12 false
  let restored := Arm64.execInstWithSvc Arm64.noSyscalls restore s
  have restoredSP : restored.sp = top := by
    rw [stack_restore_sp, sp, BitVec.sub_add_cancel]
  have obs : observations = [instructionObservation restore s, instructionObservation (.ret .x30) restored] := by
    have result : Arm64.execInstWithSvc Arm64.noSyscalls (.ret .x30) restored = out ∧
        [instructionObservation restore s, instructionObservation (.ret .x30) restored] = observations := by
      simpa only [runWordsObserved, stack_restore_decode, stack_return_decode, Bind.bind, Option.bind, Option.bind_some,
        pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] using observed
    exact result.2.symm
  intro observation member
  rw [obs] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second
  · subst observation
    exact ⟨Or.inr sp, Or.inl restoredSP⟩
  · subst observation
    refine ⟨Or.inl restoredSP, Or.inl ?_⟩
    change (restored.setPC (restored.readReg64 .x30)).sp = top
    exact (sp_set_pc _ _).trans restoredSP

theorem whole_call_stack_positions (count : BitVec 64) (s out : Arm64.State)
    (executed : runWords (wholeCallCode count) s = some out) :
    ∃ observations, runWordsObserved (wholeCallCode count) s = some (out, observations) ∧
      ∀ observation ∈ observations, StackPositions s.sp observation := by
  have expanded := runWords_code_cast (wholeCallCode count)
    ([imageWords[0]!] ++ (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!])) s out
    (whole_call_stack_shape count) executed
  obtain ⟨allocated, allocateExec, restExec⟩ := runWords_append_split [imageWords[0]!]
    (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!]) s out expanded
  obtain ⟨middle, middleExec, restoreExec⟩ := runWords_append_split (stackMiddleCode count)
    [imageWords[149]!, imageWords[150]!] allocated out restExec
  obtain ⟨allocateObs, allocateObserved⟩ := runWords_observed [imageWords[0]!] s allocated allocateExec
  obtain ⟨allocatedSP, allocationPositions⟩ := stack_allocate_observations s allocated allocateObs allocateObserved
  obtain ⟨middleObs, middleObserved⟩ := runWords_observed (stackMiddleCode count) allocated middle middleExec
  obtain ⟨middleSP, allMiddleSP⟩ := runWordsObserved_stack_preserved (stackMiddleCode count) allocated middle middleObs
    (stack_middle_preserving count) middleObserved
  obtain ⟨restoreObs, restoreObserved⟩ := runWords_observed [imageWords[149]!, imageWords[150]!] middle out restoreExec
  have restorationPositions := stack_restore_observations s.sp middle out restoreObs (middleSP.trans allocatedSP) restoreObserved
  have suffix := runWordsObserved_append_success (stackMiddleCode count) [imageWords[149]!, imageWords[150]!]
    allocated middle out middleObs restoreObs middleObserved restoreObserved
  have combined := runWordsObserved_append_success [imageWords[0]!]
    (stackMiddleCode count ++ [imageWords[149]!, imageWords[150]!]) s allocated out
    allocateObs (middleObs ++ restoreObs) allocateObserved suffix
  refine ⟨allocateObs ++ (middleObs ++ restoreObs),
    runWordsObserved_code_cast _ _ s out _ (whole_call_stack_shape count).symm combined, ?_⟩
  intro observation member
  rcases List.mem_append.mp member with allocation | rest
  · exact allocationPositions observation allocation
  · rcases List.mem_append.mp rest with middleMember | restoration
    · obtain ⟨sp, nextSP⟩ := allMiddleSP observation middleMember
      exact ⟨Or.inr (sp.trans allocatedSP), Or.inr (nextSP.trans allocatedSP)⟩
    · exact restorationPositions observation restoration

theorem stack_bottom_toNat (top : BitVec 64) (bound : 416 ≤ top.toNat) :
    (top - 416#64).toNat = top.toNat - 416 := by
  have le : 416#64 ≤ top := by simpa only [BitVec.le_def] using bound
  simpa using BitVec.toNat_sub_of_le le

theorem stack_positions_bounded (top : BitVec 64) (observation : InstructionObservation)
    (positions : StackPositions top observation) (bound : 416 ≤ top.toNat)
    (aligned : top.toNat % 16 = 0) :
    top.toNat - 416 ≤ observation.sp.toNat ∧ observation.sp.toNat ≤ top.toNat ∧
      top.toNat - 416 ≤ observation.nextSP.toNat ∧ observation.nextSP.toNat ≤ top.toNat ∧
      observation.sp.toNat % 16 = 0 ∧ observation.nextSP.toNat % 16 = 0 := by
  obtain ⟨before, after⟩ := positions
  rcases before with before | before <;> rcases after with after | after
  all_goals rw [before, after]
  all_goals try simp only [stack_bottom_toNat top bound]
  all_goals omega

theorem whole_call_observed_stack_bound (count : BitVec 64) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode count) s = some (out, observations))
    (bound : 416 ≤ s.sp.toNat) (aligned : s.sp.toNat % 16 = 0) :
    ∀ observation ∈ observations,
      s.sp.toNat - 416 ≤ observation.sp.toNat ∧ observation.sp.toNat ≤ s.sp.toNat ∧
      s.sp.toNat - 416 ≤ observation.nextSP.toNat ∧ observation.nextSP.toNat ≤ s.sp.toNat ∧
      observation.sp.toNat % 16 = 0 ∧ observation.nextSP.toNat % 16 = 0 := by
  have executed : runWords (wholeCallCode count) s = some out := by
    rw [← runWordsObserved_erases (wholeCallCode count) s, observed]
    rfl
  obtain ⟨known, native, positions⟩ := whole_call_stack_positions count s out executed
  have same : known = observations := (Prod.mk.inj (Option.some.inj (native.symm.trans observed))).2
  subst known
  intro observation member
  exact stack_positions_bounded s.sp observation (positions observation member) bound aligned

end Crypto.ARM64.Imported
