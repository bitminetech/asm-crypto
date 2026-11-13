import Proofs.ARM64.ImportedABI
import Proofs.ARM64.ImportedStrictReadTrace
import Proofs.ARM64.ImportedFetchBounds
import Proofs.ARM64.ImportedPlatformRules
import Proofs.ARM64.ImportedInstructionLocality

/-!
Serial guarantees for one actual SHA-256 execution and its observations. The
arbitrary FPCR value is carried in the restricted scalar frame. The target
profile supplies physical FPCR/ISA correspondence. NativeEqual combines these
serial results with concurrency, timing and disclosure guarantees.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem serial_observed_length (words : List (BitVec 32)) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved words s = some (out, observations)) :
    observations.length = words.length := by
  induction words generalizing s observations with
  | nil =>
    have same : s = out ∧ [] = observations := by
      simpa only [runWordsObserved, Option.some.injEq, Prod.mk.injEq] using observed
    rw [← same.2]
    rfl
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at observed
    | some instruction =>
      obtain ⟨tailObs, tailExec, shape⟩ := labeled_observed_cons word rest s out observations instruction decoded observed
      rw [shape, List.length_cons, List.length_cons, ih _ tailObs tailExec]

theorem serial_runWords_global_tail (words : List (BitVec 32)) (s out : Arm64.State)
    (permitted : PermittedWords words) (executed : runWords words s = some out) :
    GlobalTail out = GlobalTail s := by
  induction words generalizing s with
  | nil =>
    have same : s = out := by simpa only [runWords, Option.some.injEq] using executed
    rw [same]
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      exact (ih _ permitted.tail executed).trans
        (permitted_global_tail instruction (permitted word (by simp) instruction decoded) s)

/-- The framed witness is identified by the deterministic bounded evaluator,
so its final CPU is the same final CPU selected by LogicalCallResult. -/
theorem serial_same_framed_result (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (authority : Crypto.Baseline.Authority)
    (out : Arm64.State) (observations : List InstructionObservation) (fpcr : BitVec 32)
    (inputs : CallInputs base (logicalState base s message) message.bytes)
    (safe : LogicalCallResult base s message authority out observations) :
    Crypto.ARM64.CallFrame.FramedReturn base (512 + 4000 * ((message.bytes.size + 8) / 64 + 1))
      ⟨logicalState base s message, fpcr⟩ ⟨out, fpcr⟩ := by
  obtain ⟨after, framed, _, fpcrSame, _⟩ := sha256_framed base (logicalState base s message) message.bytes fpcr inputs
  have sameCPU : after.cpu = out := Option.some.inj (framed.native_result.symm.trans safe.returned)
  have same : after = ⟨out, fpcr⟩ := by
    cases after with
    | mk cpu control =>
      change cpu = out at sameCPU
      change control = fpcr at fpcrSame
      subst cpu
      subst control
      rfl
  rw [same] at framed
  exact framed

structure SerialCallResult (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (fpcr : BitVec 32) (out : Arm64.State) (observations : List InstructionObservation) : Prop where
  safe : LogicalCallResult base s message authority out observations
  framed : Crypto.ARM64.CallFrame.FramedReturn base (512 + 4000 * ((message.bytes.size + 8) / 64 + 1))
    ⟨logicalState base s message, fpcr⟩ ⟨out, fpcr⟩
  cpuABI : ModeledCPUABI s out
  strictData : ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) observations
  functionFetches : ∀ observation ∈ observations, ∀ byte, byte < 4 →
    (callerFunction base).Contains (observation.pc + BitVec.ofNat 64 byte)
  scalar : ScalarWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
  platform : ∀ word ∈ wholeCallCode (BitVec.ofNat 64 message.bytes.size), ∀ instruction,
    Arm64.decode word = some instruction → permittedInstruction instruction = true ∧ ∃ operands,
      platformOperands instruction = some operands ∧
      ∀ reg ∈ operands, reg ≠ Arm64.Reg.x18 ∧ reg ≠ Arm64.Reg.x29
  stackAccess : ∀ observation ∈ observations, StackAccessNotBelowSP s observation
  globals : GlobalTail out = GlobalTail s
  inputPreserved : ∀ p, (callerInput s extent).Contains p → out.mem.read8 p = s.mem.read8 p
  imagePreserved : ∀ p, (callerImage base).Contains p → out.mem.read8 p = s.mem.read8 p
  observationLength : observations.length = (wholeCallCode (BitVec.ofNat 64 message.bytes.size)).length
  instructionBound : observations.length ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1)

theorem sha256_serial_contract (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (fpcr : BitVec 32) (entry : PermissionViewInputs base s message extent authority) :
    ∃ out observations, SerialCallResult base s message extent authority fpcr out observations := by
  obtain ⟨out, observations, safe⟩ := sha256_logical_safe base s message extent authority entry
  have inputs := permission_view_inputs base s message extent authority entry
  have executed : runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
      (logicalState base s message) = some out := by
    rw [← runWordsObserved_erases _ (logicalState base s message), safe.observed]
    rfl
  have length := serial_observed_length _ _ _ _ safe.observed
  have countBound : message.bytes.size < 2 ^ 64 := by have := entry.length; omega
  have budget : (wholeCallCode (BitVec.ofNat 64 message.bytes.size)).length ≤
      512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] using
      whole_call_code_bound (BitVec.ofNat 64 message.bytes.size)
  refine ⟨out, observations, safe, serial_same_framed_result base s message authority out observations fpcr inputs safe,
    modeled_cpu_abi s out safe.state safe.nonvolatile safe.stackRestored,
    sha256_strict_read_footprint base s message extent authority entry out observations safe.observed,
    whole_call_function_fetches base (logicalState base s message) out message.bytes inputs observations safe.observed,
    whole_call_scalar_words _, whole_call_platform_rules _, ?_, ?_, ?_, ?_, length, length.le.trans budget⟩
  · have bounds := whole_call_stack_not_below_sp _ (logicalState base s message) out observations safe.observed
    exact bounds
  · have tail := serial_runWords_global_tail _ _ out (whole_call_permitted _) executed
    have unchanged : GlobalTail (logicalState base s message) = GlobalTail s := by cases s; rfl
    exact tail.trans unchanged
  · intro p inside
    apply safe.finalMemory p
    · exact caller_outside_delta (callerStack s) entry.stackValid p (fun held => entry.stackInput p ⟨held, inside⟩)
    · exact caller_outside_delta (callerOutput s) entry.outputValid p (fun held => entry.outputInput p ⟨held, inside⟩)
  · intro p inside
    apply safe.finalMemory p
    · exact caller_outside_delta (callerStack s) entry.stackValid p (fun held => entry.stackImage p ⟨held, inside⟩)
    · exact caller_outside_delta (callerOutput s) entry.outputValid p (fun held => entry.outputImage p ⟨held, inside⟩)

end Crypto.ARM64.Imported
