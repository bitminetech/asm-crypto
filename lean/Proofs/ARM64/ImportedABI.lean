import Models.ARM64CallFrame
import Proofs.ARM64.ImportedVerifiedCall
import Proofs.ARM64.ImportedLabeledCode

/-!
ABI and arbitrary-FPCR framing for the actual bounded SHA-256 call. CPU steps
and bounded return project to the unchanged imported execution, and every
framed step is restricted to an ordinary decoded function-image instruction.
The existing returnStable/nonvolatile/SP result supplies all modeled CPU
preservation; the full vector file is preserved, including AAPCS64 D8-D15.

The FPCR extension carries arbitrary values without an FPCR=0 entry assumption.
Its hardware meaning requires the separately named HardwareFPCRFrames and
native ISA correspondence assumptions. The extension's preservation theorem
must not be represented as a physical FPCR proof from the missing upstream
field. Physical/OS profiles, unwinding and the full equal baseline remain
separate obligations. No upstream model is changed and no axiom is added.
-/

namespace Crypto.ARM64.CallFrame

theorem Step.cpu_step {base : BitVec 64} {before after : State} (step : Step base before after) :
    Arm64.Step (Imported.program base) before.cpu after.cpu := by
  cases step with
  | exec instruction running fetched admitted => exact Arm64.Step.exec running fetched

theorem Step.fpcr_preserved {base : BitVec 64} {before after : State} (step : Step base before after) :
    after.fpcr = before.fpcr := by cases step; rfl

theorem Steps.cpu_steps {base : BitVec 64} {before after : State} (steps : Steps base before after) :
    Arm64.Steps (Imported.program base) before.cpu after.cpu := by
  induction steps with
  | refl before => exact Arm64.Steps.refl _
  | step first rest ih => exact Arm64.Steps.step first.cpu_step ih

theorem Steps.fpcr_preserved {base : BitVec 64} {before after : State} (steps : Steps base before after) :
    after.fpcr = before.fpcr := by
  induction steps with
  | refl before => rfl
  | step first rest ih => exact ih.trans first.fpcr_preserved

theorem FramedReturn.native_result {base : BitVec 64} {fuel : Nat} {before after : State}
    (returned : FramedReturn base fuel before after) :
    Imported.runToReturn (Imported.program base) fuel before.cpu = some after.cpu := returned.1

theorem FramedReturn.native_steps {base : BitVec 64} {fuel : Nat} {before after : State}
    (returned : FramedReturn base fuel before after) : Arm64.Steps (Imported.program base) before.cpu after.cpu :=
  returned.2.cpu_steps

theorem FramedReturn.fpcr_preserved {base : BitVec 64} {fuel : Nat} {before after : State}
    (returned : FramedReturn base fuel before after) : after.fpcr = before.fpcr := returned.2.fpcr_preserved

/-- A supplied extended/physical step lifts only with its explicit FPCR framing
assumption and its unchanged imported CPU projection. No hardware instance or
proof of the assumption is invented here. -/
theorem step_of_hardware_conformance (base : BitVec 64)
    (hardwareStep : Arm64.Instr → State → State → Prop)
    (frames : HardwareFPCRFrames hardwareStep) (instruction : Arm64.Instr) (before after : State)
    (actual : hardwareStep instruction before after) (admitted : Admissible instruction)
    (running : before.cpu.status = .Running)
    (fetched : (Imported.program base).fetchMem before.cpu.mem before.cpu.pc = some instruction)
    (cpu : after.cpu = (Imported.program base).evalInst instruction before.cpu) : Step base before after := by
  have fpcr := frames instruction before after admitted actual
  have same : after = ⟨(Imported.program base).evalInst instruction before.cpu, before.fpcr⟩ := by
    cases after
    simp_all
  rw [same]
  exact Step.exec before instruction running fetched admitted

end Crypto.ARM64.CallFrame

namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem scalar_family_permitted (instruction : Arm64.Instr) :
    CallFrame.ordinaryScalar instruction = permittedInstruction instruction := by cases instruction <;> rfl

theorem scalar_admissible_image (index : Fin 151) (instruction : Arm64.Instr)
    (decoded : Arm64.decode imageWords[index.val]! = some instruction) : CallFrame.Admissible instruction := by
  exact ⟨(scalar_family_permitted instruction).trans (image_permitted index instruction decoded), index, decoded⟩

def ScalarWords (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ instruction, Arm64.decode word = some instruction → CallFrame.Admissible instruction

theorem ScalarWords.tail {word : BitVec 32} {rest : List (BitVec 32)}
    (admitted : ScalarWords (word :: rest)) : ScalarWords rest := by
  intro w member instruction decoded
  exact admitted w (by simp [member]) instruction decoded

theorem whole_call_scalar_words (count : BitVec 64) : ScalarWords (wholeCallCode count) := by
  intro word member instruction decoded
  rw [← wholeCallIndices_words count] at member
  obtain ⟨index, present, same⟩ := List.mem_map.mp member
  subst word
  exact scalar_admissible_image ⟨index, wholeCallIndices_bounded count index present⟩ instruction decoded

theorem scalar_words_steps (base : BitVec 64) (words : List (BitVec 32)) (s out : Arm64.State)
    (fpcr : BitVec 32) (permitted : PermittedWords words) (admitted : ScalarWords words)
    (loaded : (program base).CodeLoaded s.mem) (executed : runWords words s = some out)
    (path : StaticPath base words s) (running : out.status = .Running) :
    CallFrame.Steps base ⟨s, fpcr⟩ ⟨out, fpcr⟩ := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact CallFrame.Steps.refl _
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have allowed := permitted word (by simp) instruction decoded
      have nextRunning := runWords_running_before rest _ out permitted.tail executed running
      have beforeRunning := permitted_running_before instruction allowed s nextRunning
      have parts : (program base).fetch s.pc = some instruction ∧
          StaticPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [StaticPath, decoded] using path
      have first : CallFrame.Step base ⟨s, fpcr⟩ ⟨Arm64.execInstWithSvc Arm64.noSyscalls instruction s, fpcr⟩ := by
        have native := CallFrame.Step.exec (base := base) ⟨s, fpcr⟩ instruction beforeRunning
          (loaded_fetch_of_fetch loaded parts.1) (admitted word (by simp) instruction decoded)
        simpa only [evalInst_permitted base instruction allowed] using native
      exact CallFrame.Steps.step first
        (ih _ permitted.tail admitted.tail (permitted_codeLoaded instruction allowed s loaded) executed parts.2)

/-- Preservation of modeled CPU ABI fields. Full vector preservation is
stronger than the AAPCS64 D8-D15 low64 requirement; no FPCR field is inferred
from the upstream state. The separate scalar frame supplies that obligation. -/
structure ModeledCPUABI (before after : Arm64.State) : Prop where
  nonvolatile : Crypto.ARM64.Imported.nonvolatile after = Crypto.ARM64.Imported.nonvolatile before
  stack : after.sp = before.sp
  vectors : after.vregs = before.vregs
  fpsr : after.fpsr = before.fpsr
  threadPointer : after.tpidrEl0 = before.tpidrEl0

theorem modeled_cpu_abi (before after : Arm64.State)
    (stable : returnStable after = returnStable before)
    (nonvolatile : Crypto.ARM64.Imported.nonvolatile after = Crypto.ARM64.Imported.nonvolatile before)
    (stack : after.sp = before.sp) : ModeledCPUABI before after := by
  have vectors := congrArg Arm64.State.vregs stable
  have fpsr := congrArg Arm64.State.fpsr stable
  have tls := congrArg Arm64.State.tpidrEl0 stable
  change after.vregs = before.vregs at vectors
  change after.fpsr = before.fpsr at fpsr
  change after.tpidrEl0 = before.tpidrEl0 at tls
  exact ⟨nonvolatile, stack, vectors, fpsr, tls⟩

theorem ModeledCPUABI.x18_to_x30 {before after : Arm64.State} (abi : ModeledCPUABI before after)
    (index : Fin 31) (bound : 18 ≤ index.val) :
    after.readReg64 (.gpr (BitVec.ofNat 5 index.val)) = before.readReg64 (.gpr (BitVec.ofNat 5 index.val)) := by
  have values := congrFun abi.nonvolatile ⟨index.val - 18, by have := index.isLt; omega⟩
  change after.readReg64 (.gpr (BitVec.ofNat 5 (18 + (index.val - 18)))) =
    before.readReg64 (.gpr (BitVec.ofNat 5 (18 + (index.val - 18)))) at values
  have same : 18 + (index.val - 18) = index.val := by omega
  simpa only [same] using values

theorem ModeledCPUABI.d8_to_d15 {before after : Arm64.State} (abi : ModeledCPUABI before after)
    (index : Fin 8) :
    after.readVReg64 (BitVec.ofNat 5 (8 + index.val)) = before.readVReg64 (BitVec.ofNat 5 (8 + index.val)) := by
  simp only [Arm64.State.readVReg64, Arm64.State.readVReg128, abi.vectors]

/-- All initial FPCR bit patterns are admitted. CPU execution is the original
bounded evaluator and all framed steps use actual fetched image instructions.
Physical FPCR preservation additionally requires HardwareFPCRFrames plus native
hardware/ISA correspondence; this is a theorem in the restricted scalar frame. -/
theorem sha256_framed (base : BitVec 64) (s : Arm64.State) (data : ByteArray) (fpcr : BitVec 32)
    (entry : CallInputs base s data) :
    ∃ after : CallFrame.State,
      CallFrame.FramedReturn base (512 + 4000 * ((data.size + 8) / 64 + 1)) ⟨s, fpcr⟩ after ∧
      ModeledCPUABI s after.cpu ∧ after.fpcr = fpcr ∧
      after.cpu.pc = s.readReg64 .x30 ∧ after.cpu.readReg64 .x0 = 0#64 ∧ after.cpu.status = .Running ∧
      memoryBytes32 after.cpu.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
  obtain ⟨out, returned, steps, state, nv, sp, pc, zero, running, digest, frame, access, observations, observed⟩ :=
    sha256_fetched base s data entry
  have erased := runWordsObserved_erases (wholeCallCode (BitVec.ofNat 64 data.size)) s
  rw [observed] at erased
  have executed : runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out := erased.symm
  have path := whole_call_staticPath base s data entry out executed running
  have framed := scalar_words_steps base (wholeCallCode (BitVec.ofNat 64 data.size)) s out fpcr
    (whole_call_permitted _) (whole_call_scalar_words _) entry.loaded executed path running
  exact ⟨⟨out, fpcr⟩, ⟨returned, framed⟩, modeled_cpu_abi s out state nv sp, rfl, pc, zero, running, digest⟩

end Crypto.ARM64.Imported
