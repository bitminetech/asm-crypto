import Models.ARM64

/-!
Restricted scalar framing extension for the exact 151 SHA-256 instruction words.
The upstream CPU state has no FPCR field. This extension carries an arbitrary
32-bit FPCR alongside that unchanged CPU state. Each admitted step performs
exactly the imported memory fetch/eval step and frames FPCR; other instruction
forms have no step in this restricted relation.

Hardware correspondence requires the explicit scalar-FPCR framing assumption:
every admitted concrete instruction leaves physical FPCR unchanged, and the
hardware CPU projection conforms to the imported ISA. Neither follows from
an absent upstream field. This file proves no physical hardware conformance,
adds no axiom and imposes no FPCR=0 precondition. No upstream model is changed.
-/
namespace Crypto.ARM64.CallFrame

structure State where
  cpu : Arm64.State
  fpcr : BitVec 32

/-- Syntactic scalar-domain restriction, excluding FP/SIMD, system-register
accesses, syscalls, software calls and atomics. -/
def ordinaryScalar : Arm64.Instr → Bool
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield ..
  | .extr .. | .b .. | .bCond .. | .cbz .. | .ret .. | .logicalShift ..
  | .addSubShift .. | .addSubExt .. | .dataProc1 .. | .ldr .. | .str ..
  | .ldp .. | .stp .. => true
  | _ => false

/-- The extension is restricted to concrete decoded function-image forms. -/
def Admissible (instruction : Arm64.Instr) : Prop :=
  ordinaryScalar instruction = true ∧
  ∃ index : Fin 151, Arm64.decode imageWords[index.val]! = some instruction

inductive Step (base : BitVec 64) : State → State → Prop where
  | exec (before : State) (instruction : Arm64.Instr)
      (running : before.cpu.status = .Running)
      (fetched : (Imported.program base).fetchMem before.cpu.mem before.cpu.pc = some instruction)
      (admitted : Admissible instruction) :
      Step base before ⟨(Imported.program base).evalInst instruction before.cpu, before.fpcr⟩

inductive Steps (base : BitVec 64) : State → State → Prop where
  | refl (before : State) : Steps base before before
  | step {before middle after : State} (first : Step base before middle)
      (rest : Steps base middle after) : Steps base before after

/-- The bounded result is literally the existing native evaluator. The second
conjunct records its restriction to the admissible scalar framing domain. -/
def FramedReturn (base : BitVec 64) (fuel : Nat) (before after : State) : Prop :=
  Imported.runToReturn (Imported.program base) fuel before.cpu = some after.cpu ∧
    Steps base before after

/-- Required profile assumption for a supplied physical/extended transition
relation. This predicate states the missing-field framing obligation explicitly;
no value of it is asserted here and no physical transition model is supplied. -/
def HardwareFPCRFrames (hardwareStep : Arm64.Instr → State → State → Prop) : Prop :=
  ∀ instruction before after, Admissible instruction → hardwareStep instruction before after →
    after.fpcr = before.fpcr

end Crypto.ARM64.CallFrame
