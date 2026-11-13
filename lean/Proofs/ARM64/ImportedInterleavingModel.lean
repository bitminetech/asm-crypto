import Proofs.ARM64.ImportedInstructionLocality
import Proofs.ARM64.ImportedBorrowAccess
import Proofs.ARM64.ImportedTraceRelation

/-!
Interleaving model for the scalar SHA-256 invocation. Each scheduling boundary
represents a finite amount of permitted external progress before the next
library instruction; actual scheduling coverage requires eventual resumption.
The environment retains the thread CPU context, but may advance unrelated
filesystem/resource state and unborrowed memory. An enable predicate controls
when a byte borrow is active, independently of reservation/accessibility.

ScheduledWords records actual memory fetch and the unchanged imported execute
operation at every library step. Local instructions must preserve the current
global tail, so no earlier environment snapshot is restored. This model alone
is not an existence, ownership, race-freedom or complete equal proof.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

@[simp] theorem projection_pc (s : Arm64.State) : (CPUProjection s).pc = s.pc := rfl
@[simp] theorem projection_sp (s : Arm64.State) : (CPUProjection s).sp = s.sp := rfl
@[simp] theorem projection_status (s : Arm64.State) : (CPUProjection s).status = s.status := rfl
@[simp] theorem projection_read64 (s : Arm64.State) (r : Arm64.Reg) :
    (CPUProjection s).readReg64 r = s.readReg64 r := by cases r <;> rfl

structure BorrowEnvironment (scope : BorrowScope) (enabled : Arm64.State → Prop) where
  advance : Nat → Arm64.State → Arm64.State
  event : Nat → Arm64.State → AccessEvent
  cpu : ∀ tick s, CPUProjection (advance tick s) = CPUProjection s
  cells : ∀ tick s, enabled s → SameCellsOn scope.protected s.mem (advance tick s).mem
  accesses : ∀ tick s, enabled s → EnvironmentAccess scope (event tick s)

def EnabledCPUInvariant (enabled : Arm64.State → Prop) : Prop :=
  ∀ left right, CPUProjection left = CPUProjection right → enabled left → enabled right

def EnabledPath (enabled : Arm64.State → Prop) : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, s => enabled s ∧ match Arm64.decode word with
    | none => False
    | some instruction => EnabledPath enabled rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

def ProtectedPath (footprint : BitVec 64 → Prop) : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, s => match Arm64.decode word with
    | none => False
    | some instruction => ProtectedAccesses footprint instruction s ∧
        ProtectedPath footprint rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

inductive ScheduledWords {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (base : BitVec 64) :
    Nat → List (BitVec 32) → Arm64.State → Arm64.State → List InstructionObservation → Prop
  | done (tick : Nat) (s : Arm64.State) : ScheduledWords environment base tick [] s s []
  | step {tick : Nat} {word : BitVec 32} {rest : List (BitVec 32)}
      {before out : Arm64.State} {observations : List InstructionObservation} {instruction : Arm64.Instr}
      (decoded : Arm64.decode word = some instruction)
      (allowed : permittedInstruction instruction = true)
      (beforeRunning : (environment.advance tick before).status = .Running)
      (fetched : (program base).fetchMem (environment.advance tick before).mem
        (environment.advance tick before).pc = some instruction)
      (afterRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before)).status = .Running)
      (globals : GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before)) =
        GlobalTail (environment.advance tick before))
      (tail : ScheduledWords environment base (tick + 1) rest
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before)) out observations) :
      ScheduledWords environment base tick (word :: rest) before out
        (instructionObservation instruction (environment.advance tick before) :: observations)

theorem ScheduledWords.length {scope : BorrowScope} {enabled : Arm64.State → Prop}
    {environment : BorrowEnvironment scope enabled} {base : BitVec 64} {tick : Nat}
    {words : List (BitVec 32)} {before after : Arm64.State} {observations : List InstructionObservation}
    (execution : ScheduledWords environment base tick words before after observations) :
    observations.length = words.length := by
  induction execution with
  | done => rfl
  | step _ _ _ _ _ _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem scheduled_native_step (base : BitVec 64) (instruction : Arm64.Instr) (s : Arm64.State)
    (allowed : permittedInstruction instruction = true) (running : s.status = .Running)
    (fetched : (program base).fetchMem s.mem s.pc = some instruction) :
    Arm64.Step (program base) s (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
  rw [← evalInst_permitted base instruction allowed]
  exact Arm64.Step.exec running fetched

theorem observation_of_cpu_projections (instruction : Arm64.Instr) (left right : Arm64.State)
    (before : CPUProjection left = CPUProjection right)
    (after : CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction left) =
      CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction right)) :
    instructionObservation instruction left = instructionObservation instruction right := by
  have pc := congrArg Arm64.State.pc before
  have sp := congrArg Arm64.State.sp before
  have nextPC := congrArg Arm64.State.pc after
  have nextSP := congrArg Arm64.State.sp after
  simp only [projection_pc, projection_sp] at pc sp nextPC nextSP
  have registers : RegistersAgree (accessRegisters instruction) left right := by
    intro r _
    have same := congrArg (fun s : Arm64.State => s.readReg64 r) before
    simpa only [projection_read64] using same
  have accesses := dataAccesses_eq_of_registers instruction left right registers
  unfold instructionObservation
  dsimp only
  rw [pc, sp, nextPC, nextSP, accesses]

end Crypto.ARM64.Imported
