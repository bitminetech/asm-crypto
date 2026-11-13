import Proofs.ARM64.ImportedFetchExecution

/-!
Data-access observations for exactly the ordinary instruction families used
by SHA-256. The addresses and widths follow the unchanged imported load/store
definitions. Successful execution establishes their actual permission guards.
ImportedPermissionView bounds these observations by the caller footprint.
-/
namespace Crypto.ARM64.Imported

structure DataAccess where
  write : Bool
  address : BitVec 64
  bytes : Nat
  deriving DecidableEq

def dataAccesses (instruction : Arm64.Instr) (s : Arm64.State) : List DataAccess :=
  match instruction with
  | .ldr _ size _ _ addr => [⟨false, (Arm64.evalAddrMode s addr).1, size.bytes⟩]
  | .str size _ addr => [⟨true, (Arm64.evalAddrMode s addr).1, size.bytes⟩]
  | .ldp w signed _ _ addr =>
      let ea := (Arm64.evalAddrMode s addr).1
      let step : BitVec 64 := if signed then 4#64 else match w with | .W32 => 4#64 | .W64 => 8#64
      let size : Arm64.MemWidth := if signed then .W32 else match w with | .W32 => .W32 | .W64 => .X64
      [⟨false, ea, size.bytes⟩, ⟨false, ea + step, size.bytes⟩]
  | .stp w _ _ addr =>
      let ea := (Arm64.evalAddrMode s addr).1
      let step : BitVec 64 := match w with | .W32 => 4#64 | .W64 => 8#64
      let size : Arm64.MemWidth := match w with | .W32 => .W32 | .W64 => .X64
      [⟨true, ea, size.bytes⟩, ⟨true, ea + step, size.bytes⟩]
  | _ => []

def DataAccess.Allowed (m : Arm64.Memory) (access : DataAccess) : Prop :=
  if access.write then m.canWrite access.address access.bytes = true
  else m.canRead access.address access.bytes = true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem permitted_accesses_allowed (instruction : Arm64.Instr) (s : Arm64.State)
    (permitted : permittedInstruction instruction = true)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running) :
    ∀ access ∈ dataAccesses instruction s, access.Allowed s.mem := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at permitted
  all_goals simp [dataAccesses]
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr,
    Arm64.execLdp, Arm64.execStp] at running
  all_goals repeat' split at running
  all_goals try simp only [status_set_status] at running
  all_goals first | contradiction | skip
  all_goals simp_all [DataAccess.Allowed]

structure InstructionObservation where
  pc : BitVec 64
  nextPC : BitVec 64
  sp : BitVec 64
  nextSP : BitVec 64
  accesses : List DataAccess
  deriving DecidableEq

def instructionObservation (instruction : Arm64.Instr) (s : Arm64.State) : InstructionObservation :=
  let after := Arm64.execInstWithSvc Arm64.noSyscalls instruction s
  ⟨s.pc, after.pc, s.sp, after.sp, dataAccesses instruction s⟩

/-- Instrument the actual imported execution without changing its state updates.
Unsupported instruction forms are outside the permitted SHA-256 vocabulary. -/
def runWordsObserved : List (BitVec 32) → Arm64.State → Option (Arm64.State × List InstructionObservation)
  | [], s => some (s, [])
  | word :: rest, s => do
      let instruction ← Arm64.decode word
      let after := Arm64.execInstWithSvc Arm64.noSyscalls instruction s
      let (out, observations) ← runWordsObserved rest after
      pure (out, instructionObservation instruction s :: observations)

theorem runWords_observed (words : List (BitVec 32)) (s out : Arm64.State)
    (executed : runWords words s = some out) :
    ∃ observations, runWordsObserved words s = some (out, observations) := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact ⟨[], rfl⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      obtain ⟨observations, observed⟩ := ih _ executed
      refine ⟨instructionObservation instruction s :: observations, ?_⟩
      simp only [runWordsObserved, decoded, Bind.bind, Option.bind, observed, pure, Pure.pure]

theorem runWordsObserved_erases (words : List (BitVec 32)) (s : Arm64.State) :
    (runWordsObserved words s).map Prod.fst = runWords words s := by
  induction words generalizing s with
  | nil => rfl
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, runWords, decoded]
    | some instruction =>
      simp only [runWordsObserved, runWords, decoded, Bind.bind, Option.bind]
      specialize ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)
      cases observed : runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) with
      | none => simpa only [observed, Option.map_none, Option.bind_none, Bind.bind, Option.bind] using ih
      | some result =>
        rcases result with ⟨out, observations⟩
        simpa only [observed, Option.map_some, Option.bind_some, Bind.bind, Option.bind, pure, Pure.pure] using ih

/-- Each data access in each actual intermediate state satisfies the imported
permission guard. ImportedPermissionView
bounds these permissions by the declared caller-owned regions. -/
def AccessPath : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, s => match Arm64.decode word with
    | none => False
    | some instruction => (∀ access ∈ dataAccesses instruction s, access.Allowed s.mem) ∧
        AccessPath rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

theorem runWords_accessPath (words : List (BitVec 32)) (s out : Arm64.State)
    (permitted : PermittedWords words) (executed : runWords words s = some out)
    (running : out.status = .Running) : AccessPath words s := by
  induction words generalizing s with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have nextRunning := runWords_running_before rest _ out permitted.tail executed running
      have allowed := permitted_accesses_allowed instruction s (permitted word (by simp) instruction decoded) nextRunning
      simp only [AccessPath, decoded]
      exact ⟨allowed, ih _ permitted.tail executed⟩

end Crypto.ARM64.Imported
