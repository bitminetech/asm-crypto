import Proofs.ARM64.ImportedPermissionView

/-!
Every actual observed instruction fetch in the conservative SHA-256 logical
view reads four executable bytes inside the recorded image. CodeLoaded and
normalized permissions propagate through each permitted scalar instruction;
StaticPath binds the observed word execution to actual memory fetches.
The terminal state is not fetched again, so RET may target outside the image
or an address within it. Semantic executable grants come from the explicit
caller Authority; physical/profile correspondence remains a separate boundary.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem fetchMem_some_canExec (prog : Arm64.Program) (m : Arm64.Memory)
    (pc : BitVec 64) (instruction : Arm64.Instr)
    (fetched : prog.fetchMem m pc = some instruction) : m.canExec pc 4 = true := by
  unfold Arm64.Program.fetchMem at fetched
  split at fetched
  · contradiction
  · split at fetched
    · contradiction
    · split at fetched
      · contradiction
      · simpa using ‹¬(!m.canExec pc 4) = true›

/-- Actual fetches in every running intermediate state; the terminal state is
not fetched again, even when RET targets an address in this same image. -/
def FetchViewPath (base : BitVec 64) : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, current => match Arm64.decode word with
    | none => False
    | some instruction => current.status = .Running ∧
        (program base).fetchMem current.mem current.pc = some instruction ∧
        (∀ i, i < 4 → (callerImage base).Contains (current.pc + BitVec.ofNat 64 i)) ∧
        FetchViewPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current)

theorem runWords_fetch_viewPath (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (current out : Arm64.State)
    (permissions : ∀ p, current.mem.perm p = logicalPermission base entryState message p)
    (loaded : (program base).CodeLoaded current.mem)
    (permitted : PermittedWords words) (path : StaticPath base words current)
    (executed : runWords words current = some out) (running : out.status = .Running) :
    FetchViewPath base words current := by
  induction words generalizing current with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current) = some out at executed
      simp only [StaticPath, decoded] at path
      have allowed := permitted word (by simp) instruction decoded
      have afterRunning := runWords_running_before rest _ out permitted.tail executed running
      have currentRunning := permitted_running_before instruction allowed current afterRunning
      have fetched := loaded_fetch_of_fetch loaded path.1
      have execute := fetchMem_some_canExec (program base) current.mem current.pc instruction fetched
      have within := view_exec_within base entryState message current.mem permissions current.pc 4 execute
      have nextPermissions (p : BitVec 64) :
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction current).mem.perm p =
            logicalPermission base entryState message p :=
        (permitted_preserves_permissions instruction allowed current p).trans (permissions p)
      have nextLoaded := permitted_codeLoaded instruction allowed current loaded
      simp only [FetchViewPath, decoded]
      exact ⟨currentRunning, fetched, within, ih _ nextPermissions nextLoaded permitted.tail path.2 executed⟩

theorem fetch_path_observed (base : BitVec 64) (words : List (BitVec 32))
    (current out : Arm64.State) (observations : List InstructionObservation)
    (path : FetchViewPath base words current)
    (observed : runWordsObserved words current = some (out, observations)) :
    ∀ observation ∈ observations, ∀ i, i < 4 →
      (callerImage base).Contains (observation.pc + BitVec.ofNat 64 i) := by
  induction words generalizing current out observations with
  | nil =>
    simp only [runWordsObserved, Option.some.injEq, Prod.mk.injEq] at observed
    rw [← observed.2]
    simp
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at observed
    | some instruction =>
      simp only [FetchViewPath, decoded] at path
      cases tailObserved : runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current) with
      | none => simp [runWordsObserved, decoded, tailObserved] at observed
      | some result =>
        rcases result with ⟨tailOut, tailObservations⟩
        simp only [runWordsObserved, decoded, Bind.bind, Option.bind, tailObserved,
          pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at observed
        intro observation member i hi
        rw [← observed.2] at member
        rcases List.mem_cons.mp member with same | later
        · subst observation
          exact path.2.2.1 i hi
        · exact ih _ tailOut tailObservations path.2.2.2 tailObserved observation later i hi

theorem fetch_observed_raw_execution (words : List (BitVec 32)) (current out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved words current = some (out, observations)) :
    runWords words current = some out := by
  have projected := congrArg (Option.map Prod.fst) observed
  have erased : (runWordsObserved words current).map Prod.fst = some out := by
    simpa only [Option.map_some] using projected
  exact (runWordsObserved_erases words current).symm.trans erased

theorem observed_fetch_within_view (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32))
    (current out : Arm64.State) (observations : List InstructionObservation)
    (permissions : ∀ p, current.mem.perm p = logicalPermission base entryState message p)
    (loaded : (program base).CodeLoaded current.mem)
    (permitted : PermittedWords words) (path : StaticPath base words current)
    (observed : runWordsObserved words current = some (out, observations)) (running : out.status = .Running) :
    ∀ observation ∈ observations, ∀ i, i < 4 →
      (callerImage base).Contains (observation.pc + BitVec.ofNat 64 i) := by
  have executed := fetch_observed_raw_execution words current out observations observed
  have fetched := runWords_fetch_viewPath base entryState message words current out permissions loaded permitted path executed running
  exact fetch_path_observed base words current out observations fetched observed

theorem logical_observed_fetch_bounds (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base entryState message extent authority)
    (words : List (BitVec 32)) (out : Arm64.State) (observations : List InstructionObservation)
    (permitted : PermittedWords words)
    (path : StaticPath base words (logicalState base entryState message))
    (observed : runWordsObserved words (logicalState base entryState message) = some (out, observations))
    (running : out.status = .Running) :
    (∀ observation ∈ observations, ∀ i, i < 4 →
      (callerImage base).Contains (observation.pc + BitVec.ofNat 64 i)) ∧
    (∀ observation ∈ observations, ∀ i, i < 4 →
      authority.executable (observation.pc + BitVec.ofNat 64 i)) := by
  have within := observed_fetch_within_view base entryState message words _ out observations
    (logicalMemory_perm base entryState message) (view_code_loaded base entryState message extent authority entry)
    permitted path observed running
  refine ⟨within, ?_⟩
  intro observation member i hi
  exact entry.imageExec _ (within observation member i hi)

end Crypto.ARM64.Imported
