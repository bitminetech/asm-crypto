import Proofs.ARM64.ImportedInterleavingModel

/-!
Construct native scheduled executions for an active borrowed SHA-256 phase.
Each environment boundary may advance unrelated globals/memory while retaining
CPU context and protected cells. Instruction locality proves the next actual
CPU/cells and successful status; loaded-code equality proves actual fetches.
The common observation list is constructed, never assumed as caller entry.

EnvironmentSafePath records enabled/admissible events at actual boundaries.
Native schedules can be rebound across policy packaging with identical advance
functions and concatenated with exact tick advancement. These helpers transfer
no borrow-admissibility claim between different policies.

Entry allocation, stack release/return policy, eventual scheduling resumption
and physical/profile correspondence require their separate adapters.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem interleaving_sameCells_trans (footprint : BitVec 64 → Prop) (left middle right : Arm64.Memory)
    (first : SameCellsOn footprint left middle) (second : SameCellsOn footprint middle right) :
    SameCellsOn footprint left right := by
  intro p hp
  exact (first p hp).trans (second p hp)

theorem interleaving_codeLoaded (base : BitVec 64) (footprint : BitVec 64 → Prop)
    (left right : Arm64.Memory) (loaded : (program base).CodeLoaded left)
    (codeProtected : ∀ i, i < (program base).code.length → footprint (base + BitVec.ofNat 64 i))
    (same : SameCellsOn footprint left right) : (program base).CodeLoaded right := by
  apply codeLoaded_of_cells loaded
  intro i hi
  exact (same (base + BitVec.ofNat 64 i) (codeProtected i hi)).symm

/-- Admissibility of each actual scheduling boundary in an active borrowed
phase. The event belongs to the actual state, not an old serial snapshot. -/
def EnvironmentSafePath {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) : Nat → List (BitVec 32) → Arm64.State → Prop
  | _, [], _ => True
  | tick, word :: rest, before => enabled before ∧
      EnvironmentAccess scope (environment.event tick before) ∧
      match Arm64.decode word with
      | none => False
      | some instruction => EnvironmentSafePath environment (tick + 1) rest
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before))

theorem schedule_serial_words_safe {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (invariant : EnabledCPUInvariant enabled)
    (base : BitVec 64)
    (codeProtected : ∀ i, i < (program base).code.length → scope.protected (base + BitVec.ofNat 64 i))
    (words : List (BitVec 32)) (tick : Nat) (serial serialOut actual : Arm64.State)
    (cpu : CPUProjection serial = CPUProjection actual)
    (same : SameCellsOn scope.protected serial.mem actual.mem)
    (loaded : (program base).CodeLoaded serial.mem)
    (permitted : PermittedWords words) (path : StaticPath base words serial)
    (executed : runWords words serial = some serialOut) (running : serialOut.status = .Running)
    (enabledPath : EnabledPath enabled words serial) (accessesProtected : ProtectedPath scope.protected words serial) :
    ∃ actualOut observations,
      ScheduledWords environment base tick words actual actualOut observations ∧
      runWordsObserved words serial = some (serialOut, observations) ∧
      CPUProjection serialOut = CPUProjection actualOut ∧
      SameCellsOn scope.protected serialOut.mem actualOut.mem ∧ actualOut.status = .Running ∧
      EnvironmentSafePath environment tick words actual := by
  induction words generalizing tick serial actual with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst serialOut
    have statuses := congrArg Arm64.State.status cpu
    simp only [projection_status] at statuses
    exact ⟨actual, [], ScheduledWords.done tick actual, rfl, cpu, same, statuses.symm.trans running, True.intro⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) = some serialOut at executed
      simp only [StaticPath, decoded] at path
      simp only [EnabledPath, decoded] at enabledPath
      simp only [ProtectedPath, decoded] at accessesProtected
      have actualEnabled := invariant serial actual cpu enabledPath.1
      let advanced := environment.advance tick actual
      have advancedCPU : CPUProjection serial = CPUProjection advanced := cpu.trans (environment.cpu tick actual).symm
      have advancedCells : SameCellsOn scope.protected serial.mem advanced.mem :=
        interleaving_sameCells_trans scope.protected serial.mem actual.mem advanced.mem same
          (environment.cells tick actual actualEnabled)
      have allowed := permitted word (by simp) instruction decoded
      have serialAfterRunning := runWords_running_before rest _ serialOut permitted.tail executed running
      have serialBeforeRunning := permitted_running_before instruction allowed serial serialAfterRunning
      obtain ⟨pairedCPU, pairedCells, actualAfterRunning, _, actualGlobals⟩ :=
        permitted_projected_instruction_locality scope.protected instruction allowed serial advanced
          advancedCPU advancedCells accessesProtected.1 serialAfterRunning
      have advancedLoaded := interleaving_codeLoaded base scope.protected serial.mem advanced.mem loaded codeProtected advancedCells
      have pc := congrArg Arm64.State.pc advancedCPU
      simp only [projection_pc] at pc
      have staticFetch : (program base).fetch advanced.pc = some instruction := by
        rw [← pc]
        exact path.1
      have fetched := loaded_fetch_of_fetch advancedLoaded staticFetch
      have beforeStatus := congrArg Arm64.State.status advancedCPU
      simp only [projection_status] at beforeStatus
      have beforeRunning : advanced.status = .Running := beforeStatus.symm.trans serialBeforeRunning
      have serialLoadedNext := permitted_codeLoaded instruction allowed serial loaded
      obtain ⟨actualOut, observations, scheduled, observed, finalCPU, finalCells, finalRunning, safeTail⟩ :=
        ih (tick + 1) _ _ pairedCPU pairedCells serialLoadedNext permitted.tail path.2 executed enabledPath.2 accessesProtected.2
      have observationEq := observation_of_cpu_projections instruction serial advanced advancedCPU pairedCPU
      have serialObserved : runWordsObserved (word :: rest) serial =
          some (serialOut, instructionObservation instruction advanced :: observations) := by
        simp only [runWordsObserved, decoded, Bind.bind, Option.bind, observed, pure, Pure.pure]
        rw [observationEq]
      have whole : ScheduledWords environment base tick (word :: rest) actual actualOut
          (instructionObservation instruction advanced :: observations) :=
        ScheduledWords.step (environment := environment) (base := base) (tick := tick)
          (word := word) (rest := rest) (before := actual) (out := actualOut)
          (observations := observations) (instruction := instruction)
          decoded allowed beforeRunning fetched actualAfterRunning actualGlobals scheduled
      have safe : EnvironmentSafePath environment tick (word :: rest) actual := by
        simp only [EnvironmentSafePath, decoded]
        exact ⟨actualEnabled, environment.accesses tick actual actualEnabled, safeTail⟩
      exact ⟨actualOut, instructionObservation instruction advanced :: observations,
        whole, serialObserved, finalCPU, finalCells, finalRunning, safe⟩

theorem schedule_serial_words {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (invariant : EnabledCPUInvariant enabled)
    (base : BitVec 64)
    (codeProtected : ∀ i, i < (program base).code.length → scope.protected (base + BitVec.ofNat 64 i))
    (words : List (BitVec 32)) (tick : Nat) (serial serialOut actual : Arm64.State)
    (cpu : CPUProjection serial = CPUProjection actual)
    (same : SameCellsOn scope.protected serial.mem actual.mem)
    (loaded : (program base).CodeLoaded serial.mem)
    (permitted : PermittedWords words) (path : StaticPath base words serial)
    (executed : runWords words serial = some serialOut) (running : serialOut.status = .Running)
    (enabledPath : EnabledPath enabled words serial) (accessesProtected : ProtectedPath scope.protected words serial) :
    ∃ actualOut observations,
      ScheduledWords environment base tick words actual actualOut observations ∧
      runWordsObserved words serial = some (serialOut, observations) ∧
      CPUProjection serialOut = CPUProjection actualOut ∧
      SameCellsOn scope.protected serialOut.mem actualOut.mem ∧ actualOut.status = .Running := by
  obtain ⟨actualOut, observations, scheduled, observed, paired, cells, status, _⟩ :=
    schedule_serial_words_safe environment invariant base codeProtected words tick serial serialOut actual
      cpu same loaded permitted path executed running enabledPath accessesProtected
  exact ⟨actualOut, observations, scheduled, observed, paired, cells, status⟩

/-- The constructive schedule uses any supplied actual serial observation
list, by determinism of the unchanged instrumented evaluator. -/
theorem schedule_serial_observed {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (invariant : EnabledCPUInvariant enabled)
    (base : BitVec 64)
    (codeProtected : ∀ i, i < (program base).code.length → scope.protected (base + BitVec.ofNat 64 i))
    (words : List (BitVec 32)) (tick : Nat) (serial serialOut actual : Arm64.State)
    (observations : List InstructionObservation)
    (cpu : CPUProjection serial = CPUProjection actual)
    (same : SameCellsOn scope.protected serial.mem actual.mem)
    (loaded : (program base).CodeLoaded serial.mem)
    (permitted : PermittedWords words) (path : StaticPath base words serial)
    (executed : runWords words serial = some serialOut) (running : serialOut.status = .Running)
    (enabledPath : EnabledPath enabled words serial) (accessesProtected : ProtectedPath scope.protected words serial)
    (observed : runWordsObserved words serial = some (serialOut, observations)) :
    ∃ actualOut, ScheduledWords environment base tick words actual actualOut observations ∧
      CPUProjection serialOut = CPUProjection actualOut ∧
      SameCellsOn scope.protected serialOut.mem actualOut.mem ∧ actualOut.status = .Running := by
  obtain ⟨actualOut, known, scheduled, knownObserved, paired, cells, status⟩ :=
    schedule_serial_words environment invariant base codeProtected words tick serial serialOut actual
      cpu same loaded permitted path executed running enabledPath accessesProtected
  have sameTrace : known = observations := (Prod.mk.inj (Option.some.inj (knownObserved.symm.trans observed))).2
  subst known
  exact ⟨actualOut, scheduled, paired, cells, status⟩

theorem schedule_serial_observed_safe {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (invariant : EnabledCPUInvariant enabled)
    (base : BitVec 64)
    (codeProtected : ∀ i, i < (program base).code.length → scope.protected (base + BitVec.ofNat 64 i))
    (words : List (BitVec 32)) (tick : Nat) (serial serialOut actual : Arm64.State)
    (observations : List InstructionObservation)
    (cpu : CPUProjection serial = CPUProjection actual)
    (same : SameCellsOn scope.protected serial.mem actual.mem)
    (loaded : (program base).CodeLoaded serial.mem)
    (permitted : PermittedWords words) (path : StaticPath base words serial)
    (executed : runWords words serial = some serialOut) (running : serialOut.status = .Running)
    (enabledPath : EnabledPath enabled words serial) (accessesProtected : ProtectedPath scope.protected words serial)
    (observed : runWordsObserved words serial = some (serialOut, observations)) :
    ∃ actualOut, ScheduledWords environment base tick words actual actualOut observations ∧
      CPUProjection serialOut = CPUProjection actualOut ∧
      SameCellsOn scope.protected serialOut.mem actualOut.mem ∧ actualOut.status = .Running ∧
      EnvironmentSafePath environment tick words actual := by
  obtain ⟨actualOut, known, scheduled, knownObserved, paired, cells, status, safe⟩ :=
    schedule_serial_words_safe environment invariant base codeProtected words tick serial serialOut actual
      cpu same loaded permitted path executed running enabledPath accessesProtected
  have sameTrace : known = observations := (Prod.mk.inj (Option.some.inj (knownObserved.symm.trans observed))).2
  subst known
  exact ⟨actualOut, scheduled, paired, cells, status, safe⟩

/-- Native schedules depend on advance, not the scope/enable/event proof
packaging. This transfers no borrow-admissibility claim between policies. -/
theorem ScheduledWords.rebind {leftScope rightScope : BorrowScope}
    {leftEnabled rightEnabled : Arm64.State → Prop}
    (left : BorrowEnvironment leftScope leftEnabled) (right : BorrowEnvironment rightScope rightEnabled)
    (sameAdvance : left.advance = right.advance)
    {base : BitVec 64} {tick : Nat} {words : List (BitVec 32)}
    {before out : Arm64.State} {observations : List InstructionObservation}
    (execution : ScheduledWords left base tick words before out observations) :
    ScheduledWords right base tick words before out observations := by
  cases left with
  | mk leftAdvance leftEvent leftCPU leftCells leftAccesses =>
    cases right with
    | mk rightAdvance rightEvent rightCPU rightCells rightAccesses =>
      change leftAdvance = rightAdvance at sameAdvance
      subst rightAdvance
      induction execution with
      | done tick s => exact ScheduledWords.done tick s
      | step decoded allowed beforeRunning fetched afterRunning globals tail ih =>
        exact ScheduledWords.step decoded allowed beforeRunning fetched afterRunning globals ih

theorem ScheduledWords.advance_congr {leftScope rightScope : BorrowScope}
    {leftEnabled rightEnabled : Arm64.State → Prop}
    (left : BorrowEnvironment leftScope leftEnabled) (right : BorrowEnvironment rightScope rightEnabled)
    (sameAdvance : ∀ tick s, left.advance tick s = right.advance tick s)
    {base : BitVec 64} {tick : Nat} {words : List (BitVec 32)}
    {before out : Arm64.State} {observations : List InstructionObservation}
    (execution : ScheduledWords left base tick words before out observations) :
    ScheduledWords right base tick words before out observations :=
  ScheduledWords.rebind left right (funext fun tick => funext fun s => sameAdvance tick s) execution

theorem ScheduledWords.append {scope : BorrowScope} {enabled : Arm64.State → Prop}
    {environment : BorrowEnvironment scope enabled} {base : BitVec 64}
    {tick : Nat} {left right : List (BitVec 32)} {before middle out : Arm64.State}
    {leftObservations rightObservations : List InstructionObservation}
    (first : ScheduledWords environment base tick left before middle leftObservations)
    (second : ScheduledWords environment base (tick + left.length) right middle out rightObservations) :
    ScheduledWords environment base tick (left ++ right) before out (leftObservations ++ rightObservations) := by
  revert second
  induction first with
  | done tick s =>
    intro second
    simpa only [List.length_nil, Nat.add_zero, List.nil_append] using second
  | @step tick word rest before middle observations instruction decoded allowed beforeRunning fetched afterRunning globals tail ih =>
    intro second
    have ticks : tick + (word :: rest).length = (tick + 1) + rest.length := by
      simp only [List.length_cons]
      omega
    have shifted : ScheduledWords environment base ((tick + 1) + rest.length) right middle out rightObservations := by
      simpa only [ticks] using second
    have joined := ih shifted
    exact ScheduledWords.step (environment := environment) (base := base) (tick := tick)
      (word := word) (rest := rest ++ right) (before := before) (out := out)
      (observations := observations ++ rightObservations) (instruction := instruction)
      decoded allowed beforeRunning fetched afterRunning globals joined

end Crypto.ARM64.Imported
