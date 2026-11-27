import Proofs.HMACSHA256.ARM64NativeExecution
import Proofs.ARM64.ImportedInterleavingModel

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Baseline

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

structure ScopedPermissions (scope : BorrowScope) (m : Arm64.Memory) : Prop where
  read : ∀ p, (m.perm p).r = true → scope.protected p
  execute : ∀ p, (m.perm p).x = true → scope.protected p
  write : ∀ p, ((m.perm p).w && !(m.perm p).x) = true → scope.exclusive p

private theorem ScopedPermissions.transport {scope : BorrowScope} {a b : Arm64.Memory}
    (g : ScopedPermissions scope a) (same : ∀ p, b.perm p = a.perm p) : ScopedPermissions scope b :=
  ⟨fun p h => g.read p (same p ▸ h), fun p h => g.execute p (same p ▸ h),
    fun p h => g.write p (same p ▸ h)⟩

private theorem observation_permission {scope : BorrowScope} {s : Arm64.State} {p : Arm64.Program}
    {i : Arm64.Instr} (g : ScopedPermissions scope s.mem) (localForm : hmacLocal i = true)
    (fetch : p.fetchMem s.mem s.pc = some i)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running) :
    CallAccess scope (observedAccessEvent (instructionObservation i s)) := by
  have executable := fetchMem_some_canExec p s.mem s.pc i fetch
  have touch := hmac_data_allowed i s localForm running
  refine ⟨?_, ?_, fun _ h => h.elim, fun _ h => h.elim⟩
  · rintro addr (⟨k, hk, rfl⟩ | ⟨a, present, read, k, hk, rfl⟩)
    · exact g.execute _ ((allPerm_true_iff s.mem (·.x) s.pc 4).mp executable k hk)
    · have allowed := touch a present
      simp only [DataAccess.Allowed, read, Bool.false_eq_true, if_false, Arm64.Memory.canRead,
        Bool.and_eq_true] at allowed
      exact g.read _ ((allPerm_true_iff s.mem (·.r) a.address a.bytes).mp allowed.1 k hk)
  · rintro addr ⟨a, present, writes, k, hk, rfl⟩
    have allowed := touch a present
    simp only [DataAccess.Allowed, writes, if_true] at allowed
    exact g.write _ ((allPerm_true_iff s.mem (fun p => p.w && !p.x) a.address a.bytes).mp allowed k hk)

theorem NativeExecution.borrowed_accesses {base : Addr} {s out : Arm64.State}
    {obs : List InstructionObservation} (run : NativeExecution base s obs out)
    {scope : BorrowScope} (g : ScopedPermissions scope s.mem) :
    ∀ e ∈ obs, CallAccess scope (observedAccessEvent e) := by
  induction run with
  | nil => simp
  | cons _ allowed _ fetch tail ih =>
    intro e h
    rcases List.mem_cons.mp h with head | back
    · subst e
      exact observation_permission g allowed fetch tail.running
    · exact ih (g.transport (hmac_permissions_preserved _ _ allowed)) e back

private theorem fetch_same_cells {p : Arm64.Program} {s t : Arm64.State} {i : Arm64.Instr}
    (pc : t.pc = s.pc) (fetch : p.fetchMem s.mem s.pc = some i)
    (bytes : ∀ j : Fin 4, t.mem.cells (s.pc + BitVec.ofNat 64 j.val) =
      s.mem.cells (s.pc + BitVec.ofNat 64 j.val)) :
    p.fetchMem t.mem t.pc = some i := by
  have word := read32_of_cells s.pc bytes
  have executable : t.mem.canExec s.pc 4 = s.mem.canExec s.pc 4 := by
    apply Bool.eq_iff_iff.mpr
    simp only [Arm64.Memory.canExec, allPerm_true_iff]
    have equal (j : Nat) (hj : j < 4) : t.mem.perm (s.pc + BitVec.ofNat 64 j) =
        s.mem.perm (s.pc + BitVec.ofNat 64 j) := by
      unfold Arm64.Memory.perm
      rw [bytes ⟨j, hj⟩]
    exact ⟨fun h j hj => equal j hj ▸ h j hj, fun h j hj => (equal j hj).symm ▸ h j hj⟩
  simpa only [pc, Arm64.Program.fetchMem, word, executable] using fetch

private theorem hmac_extra_overlay (i : Arm64.Instr) (g s : Arm64.State)
    (added : hmacExtra i = true) :
    Arm64.execInstWithSvc Arm64.noSyscalls i (CPUOverlay s g) =
      CPUOverlay (Arm64.execInstWithSvc Arm64.noSyscalls i s) g := by
  cases i <;> simp only [hmacExtra, Bool.false_eq_true] at added
  all_goals
    simp only [Arm64.execInstWithSvc, Arm64.execDataProc3, locality_overlay_pc,
      locality_overlay_read64, locality_overlay_read32, locality_overlay_setPC, locality_overlay_write,
      locality_overlay_write64, locality_overlay_advance]

private theorem hmac_extra_memory (i : Arm64.Instr) (s : Arm64.State)
    (added : hmacExtra i = true) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem = s.mem := by
  cases i <;> simp only [hmacExtra, Bool.false_eq_true] at added
  all_goals rfl

private theorem hmac_projected_locality {scope : BorrowScope} (i : Arm64.Instr) (s t : Arm64.State)
    (allowed : hmacLocal i = true) (running : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running)
    (cpu : CPUProjection s = CPUProjection t) (cells : SameCellsOn scope.protected s.mem t.mem)
    (footprint : ProtectedAccesses scope.protected i s) :
    CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls i s) =
      CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls i t) ∧
    SameCellsOn scope.protected (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem
      (Arm64.execInstWithSvc Arm64.noSyscalls i t).mem ∧
    GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls i t) = GlobalTail t := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | added
  · obtain ⟨paired, memory, _, _, globals⟩ :=
      permitted_projected_instruction_locality scope.protected i common s t cpu cells footprint running
    exact ⟨paired, memory, globals⟩
  have sameCPU := congrArg (Arm64.execInstWithSvc Arm64.noSyscalls i) cpu
  have equation (u : Arm64.State) : CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls i u) =
      Arm64.execInstWithSvc Arm64.noSyscalls i (CPUProjection u) := by
    unfold CPUProjection
    rw [hmac_extra_overlay _ _ _ added]
    congr 1
    cases i <;> simp only [hmacExtra, Bool.false_eq_true] at added
    all_goals rfl
  have globals := congrArg GlobalTail (hmac_extra_overlay i t t added)
  refine ⟨(equation s).trans (sameCPU.trans (equation t).symm), ?_, ?_⟩
  · simpa only [hmac_extra_memory _ _ added] using cells
  · simpa only [locality_overlay_self, locality_global_overlay] using globals

/-- All modeled HMAC and SHA instructions preserve the current external
resource state, even when unrelated operations advance between instructions. -/
inductive ScheduledExecution (base : Addr) {scope : BorrowScope}
    (env : BorrowEnvironment scope (fun _ => True)) :
    Nat → Arm64.State → List InstructionObservation → Arm64.State → Prop where
  | nil (tick : Nat) (s : Arm64.State) : ScheduledExecution base env tick s [] s
  | step {tick : Nat} {s out : Arm64.State} {p : Arm64.Program} {i : Arm64.Instr}
      {rest : List InstructionObservation}
      (image : LinkedImage base p) (allowed : hmacLocal i = true)
      (running : (env.advance tick s).status = .Running)
      (fetched : p.fetchMem (env.advance tick s).mem (env.advance tick s).pc = some i)
      (global : GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls i (env.advance tick s)) =
        GlobalTail (env.advance tick s))
      (safe : ¬DataRace (observedAccessEvent (instructionObservation i (env.advance tick s))) (env.event tick s))
      (tail : ScheduledExecution base env (tick + 1)
        (Arm64.execInstWithSvc Arm64.noSyscalls i (env.advance tick s)) rest out) :
      ScheduledExecution base env tick s (instructionObservation i (env.advance tick s) :: rest) out

theorem NativeExecution.scheduled {base : Addr} {s out : Arm64.State} {obs : List InstructionObservation}
    (run : NativeExecution base s obs out) {scope : BorrowScope}
    (env : BorrowEnvironment scope (fun _ => True))
    (g : ScopedPermissions scope s.mem) (tick : Nat) (actual : Arm64.State)
    (cpu : CPUProjection s = CPUProjection actual)
    (cells : SameCellsOn scope.protected s.mem actual.mem) :
    ∃ actualOut, ScheduledExecution base env tick actual obs actualOut ∧
      CPUProjection out = CPUProjection actualOut ∧ SameCellsOn scope.protected out.mem actualOut.mem := by
  induction run generalizing tick actual with
  | nil => exact ⟨actual, .nil tick actual, cpu, cells⟩
  | @cons p i s out rest image allowed running fetched tail ih =>
    let advanced := env.advance tick actual
    have access := observation_permission g allowed fetched tail.running
    have advancedCPU : CPUProjection s = CPUProjection advanced := cpu.trans (env.cpu tick actual).symm
    have advancedCells : SameCellsOn scope.protected s.mem advanced.mem := fun p h =>
      (cells p h).trans (env.cells tick actual trivial p h)
    have pc : advanced.pc = s.pc := (congrArg Arm64.State.pc advancedCPU).symm
    have nextFetch : p.fetchMem advanced.mem advanced.pc = some i := by
      apply fetch_same_cells (s := s) (t := advanced) pc fetched
      intro j
      exact (advancedCells _ (access.1 _ (.inl ⟨j.val, j.isLt, rfl⟩))).symm
    have protect : ProtectedAccesses scope.protected i s := by
      intro a present j hj
      cases w : a.write
      · exact access.1 _ (.inr ⟨a, present, w, j, hj, rfl⟩)
      · exact .inr (access.2.1 _ ⟨a, present, w, j, hj, rfl⟩)
    obtain ⟨afterCPU, afterMem, globals⟩ :=
      hmac_projected_locality i s advanced allowed tail.running advancedCPU advancedCells protect
    have nextRunning : advanced.status = .Running := (congrArg Arm64.State.status advancedCPU).symm.trans running
    have observations := observation_of_cpu_projections i s advanced advancedCPU afterCPU
    have safe := borrow_accesses_race_free _ _ _ access (env.accesses tick actual trivial)
    rw [observations] at safe
    obtain ⟨result, later, regs, memory⟩ := ih (g.transport (hmac_permissions_preserved i s allowed))
      (tick + 1) _ afterCPU afterMem
    rw [observations]
    exact ⟨result, .step image allowed nextRunning nextFetch globals safe later, regs, memory⟩

end Crypto.HMACSHA256.ARM64
