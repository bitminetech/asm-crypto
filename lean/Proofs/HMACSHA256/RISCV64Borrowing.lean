import Proofs.HMACSHA256.RISCV64Program
import Proofs.RISCV64.Borrowing

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.Baseline (BorrowScope CallAccess EnvironmentAccess AccessEvent DataRace borrow_accesses_race_free)
open Crypto.ARM64.Imported (allPerm_true_iff)

/-- The modeled memory permissions are contained in the independently
borrowed footprint. A successful instruction cannot use a grant outside it.
The caller's physical binding supplies the alias-aware interpretation. -/
structure ScopedPermissions (scope : BorrowScope) (m : Memory) : Prop where
  read : ∀ p, (m.perm p).r = true → scope.protected p
  exec : ∀ p, (m.perm p).x = true → scope.protected p
  write : ∀ p, ((m.perm p).w && !(m.perm p).x) = true → scope.exclusive p

theorem ScopedPermissions.preserved {scope : BorrowScope} {before after : Memory}
    (entry : ScopedPermissions scope before) (same : ∀ p, after.perm p = before.perm p) :
    ScopedPermissions scope after where
  read := fun p h => entry.read p (by rw [← same p]; exact h)
  exec := fun p h => entry.exec p (by rw [← same p]; exact h)
  write := fun p h => entry.write p (by rw [← same p]; exact h)

theorem permitted_access_borrow {scope : BorrowScope} {m : Memory}
    (entry : ScopedPermissions scope m) (a : Access) (ok : a.permitted m = true) :
    CallAccess scope (memoryEvent a) := by
  refine ⟨?_, ?_, fun _ h => h, fun _ h => h⟩
  · intro p h
    cases a with
    | fetch start bytes =>
      obtain ⟨i, within, address⟩ := h
      subst p
      simp only [Access.permitted, Bool.and_eq_true] at ok
      have fetch : m.canExec start bytes = true := ok.2
      exact entry.exec _ ((allPerm_true_iff m (·.x) start bytes).mp fetch i within)
    | read start width =>
      obtain ⟨i, within, address⟩ := h
      subst p
      simp only [Access.permitted, Bool.and_eq_true] at ok
      have read : m.canRead start width.bytes = true := ok.2
      have every : m.allPerm (·.r) start width.bytes = true := by
        simp only [Arm64.Memory.canRead, Bool.and_eq_true] at read
        exact read.1
      exact entry.read _ ((allPerm_true_iff m (·.r) start width.bytes).mp every i within)
    | write => exact h.elim
  · intro p h
    cases a with
    | write start width =>
      obtain ⟨i, within, address⟩ := h
      subst p
      simp only [Access.permitted, Bool.and_eq_true] at ok
      have write : m.canWrite start width.bytes = true := ok.2
      exact entry.write _ ((allPerm_true_iff m (fun p => p.w && !p.x) start width.bytes).mp write i within)
    | fetch => exact h.elim
    | read => exact h.elim

theorem ProgramExecution.borrowed_accesses {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (scope : BorrowScope)
    (permissions : ScopedPermissions scope s.mem) :
    ∀ step ∈ events, ∀ a ∈ step, CallAccess scope (memoryEvent a) := by
  induction run with
  | nil => simp
  | cons head _ ih =>
    intro listed membership a present
    rcases List.mem_cons.mp membership with same | later
    · subst listed
      exact permitted_access_borrow permissions a (List.all_eq_true.mp head.allowed a present)
    · exact ih (permissions.preserved head.perm) listed later a present

/-- The access trace of a checked linked execution obeys the borrowed scope,
and none of those accesses races a permitted environment event. -/
theorem ProgramExecution.no_data_race {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (scope : BorrowScope)
    (permissions : ScopedPermissions scope s.mem) (environment : AccessEvent)
    (allowed : EnvironmentAccess scope environment) :
    ∀ step ∈ events, ∀ a ∈ step, ¬DataRace (memoryEvent a) environment := by
  intro step happens a observed
  exact borrow_accesses_race_free _ _ _ (run.borrowed_accesses scope permissions step happens a observed) allowed

end Crypto.HMACSHA256.RISCV64
