import Proofs.Baseline

/-!
Shared borrow/interference predicates for a pure leaf call. Addresses must be
interpreted through the target's alias-aware memory profile. Shared regions
include complete immutable input/code borrows; exclusive regions include the
complete writable output and active stack, not merely bytes actually accessed.

Unlike byte preservation alone, an admissible environment also excludes reads
racing the call's writes, and release/protection changes during the borrow.
Connecting these events to native executions and real ownership/lifetime is a
separate obligation. These definitions are a candidate dependency of a future
independently reviewed baseline, not an equal certificate.
-/
namespace Crypto.Baseline

structure BorrowScope where
  shared : Address → Prop
  exclusive : Address → Prop

def BorrowScope.protected (scope : BorrowScope) (p : Address) : Prop :=
  scope.shared p ∨ scope.exclusive p

structure AccessEvent where
  reads : Address → Prop
  writes : Address → Prop
  releases : Address → Prop
  changesProtection : Address → Prop

def CallAccess (scope : BorrowScope) (event : AccessEvent) : Prop :=
  (∀ p, event.reads p → scope.protected p) ∧
  (∀ p, event.writes p → scope.exclusive p) ∧
  (∀ p, ¬event.releases p) ∧ (∀ p, ¬event.changesProtection p)

def EnvironmentAccess (scope : BorrowScope) (event : AccessEvent) : Prop :=
  (∀ p, scope.exclusive p → ¬event.reads p) ∧
  (∀ p, scope.protected p → ¬event.writes p) ∧
  (∀ p, scope.protected p → ¬event.releases p) ∧
  (∀ p, scope.protected p → ¬event.changesProtection p)

def DataRace (left right : AccessEvent) : Prop :=
  ∃ p, (left.writes p ∧ (right.reads p ∨ right.writes p)) ∨
    (right.writes p ∧ (left.reads p ∨ left.writes p))

theorem borrow_accesses_race_free (scope : BorrowScope) (call environment : AccessEvent)
    (localAccess : CallAccess scope call) (externalAccess : EnvironmentAccess scope environment) :
    ¬DataRace call environment := by
  rintro ⟨p, (⟨write, read | writeOther⟩ | ⟨writeOther, read | write⟩)⟩
  · exact externalAccess.1 p (localAccess.2.1 p write) read
  · exact externalAccess.2.1 p (Or.inr (localAccess.2.1 p write)) writeOther
  · exact externalAccess.2.1 p (localAccess.1 p read) writeOther
  · exact externalAccess.2.1 p (Or.inr (localAccess.2.1 p write)) writeOther

/-- The cell includes permissions/liveness or other capability information when
the chosen memory profile carries it. Environment steps preserve current owned
cells, so this does not restore stale snapshots after unrelated progress. -/
def KeepsBorrowed {Cell : Type} (scope : BorrowScope) (before after : Address → Cell) : Prop :=
  ∀ p, scope.protected p → after p = before p

theorem KeepsBorrowed.refl {Cell : Type} (scope : BorrowScope) (memory : Address → Cell) :
    KeepsBorrowed scope memory memory := by intro p _; rfl

theorem KeepsBorrowed.trans {Cell : Type} {scope : BorrowScope} {a b c : Address → Cell}
    (first : KeepsBorrowed scope a b) (second : KeepsBorrowed scope b c) : KeepsBorrowed scope a c := by
  intro p hp
  exact (second p hp).trans (first p hp)

noncomputable def updateUnborrowed {Cell : Type} (scope : BorrowScope)
    (before replacement : Address → Cell) (p : Address) : Cell := by
  classical
  exact if scope.protected p then before p else replacement p

theorem updateUnborrowed_keeps {Cell : Type} (scope : BorrowScope) (before replacement : Address → Cell) :
    KeepsBorrowed scope before (updateUnborrowed scope before replacement) := by
  intro p hp
  simp [updateUnborrowed, hp]

end Crypto.Baseline
