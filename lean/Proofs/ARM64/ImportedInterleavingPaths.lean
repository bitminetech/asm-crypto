import Proofs.ARM64.ImportedInterleavingModel
import Proofs.ARM64.ImportedDynamicEnvironment
import Proofs.ARM64.ImportedLabeledExecution

/-! Native path/borrow composition helpers for the dynamic invocation proof. -/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

theorem StaticPath.prefix {base : BitVec 64} (xs ys : List (BitVec 32)) (s : Arm64.State)
    (whole : StaticPath base (xs ++ ys) s) : StaticPath base xs s := by
  induction xs generalizing s with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [List.cons_append, StaticPath, decoded] at whole
    | some instruction =>
      have fields : (program base).fetch s.pc = some instruction ∧
          StaticPath base (rest ++ ys) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [List.cons_append, StaticPath, decoded] using whole
      simp only [StaticPath, decoded]
      exact ⟨fields.1, ih _ fields.2⟩

theorem StaticPath.suffix {base : BitVec 64} (xs ys : List (BitVec 32)) (s mid : Arm64.State)
    (executed : runWords xs s = some mid) (whole : StaticPath base (xs ++ ys) s) :
    StaticPath base ys mid := by
  induction xs generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst mid
    exact whole
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some mid at executed
      have fields : (program base).fetch s.pc = some instruction ∧
          StaticPath base (rest ++ ys) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [List.cons_append, StaticPath, decoded] using whole
      exact ih _ executed fields.2

theorem ProtectedPath.prefix (footprint : BitVec 64 → Prop) (xs ys : List (BitVec 32)) (s : Arm64.State)
    (whole : ProtectedPath footprint (xs ++ ys) s) : ProtectedPath footprint xs s := by
  induction xs generalizing s with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [List.cons_append, ProtectedPath, decoded] at whole
    | some instruction =>
      simp only [List.cons_append, ProtectedPath, decoded] at whole
      simp only [ProtectedPath, decoded]
      exact ⟨whole.1, ih _ whole.2⟩

theorem ProtectedPath.suffix (footprint : BitVec 64 → Prop) (xs ys : List (BitVec 32)) (s mid : Arm64.State)
    (executed : runWords xs s = some mid) (whole : ProtectedPath footprint (xs ++ ys) s) :
    ProtectedPath footprint ys mid := by
  induction xs generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst mid
    exact whole
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some mid at executed
      simp only [List.cons_append, ProtectedPath, decoded] at whole
      exact ih _ executed whole.2

theorem protectedPath_of_observations (footprint : BitVec 64 → Prop) (words : List (BitVec 32))
    (s out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved words s = some (out, observations))
    (confined : ∀ observation ∈ observations, ∀ access ∈ observation.accesses,
      ∀ i, i < access.bytes → footprint (access.address + BitVec.ofNat 64 i)) :
    ProtectedPath footprint words s := by
  induction words generalizing s observations with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at observed
    | some instruction =>
      obtain ⟨tail, tailObserved, same⟩ := labeled_observed_cons word rest s out observations instruction decoded observed
      simp only [ProtectedPath, decoded]
      refine ⟨?_, ih _ tail tailObserved ?_⟩
      · intro access present i bound
        exact confined (instructionObservation instruction s) (by rw [same]; simp) access present i bound
      · intro observation present access accessMember i bound
        exact confined observation (by rw [same]; simp [present]) access accessMember i bound

theorem safe_observations_protected (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (out : Arm64.State)
    (observations : List InstructionObservation) (result : LogicalCallResult base s message authority out observations) :
    ∀ observation ∈ observations, ∀ access ∈ observation.accesses,
      ∀ i, i < access.bytes → (shaBorrowScope base s extent).protected (access.address + BitVec.ofNat 64 i) := by
  intro observation present access member i bound
  have within := result.confined observation present access member i bound
  cases writing : access.write
  · have read : permissionReadFootprint base s message (access.address + BitVec.ofNat 64 i) := by
      simpa only [writing, Bool.false_eq_true, ↓reduceIte] using within
    exact view_read_borrowed base s message extent authority entry _ read
  · have write : permissionWriteFootprint s (access.address + BitVec.ofNat 64 i) := by
      simpa only [writing, ↓reduceIte] using within
    exact Or.inr write

theorem enabled_preserving_then_last (entry s out : Arm64.State) (middle : List (BitVec 32)) (last : BitVec 32)
    (preserved : StackPreservingWords middle) (active : stackActive entry s)
    (executed : runWords (middle ++ [last]) s = some out) :
    EnabledPath (stackActive entry) (middle ++ [last]) s := by
  induction middle generalizing s with
  | nil =>
    cases decoded : Arm64.decode last with
    | none => simp [runWords, decoded] at executed
    | some instruction => simp only [List.nil_append, EnabledPath, decoded]; exact ⟨active, True.intro⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [List.cons_append, runWords, decoded] at executed
      change runWords (rest ++ [last]) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have stack := stack_preserving_sp instruction s (preserved word (by simp) instruction decoded)
      have nextActive : stackActive entry (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := stack.trans active
      simp only [List.cons_append, EnabledPath, decoded]
      exact ⟨active, ih _ preserved.tail nextActive executed⟩

theorem enabled_true_path (words : List (BitVec 32)) (s out : Arm64.State)
    (executed : runWords words s = some out) : EnabledPath (fun _ => True) words s := by
  induction words generalizing s with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      simp only [EnabledPath, decoded]
      exact ⟨True.intro, ih _ executed⟩

end Crypto.ARM64.Imported
