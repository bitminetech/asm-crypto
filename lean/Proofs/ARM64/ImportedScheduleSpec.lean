import Proofs.ARM64.ImportedScheduleRAM
import equiv.SHA256.Foldl.Fused

/-!
Pure adapter proofs over the unchanged imported FIPS schedule. Expansion only
reads earlier words, so arbitrary workspace contents beyond the initialized
16-word message block do not affect the completed 64-word schedule.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.VecBridge
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Fused

abbrev ScheduleWords := Vector (BitVec 32) 64

theorem schedule_step_get_self (M : Vector (BitVec 32) 16) (W : ScheduleWords) (t : Fin 64) :
    (specScheduleStep M t.val W)[t.val]! =
      if t.val < 16 then M[t.val]! else
        SHS.SHA256.smallSigma1 W[t.val - 2]! + W[t.val - 7]! +
        SHS.SHA256.smallSigma0 W[t.val - 15]! + W[t.val - 16]! := by
  unfold specScheduleStep
  split <;>
    rw [getElem_bang_eq_getElem _ _ t.isLt, set_bang_eq_set _ _ t.isLt, Vector.getElem_set_self]

theorem schedule_step_prefix (M : Vector (BitVec 32) 16) (W W' : ScheduleWords)
    (t : Fin 64) (ht : 16 ≤ t.val)
    (h : ∀ j, j < t.val → W[j]! = W'[j]!) :
    ∀ j, j < t.val + 1 → (specScheduleStep M t.val W)[j]! = (specScheduleStep M t.val W')[j]! := by
  intro j hj
  by_cases he : j = t.val
  · subst j
    rw [schedule_step_get_self, schedule_step_get_self, if_neg (by omega), if_neg (by omega)]
    rw [h (t.val - 2) (by omega), h (t.val - 7) (by omega),
      h (t.val - 15) (by omega), h (t.val - 16) (by omega)]
  · rw [getElem!_specScheduleStep_ne M t.val W j he,
        getElem!_specScheduleStep_ne M t.val W' j he]
    exact h j (by omega)

def expandedWords (M : Vector (BitVec 32) 16) (initial : ScheduleWords) (n : Nat) : ScheduleWords :=
  Fin.foldl n (fun W (i : Fin n) => specScheduleStep M (16 + i.val) W) initial

theorem expanded_prefix (M : Vector (BitVec 32) 16) (W W' : ScheduleWords)
    (h : ∀ j, j < 16 → W[j]! = W'[j]!) (n : Nat) (hn : n ≤ 48) :
    ∀ j, j < 16 + n → (expandedWords M W n)[j]! = (expandedWords M W' n)[j]! := by
  induction n with
  | zero => simpa only [expandedWords, Fin.foldl_zero, Nat.add_zero] using h
  | succ n ih =>
    have prev := ih (by omega)
    have step := schedule_step_prefix M (expandedWords M W n) (expandedWords M W' n)
      ⟨16 + n, by omega⟩ (by change 16 ≤ 16 + n; omega) prev
    simpa only [expandedWords, Fin.foldl_succ_last, Fin.val_last, Fin.val_castSucc,
      Nat.add_assoc] using step

def initialSchedule (M : Vector (BitVec 32) 16) (n : Nat) : ScheduleWords :=
  Fin.foldl n (fun W (i : Fin n) => specScheduleStep M i.val W) (Vector.replicate 64 default)

theorem initial_schedule_prefix (M : Vector (BitVec 32) 16) (n : Nat) (hn : n ≤ 16) :
    ∀ j, j < n → (initialSchedule M n)[j]! = M[j]! := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have prev := ih (by omega)
    unfold initialSchedule
    rw [Fin.foldl_succ_last]
    change (specScheduleStep M n (initialSchedule M n))[j]! = M[j]!
    by_cases he : j = n
    · subst j
      have self := schedule_step_get_self M (initialSchedule M n) ⟨n, by omega⟩
      simpa only [show n < 16 by omega, if_true] using self
    · rw [getElem!_specScheduleStep_ne M n (initialSchedule M n) j he]
      exact prev j (by omega)

theorem expanded_eq_schedule (M : Vector (BitVec 32) 16) (W : ScheduleWords)
    (h : ∀ j, j < 16 → W[j]! = M[j]!) :
    expandedWords M W 48 = SHS.SHA256.schedule M := by
  have split : SHS.SHA256.schedule M = expandedWords M (initialSchedule M 16) 48 := by
    exact (schedule_eq_foldl M).trans
      (Fin.foldl_add (n := 16) (m := 48)
        (fun W (i : Fin (16 + 48)) => specScheduleStep M i.val W) (Vector.replicate 64 default))
  rw [split]
  apply Vector.ext
  intro j hj
  rw [← getElem_bang_eq_getElem _ _ hj, ← getElem_bang_eq_getElem _ _ hj]
  exact expanded_prefix M W (initialSchedule M 16)
    (fun j hj => (h j hj).trans (initial_schedule_prefix M 16 (by decide) j hj).symm)
    48 (by decide) j (by omega)

end Crypto.ARM64.Imported
