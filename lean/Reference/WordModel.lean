import EthLib.Cryptography.Proofs.Hash.Sha256
import Mathlib.Tactic.IntervalCases

/-! Word and vector views used by the assembly proofs. -/
namespace Crypto.Reference.WordModel

open EthLib.Cryptography.Hash.Sha256

abbrev Word := BitVec 32
abbrev Hash := Vector Word 8
abbrev Block := Vector Word 16
abbrev Schedule := Vector Word 64

def toState (s : Hash) : Spec.State := ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩

@[simp] theorem toState_words (s : Spec.State) : toState s.words = s := by cases s; rfl

@[simp] theorem words_toState (s : Hash) : (toState s).words = s := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

abbrev K : Vector Word 64 := EthLib.Cryptography.Hash.Sha256.K.map UInt32.toBitVec
abbrev H0_256 : Hash := Spec.initial.words

abbrev smallSigma0 := Spec.small0
abbrev smallSigma1 := Spec.small1
abbrev bigSigma0 := Spec.large0
abbrev bigSigma1 := Spec.large1

def Ch (x y z : Word) : Word := (x &&& y) ^^^ ((~~~x) &&& z)
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def specScheduleStep (input : Block) (t : Nat) (words : Schedule) : Schedule :=
  words.set! t (if t < 16 then input[t]! else
    smallSigma1 words[t - 2]! + words[t - 7]! + smallSigma0 words[t - 15]! + words[t - 16]!)

private theorem setBang {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (x : α) :
    v.set! i x = v.setIfInBounds i x := by cases v; rfl

theorem getElem!_specScheduleStep_ne (input : Block) (t : Nat) (words : Schedule)
    (j : Nat) (different : j ≠ t) : (specScheduleStep input t words)[j]! = words[j]! := by
  by_cases inside : j < 64
  · rw [getElem!_pos _ j inside, getElem!_pos _ j inside]
    simp [specScheduleStep, setBang, Ne.symm different]
  · rw [getElem!_neg _ j inside, getElem!_neg _ j inside]

private def schedulePrefix (input : Block) (steps : Nat) : Schedule :=
  Fin.foldl steps (fun words t => specScheduleStep input t.val words) (Vector.replicate 64 0)

private theorem schedule_prefix (input : Block) (steps : Nat) (bound : steps ≤ 64)
    (t : Nat) (done : t < steps) : (schedulePrefix input steps)[t]! = Spec.messageWord input t := by
  induction steps generalizing t with
  | zero => omega
  | succ n ih =>
    have next : schedulePrefix input (n+1) = specScheduleStep input n (schedulePrefix input n) := by
      simp only [schedulePrefix, Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    rw [next]
    by_cases finalWord : t = n
    · subst t
      have inside : n < 64 := by omega
      rw [specScheduleStep]
      have setSlot (w : Word) : ((schedulePrefix input n).set! n w)[n]! = w := by
        rw [setBang, getElem!_pos _ n inside]
        exact Vector.getElem_setIfInBounds_self inside
      rw [setSlot]
      by_cases early : n < 16
      · rw [if_pos early, getElem!_pos _ n early]
        conv_rhs => rw [Spec.messageWord]
        simp only [dif_pos early]
      · rw [if_neg early]
        have earlier (i : Nat) (hi : i < n) := ih (by omega) i hi
        rw [earlier (n-2) (by omega), earlier (n-7) (by omega),
          earlier (n-15) (by omega), earlier (n-16) (by omega)]
        conv_rhs => rw [Spec.messageWord]
        simp only [dif_neg early]
        ac_rfl
    · rw [getElem!_specScheduleStep_ne _ _ _ _ finalWord]
      exact ih (by omega) t (by omega)

def schedule (input : Block) : Schedule := Vector.ofFn fun i => Spec.messageWord input i.val

theorem schedule_eq_foldl (input : Block) : schedule input =
    Fin.foldl 64 (fun words t => specScheduleStep input t.val words) (Vector.replicate 64 0) := by
  apply Vector.ext
  intro i hi
  have agree := schedule_prefix input 64 (by decide) i hi
  rw [getElem!_pos (schedulePrefix input 64) i hi] at agree
  simp only [schedule, Vector.getElem_ofFn]
  exact agree.symm

theorem schedule_word (input : Block) (i : Fin 64) : (schedule input)[i.val]! =
    Spec.messageWord input i.val := by
  rw [getElem!_pos (schedule input) i.val i.isLt]
  simp only [schedule, Vector.getElem_ofFn]

def specRoundStep (words : Schedule) (t : Nat) (s : Hash) : Hash :=
  (Spec.step (toState s) K[t]! words[t]!).words

def addH (initial s : Hash) : Hash := Vector.ofFn fun i => s[i] + initial[i]

def compress (initial : Hash) (input : Block) : Hash := (Spec.compression input (toState initial)).words

private def roundsPrefix (input : Block) (initial : Hash) (steps : Nat) : Hash :=
  Fin.foldl steps (fun s t => specRoundStep (schedule input) t.val s) initial

private theorem rounds_agree (input : Block) (initial : Hash) (steps : Nat) (bound : steps ≤ 64) :
    toState (roundsPrefix input initial steps) = Spec.rounds input (toState initial) steps := by
  induction steps with
  | zero => simp only [roundsPrefix, Fin.foldl_zero, Spec.rounds]
  | succ n ih =>
    have next : roundsPrefix input initial (n+1) =
        specRoundStep (schedule input) n (roundsPrefix input initial n) := by
      simp only [roundsPrefix, Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    rw [next, specRoundStep, toState_words, ih (by omega), schedule_word input ⟨n, by omega⟩,
      Spec.rounds]
    have inside : n < 64 := by omega
    rw [getElem!_pos K n inside, getElem!_pos EthLib.Cryptography.Hash.Sha256.K n inside]
    simp only [K, Vector.getElem_map]

private theorem addH_agrees (initial s : Spec.State) : addH initial.words s.words =
    (⟨s.a + initial.a, s.b + initial.b, s.c + initial.c, s.d + initial.d,
      s.e + initial.e, s.f + initial.f, s.g + initial.g, s.h + initial.h⟩ : Spec.State).words := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem compress_eq_rounds (initial : Hash) (input : Block) :
    addH initial (Fin.foldl 64 (fun s t => specRoundStep (schedule input) t.val s) initial) =
      compress initial input := by
  change addH initial (roundsPrefix input initial 64) = compress initial input
  have round := congrArg Spec.State.words (rounds_agree input initial 64 (by decide))
  rw [words_toState] at round
  rw [round, ← words_toState initial, addH_agrees]
  simp only [compress, toState_words, Spec.compression]

theorem getElem_bang_eq_getElem {α : Type} [Inhabited α] {n : Nat}
    (v : Vector α n) (i : Nat) (h : i < n) : v[i]! = v[i]'h := getElem!_pos v i h

theorem set_bang_eq_set {α : Type} {n : Nat} (v : Vector α n) (i : Nat)
    (h : i < n) (value : α) : v.set! i value = v.set i value h := by
  rw [setBang]
  apply Vector.ext
  intro j hj
  simp [Vector.getElem_setIfInBounds, Vector.getElem_set]

theorem fin_foldl_ext {α : Type} (count : Nat) (f g : α → Fin count → α)
    (initial : α) (eq : ∀ acc i, f acc i = g acc i) :
    Fin.foldl count f initial = Fin.foldl count g initial := by
  have same : f = g := funext fun acc => funext (eq acc)
  rw [same]

end Crypto.Reference.WordModel
