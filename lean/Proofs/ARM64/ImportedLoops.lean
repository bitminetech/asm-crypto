import Proofs.ARM64.ImportedCycles

/-!
Compose the recorded 33-word round cycle 64 times and identify its working
variables with the imported FIPS fold. Counter values, branch destinations,
memory, SP and the required register frame are maintained by induction.
`runCycles_words` identifies the iterator with execution of the repeated words.
-/
set_option Elab.async false

namespace Crypto.ARM64.Imported

theorem CoreFrame.refl (s : Arm64.State) : CoreFrame s s := by
  cases s
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CoreFrame.trans {a b c : Arm64.State} (h : CoreFrame a b) (k : CoreFrame b c) :
    CoreFrame a c := by
  obtain ⟨hs, hn, h0, h1, h2, h3, h4, h6⟩ := h
  obtain ⟨ks, kn, k0, k1, k2, k3, k4, k6⟩ := k
  exact ⟨ks.trans hs, kn.trans hn, k0.trans h0, k1.trans h1,
    k2.trans h2, k3.trans h3, k4.trans h4, k6.trans h6⟩

theorem CoreFrame.mem {a b : Arm64.State} (h : CoreFrame a b) : b.mem = a.mem := by
  have result := congrArg Arm64.State.mem h.1
  exact result

theorem CoreFrame.sp {a b : Arm64.State} (h : CoreFrame a b) : b.sp = a.sp := by
  have result := congrArg Arm64.State.sp h.1
  exact result

theorem CoreFrame.aligned {a b : Arm64.State} (h : CoreFrame a b) : b.spAligned = a.spAligned := by
  have result := congrArg Arm64.State.spAligned h.1
  exact result

theorem CoreFrame.x0 {a b : Arm64.State} (h : CoreFrame a b) : b.readReg64 .x0 = a.readReg64 .x0 :=
  h.2.2.1

def iterateStep {α : Type} (step : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n + 1, s => (iterateStep step n s).bind step

theorem iterateStep_invariant {α : Type} (step : α → Option α) (P : Nat → α → Prop)
    (n : Nat) (s : α) (h0 : P 0 s)
    (hs : ∀ i, i < n → ∀ mid, P i mid → ∃ out, step mid = some out ∧ P (i + 1) out) :
    ∃ out, iterateStep step n s = some out ∧ P n out := by
  induction n with
  | zero => exact ⟨s, rfl, h0⟩
  | succ n ih =>
    obtain ⟨mid, hm, hp⟩ := ih (fun i hi => hs i (by omega))
    obtain ⟨out, ho, hpost⟩ := hs n (by omega) mid hp
    refine ⟨out, ?_, hpost⟩
    change (iterateStep step n s).bind step = some out
    rw [hm]
    exact ho

def runCycles (code : List (BitVec 32)) (n : Nat) (s : Arm64.State) : Option Arm64.State :=
  iterateStep (runWords code) n s

theorem runCycles_words (code : List (BitVec 32)) (n : Nat) (s : Arm64.State) :
    runCycles code n s = runWords ((List.replicate n code).flatten) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (runCycles code n s).bind (runWords code) = _
    rw [List.replicate_succ', List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, runWords_append, ← ih]

theorem round_loop_prefix (s : Arm64.State) (W : Vector (BitVec 32) 64)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hwv : ∀ i : Fin 64, s.mem.read32 (s.sp + BitVec.ofNat 64 (4 * i.val)) = W[i.val]!)
    (n : Nat) (hn : n ≤ 64) :
    ∃ out, runCycles roundCycleCode n s = some out ∧ CoreFrame s out ∧
      out.pc = (if n < 64 then s.pc else s.pc + 132#64) ∧
      out.readReg64 .x5 = BitVec.ofNat 64 n ∧
      working out = Fin.foldl n
        (fun work (i : Fin n) => SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W i.val work)
        (working s) := by
  let P (i : Nat) (mid : Arm64.State) : Prop :=
    CoreFrame s mid ∧ mid.pc = (if i < 64 then s.pc else s.pc + 132#64) ∧
    mid.readReg64 .x5 = BitVec.ofNat 64 i ∧
    working mid = Fin.foldl i
      (fun work (j : Fin i) => SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W j.val work)
      (working s)
  have h0 : P 0 s := ⟨CoreFrame.refl s, rfl, hc, (Fin.foldl_zero _ _).symm⟩
  have hs (i : Nat) (hi : i < n) (mid : Arm64.State) (hp : P i mid) :
      ∃ out, runWords roundCycleCode mid = some out ∧ P (i + 1) out := by
    obtain ⟨hf, hp, hc', hw'⟩ := hp
    let t : Fin 64 := ⟨i, by omega⟩
    have kr : mid.mem.canRead (mid.readReg64 .x0 + (mid.readReg64 .x5 <<< 2)) 4 = true := by
      rw [hc', show i = t.val from rfl, index_shift_two, hf.mem, hf.x0]
      exact hkr t
    have wr : mid.mem.canRead (mid.sp + (mid.readReg64 .x5 <<< 2)) 4 = true := by
      rw [hc', show i = t.val from rfl, index_shift_two, hf.mem, hf.sp]
      exact hwr t
    have kv : mid.mem.read32 (mid.readReg64 .x0 + (mid.readReg64 .x5 <<< 2)) = SHS.SHA256.K[t.val]! := by
      rw [hc', show i = t.val from rfl, index_shift_two, hf.mem, hf.x0]
      exact hkv t
    have wv : mid.mem.read32 (mid.sp + (mid.readReg64 .x5 <<< 2)) = W[t.val]! := by
      rw [hc', show i = t.val from rfl, index_shift_two, hf.mem, hf.sp]
      exact hwv t
    obtain ⟨out, ho, ff, pc, count, work⟩ := round_cycle mid W t
      (by rw [hf.aligned]; exact hsp) kr wr kv wv hc'
    refine ⟨out, ho, hf.trans ff, ?_, count, ?_⟩
    · have hlt : i < 64 := by omega
      simp only [if_pos hlt] at hp
      simpa only [t, hp] using pc
    · have hpure :
          SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W i
            (Fin.foldl i (fun work (j : Fin i) =>
              SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W j.val work) (working s)) =
          Fin.foldl (i + 1) (fun work (j : Fin (i + 1)) =>
            SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W j.val work) (working s) :=
        (Fin.foldl_succ_last
          (fun work (j : Fin (i + 1)) =>
            SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W j.val work)
          (working s)).symm
      have hrewrite := congrArg (SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W i) hw'
      exact work.trans (hrewrite.trans hpure)
  exact iterateStep_invariant (runWords roundCycleCode) P n s h0 hs

theorem round_loop (s : Arm64.State) (W : Vector (BitVec 32) 64)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hwv : ∀ i : Fin 64, s.mem.read32 (s.sp + BitVec.ofNat 64 (4 * i.val)) = W[i.val]!) :
    ∃ out, runCycles roundCycleCode 64 s = some out ∧ CoreFrame s out ∧
      out.pc = s.pc + 132#64 ∧ out.readReg64 .x5 = 64#64 ∧
      working out = Fin.foldl 64
        (fun work (i : Fin 64) => SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W i.val work)
        (working s) := by
  obtain ⟨out, he, hf, hp, hc', hw⟩ := round_loop_prefix s W hsp hc hkr hwr hkv hwv 64 (by decide)
  exact ⟨out, he, hf, hp, hc', hw⟩

end Crypto.ARM64.Imported
