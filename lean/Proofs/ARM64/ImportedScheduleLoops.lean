import Proofs.ARM64.ImportedLoops
import Proofs.ARM64.ImportedScheduleCycle
import Proofs.ARM64.ImportedScheduleSpec

/-!
The 48 recorded schedule-expansion cycles maintain the register/state frame
and workspace permissions. Their final RAM snapshot is the imported FIPS
schedule whenever the first 16 words initially contain the message block;
the other workspace bytes may be arbitrary. Fetching, source-word loading,
whole-function memory bounds and `equal` remain separate obligations.
-/
namespace Crypto.ARM64.Imported

theorem DataFrame.refl (s : Arm64.State) : DataFrame s s := by
  cases s
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem DataFrame.trans {a b c : Arm64.State} (h : DataFrame a b) (k : DataFrame b c) :
    DataFrame a c := by
  obtain ⟨hs, hn, h0, h1, h2, h3, h4, h6⟩ := h
  obtain ⟨ks, kn, k0, k1, k2, k3, k4, k6⟩ := k
  exact ⟨ks.trans hs, kn.trans hn, k0.trans h0, k1.trans h1,
    k2.trans h2, k3.trans h3, k4.trans h4, k6.trans h6⟩

theorem DataFrame.sp {a b : Arm64.State} (h : DataFrame a b) : b.sp = a.sp := by
  have result := congrArg Arm64.State.sp h.1
  exact result

theorem schedule_loop_prefix (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hc : s.readReg64 .x5 = 16#64)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (n : Nat) (hn : n ≤ 48) :
    ∃ out, runCycles scheduleCycleCode n s = some out ∧ DataFrame s out ∧
      out.pc = (if 16 + n < 64 then s.pc else s.pc + 72#64) ∧
      out.readReg64 .x5 = BitVec.ofNat 64 (16 + n) ∧
      wordVector 64 out.mem out.sp = Fin.foldl n
        (fun W (i : Fin n) => SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + i.val) W)
        (wordVector 64 s.mem s.sp) ∧
      (∀ i : Fin 64, out.mem.canRead (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) := by
  let P (i : Nat) (mid : Arm64.State) : Prop :=
    DataFrame s mid ∧ mid.pc = (if 16 + i < 64 then s.pc else s.pc + 72#64) ∧
    mid.readReg64 .x5 = BitVec.ofNat 64 (16 + i) ∧
    wordVector 64 mid.mem mid.sp = Fin.foldl i
      (fun W (j : Fin i) => SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + j.val) W)
      (wordVector 64 s.mem s.sp) ∧
    (∀ j : Fin 64, mid.mem.canRead (mid.sp + BitVec.ofNat 64 (4 * j.val)) 4 = true) ∧
    (∀ j : Fin 64, mid.mem.canWrite (mid.sp + BitVec.ofNat 64 (4 * j.val)) 4 = true)
  have h0 : P 0 s := ⟨DataFrame.refl s, rfl, hc, (Fin.foldl_zero _ _).symm, hr, hw⟩
  have hs (i : Nat) (hi : i < n) (mid : Arm64.State) (hp : P i mid) :
      ∃ out, runWords scheduleCycleCode mid = some out ∧ P (i + 1) out := by
    obtain ⟨hf, hp, hc', hwords, hr', hw'⟩ := hp
    let t : Fin 64 := ⟨16 + i, by omega⟩
    obtain ⟨out, ho, ff, pc, count, mem, words⟩ :=
      schedule_cycle mid M t (by dsimp [t]; omega) hc' hr' hw'
    refine ⟨out, ho, hf.trans ff, ?_, ?_, ?_, ?_, ?_⟩
    · have hlt : 16 + i < 64 := by omega
      simp only [if_pos hlt] at hp
      simpa only [t, hp, Nat.add_assoc] using pc
    · simpa only [t, Nat.add_assoc] using count
    · have hpure :
          SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + i)
            (Fin.foldl i (fun W (j : Fin i) =>
              SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + j.val) W)
              (wordVector 64 s.mem s.sp)) =
          Fin.foldl (i + 1) (fun W (j : Fin (i + 1)) =>
            SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + j.val) W)
            (wordVector 64 s.mem s.sp) :=
        (Fin.foldl_succ_last
          (fun W (j : Fin (i + 1)) =>
            SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + j.val) W)
          (wordVector 64 s.mem s.sp)).symm
      exact words.trans ((congrArg
        (SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + i)) hwords).trans hpure)
    · intro j
      rw [mem, ff.sp]
      exact canRead_write32 _ _ _ _ _ (hr' j)
    · intro j
      rw [mem, ff.sp, canWrite_write32]
      exact hw' j
  exact iterateStep_invariant (runWords scheduleCycleCode) P n s h0 hs

theorem schedule_loop (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hc : s.readReg64 .x5 = 16#64)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ out, runCycles scheduleCycleCode 48 s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 72#64 ∧ out.readReg64 .x5 = 64#64 ∧
      wordVector 64 out.mem out.sp = Fin.foldl 48
        (fun W (i : Fin 48) => SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M (16 + i.val) W)
        (wordVector 64 s.mem s.sp) ∧
      (∀ i : Fin 64, out.mem.canRead (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) := by
  obtain ⟨out, he, hf, hp, hc', hwords, hr', hw'⟩ := schedule_loop_prefix s M hc hr hw 48 (by decide)
  exact ⟨out, he, hf, hp, hc', hwords, hr', hw'⟩

theorem schedule_loop_matches_spec (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hc : s.readReg64 .x5 = 16#64)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hfirst : ∀ j, j < 16 → (wordVector 64 s.mem s.sp)[j]! = M[j]!) :
    ∃ out, runCycles scheduleCycleCode 48 s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 72#64 ∧ out.readReg64 .x5 = 64#64 ∧
      wordVector 64 out.mem out.sp = SHS.SHA256.schedule M ∧
      (∀ i : Fin 64, out.mem.canRead (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) := by
  obtain ⟨out, he, hf, hp, hc', words, hr', hw'⟩ := schedule_loop s M hc hr hw
  exact ⟨out, he, hf, hp, hc', words.trans
    (expanded_eq_schedule M (wordVector 64 s.mem s.sp) hfirst), hr', hw'⟩

end Crypto.ARM64.Imported
