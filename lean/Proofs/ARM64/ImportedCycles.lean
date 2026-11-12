import Proofs.ARM64.ImportedCounter
import Proofs.ARM64.ImportedScheduleRAM

/-! Composition of the recorded round body and ADD/CMP/B.LO control.
This is execution of a list of decoded words; instruction-fetch agreement and
whole-call `equal` are separate obligations. -/

namespace Crypto.ARM64.Imported

theorem runWords_append (xs ys : List (BitVec 32)) (s : Arm64.State) :
    runWords (xs ++ ys) s = (runWords xs s).bind (runWords ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons word rest ih =>
    cases hd : Arm64.decode word <;> simp [runWords, hd, ih]

theorem exists_of_map_some {α β : Type} (result : Option α) (f : α → β) (value : β)
    (h : result.map f = some value) : ∃ out, result = some out ∧ f out = value := by
  cases result with
  | none => simp at h
  | some out =>
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨out, rfl, h⟩

theorem controlStable_of_stable {before after : Arm64.State} (h : stable after = stable before) :
    controlStable after = controlStable before := by
  change { stable after with pstate := Arm64.PState.zero } =
    { stable before with pstate := Arm64.PState.zero }
  rw [h]

def CoreFrame (before after : Arm64.State) : Prop :=
  controlStable after = controlStable before ∧ nonvolatile after = nonvolatile before ∧
  after.readReg64 .x0 = before.readReg64 .x0 ∧
  after.readReg64 .x1 = before.readReg64 .x1 ∧
  after.readReg64 .x2 = before.readReg64 .x2 ∧
  after.readReg64 .x3 = before.readReg64 .x3 ∧
  after.readReg64 .x4 = before.readReg64 .x4 ∧
  after.readReg64 .x6 = before.readReg64 .x6

def roundCycleCode : List (BitVec 32) := Round.code ++ roundControlCode

theorem round_cycle (s : Arm64.State) (W : Vector (BitVec 32) 64) (t : Fin 64)
    (hsp : s.spAligned = true)
    (hk : s.mem.canRead (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canRead (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hK : s.mem.read32 (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) = SHS.SHA256.K[t.val]!)
    (hW : s.mem.read32 (s.sp + (s.readReg64 .x5 <<< 2)) = W[t.val]!)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    ∃ after, runWords roundCycleCode s = some after ∧ CoreFrame s after ∧
      after.pc = (if t.val + 1 < 64 then s.pc else s.pc + 132#64) ∧
      after.readReg64 .x5 = BitVec.ofNat 64 (t.val + 1) ∧
      working after = SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W t.val (working s) := by
  obtain ⟨body, hb, hwork⟩ := exists_of_map_some _ _ _
    (round_matches_spec s W t.val hsp hk hw hK hW)
  have frame := round_frame s hsp hk hw
  rw [hb] at frame
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at frame
  obtain ⟨hst, hpc, hnv, h0, h1, h2, h3, h4, h5, h6⟩ := frame
  obtain ⟨after, ha, post⟩ := exists_of_map_some _ _ _
    (round_control_step body t (h5.trans hc))
  simp only [Prod.mk.injEq] at post
  obtain ⟨hst', hpc', hnv', hwork', h0', h1', h2', h3', h4', h5', h6'⟩ := post
  refine ⟨after, ?_, ?_, ?_, h5', hwork'.trans hwork⟩
  · simp [roundCycleCode, runWords_append, hb, ha]
  · exact ⟨hst'.trans (controlStable_of_stable hst), hnv'.trans hnv,
      h0'.trans h0, h1'.trans h1, h2'.trans h2, h3'.trans h3, h4'.trans h4, h6'.trans h6⟩
  · rw [hpc', hpc]
    split <;> simp_all [BitVec.add_assoc, BitVec.add_sub_cancel]

end Crypto.ARM64.Imported
