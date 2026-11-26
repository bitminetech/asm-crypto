import Proofs.RISCV64.CounterLoop
import Proofs.ARM64.ImportedScheduleSpec
import Proofs.ARM64.ImportedMemoryRange

namespace Crypto.RISCV64

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Crypto.ARM64.Imported
  (wordVector wordVector_store64 index_shift_two slot_address_back schedule_step_get_self
   expandedWords expanded_eq_schedule workspace_store_outside)
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Fused (getElem!_specScheduleStep_ne)
open SHS.Equiv.VecBridge (getElem_bang_eq_getElem)

private theorem wordVector_get (m : Memory) (base : Addr) (i : Fin 64) :
    (wordVector 64 m base)[i.val]! =
      m.read32 (base + BitVec.ofNat 64 (4 * i.val)) := by
  rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ i.isLt]
  simp only [wordVector, Vector.getElem_ofFn]

theorem table_index (s : CPU) (base : Reg) (t : Fin 64)
    (index : s.reg 15 = BitVec.ofNat 64 t.val) :
    tableAddress s base = s.reg base + BitVec.ofNat 64 (4 * t.val) := by
  rw [tableAddress, index, index_shift_two t]

private theorem previousWord (s : CPU) (t : Fin 64) (k : Nat) (hk : k ≤ t.val)
    (index : s.reg 15 = BitVec.ofNat 64 t.val) :
    s.mem.read32 (tableAddress s 2 - BitVec.ofNat 64 (4*k)) =
      (wordVector 64 s.mem (s.reg 2))[t.val-k]! := by
  have hb : t.val - k < 64 := by have := t.isLt; omega
  rw [table_index s 2 t index, slot_address_back _ _ _ hk]
  exact (wordVector_get s.mem (s.reg 2) ⟨t.val - k, hb⟩).symm

theorem expansion_schedule (s : CPU) (M : Vector Word 16) (t : Fin 64) (ht : 16 ≤ t.val)
    (index : s.reg 15 = BitVec.ofNat 64 t.val) :
    let out := run expansionBody s
    wordVector 64 out.mem (out.reg 2) = specScheduleStep M t.val (wordVector 64 s.mem (s.reg 2)) := by
  dsimp only
  rw [(expansion_frame s).1, expansion_value, table_index s 2 t index, wordVector_store64]
  have expanded : expandedWord s =
      (specScheduleStep M t.val (wordVector 64 s.mem (s.reg 2)))[t.val]! := by
    rw [schedule_step_get_self, if_neg (by omega)]
    unfold expandedWord
    change
      SHS.SHA256.smallSigma1 (s.mem.read32 (tableAddress s 2 - BitVec.ofNat 64 (4*2))) +
        s.mem.read32 (tableAddress s 2 - BitVec.ofNat 64 (4*7)) +
        SHS.SHA256.smallSigma0 (s.mem.read32 (tableAddress s 2 - BitVec.ofNat 64 (4*15))) +
        s.mem.read32 (tableAddress s 2 - BitVec.ofNat 64 (4*16)) = _
    rw [previousWord s t 2 (by omega) index, previousWord s t 7 (by omega) index,
      previousWord s t 15 (by omega) index, previousWord s t 16 ht index]
  apply Vector.ext
  intro j hj
  rw [Crypto.ARM64.Imported.vector_setBang_eq_setIfInBounds, Vector.getElem_setIfInBounds hj]
  by_cases same : t.val = j
  · subst j
    rw [if_pos rfl, expanded, getElem_bang_eq_getElem _ _ hj]
  · rw [if_neg same]
    have keep := getElem!_specScheduleStep_ne M t.val
      (wordVector 64 s.mem (s.reg 2)) j (Ne.symm same)
    simpa only [getElem_bang_eq_getElem _ _ hj] using keep.symm

def expansionCycle : List Instruction := expansionBody ++ latch 64#64 (-118)

def expansionCode : Nat → List Instruction
  | 0 => []
  | n + 1 => expansionCode n ++ expansionCycle

private theorem expansion_code_no_return (n : Nat) (i : Instruction) (hi : i ∈ expansionCode n) :
    i.op ≠ .ret := by
  induction n with
  | zero => simp [expansionCode] at hi
  | succ n ih =>
    rcases List.mem_append.mp hi with older | one
    · exact ih older
    · have check : expansionCycle.all (fun j => !(j.op == .ret)) = true := by decide +kernel
      simpa using List.all_eq_true.mp check i one

attribute [local irreducible] run wordVector specScheduleStep

private theorem expansion_cycle (base : Addr) (s : CPU) (M : Vector Word 16)
    (t : Fin 64) (ht : 16 ≤ t.val) (pc : s.pc = base + 0x134)
    (index : s.reg 15 = BitVec.ofNat 64 t.val) :
    let out := run expansionCycle s
    ImageExecution base s expansionCycle out ∧
      out.pc = (if t.val + 1 < 64 then base + 0x134 else base + 0x1ae) ∧
      out.reg 15 = BitVec.ofNat 64 (t.val + 1) ∧ out.reg 2 = s.reg 2 ∧
      wordVector 64 out.mem (out.reg 2) = specScheduleStep M t.val (wordVector 64 s.mem (s.reg 2)) ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  have linear : expansionBody.all Instruction.linear = true := by decide +kernel
  have straight := ImageExecution.linear_run base s expansionBody 0x134 pc (by decide)
    expansionBody_decoded linear
  have midPC : (run expansionBody s).pc = base + 0x1a4 := by
    rw [(expansion_frame s).2.2, pc, BitVec.add_assoc]; rfl
  have eqIndex := (expansion_frame s).2.1.trans index
  have small := t.isLt
  obtain ⟨next, idx, mem, keep⟩ := latch_state (run expansionBody s) 64 (-118) t.val
    (by omega) (by decide) eqIndex
  have sp := keep 2 (by decide) (by decide)
  have tail := latch_execution base (run expansionBody s) 0x1a4 64 (-118) midPC
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  dsimp only [expansionCycle]
  rw [run_append]
  refine ⟨straight.append tail ?_, ?_, idx, sp.trans (expansion_frame s).1, ?_, ?_⟩
  · intro i hi
    exact Instruction.linear_ne_return (List.all_eq_true.mp linear i hi)
  · rw [next, midPC]
    split <;> simp (config := { decide := true }) [BitVec.add_assoc]
  · rw [mem, sp]
    exact expansion_schedule s M t ht index
  · intro p hp
    rw [mem, expansion_value, table_index s 2 t index]
    exact workspace_store_outside s.mem (s.reg 2) p t (expandedWord s) hp

private theorem expansion_prefix (base : Addr) (s : CPU) (M : Vector Word 16)
    (pc : s.pc = base + 0x134) (index : s.reg 15 = 16) (n : Nat) (bound : n ≤ 48) :
    let out := run (expansionCode n) s
    ImageExecution base s (expansionCode n) out ∧
      out.pc = (if 16 + n < 64 then base + 0x134 else base + 0x1ae) ∧
      out.reg 15 = BitVec.ofNat 64 (16+n) ∧ out.reg 2 = s.reg 2 ∧
      wordVector 64 out.mem (out.reg 2) = expandedWords M (wordVector 64 s.mem (s.reg 2)) n ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  change s.reg 15#5 = 16#64 at index
  induction n with
  | zero =>
    simpa [expansionCode, run, expandedWords, pc, index] using (ImageExecution.nil (base := base) s)
  | succ n ih =>
    have small : 16+n < 64 := by omega
    obtain ⟨prior, pos, idx, sp, before, frame⟩ := ih (by omega)
    let mid := run (expansionCode n) s
    obtain ⟨cycle, exit, idx', sp', words, preserve⟩ := expansion_cycle base mid M
      ⟨16+n, small⟩ (by change 16 ≤ 16+n; omega) (by simpa only [if_pos small] using pos) idx
    dsimp only [expansionCode]
    rw [run_append]
    refine ⟨prior.append cycle (expansion_code_no_return n), exit, idx', sp'.trans sp, ?_, ?_⟩
    · rw [words, before]
      simp only [expandedWords, Fin.foldl_succ_last, Fin.val_last, Fin.val_castSucc]
    · intro p hp
      exact (preserve _ (by rw [sp]; exact hp)).trans (frame _ hp)

/-- The linked expansion loop fills the rest of the 256-byte schedule from
its first 16 words, independently of the old contents in slots 16 through 63. -/
theorem expansion_loaded (base : Addr) (s : CPU) (M : Vector Word 16)
    (pc : s.pc = base + 0x134) (index : s.reg 15 = 16)
    (initial : ∀ j, j < 16 → (wordVector 64 s.mem (s.reg 2))[j]! = M[j]!) :
    let out := run (expansionCode 48) s
    ImageExecution base s (expansionCode 48) out ∧ out.pc = base + 0x1ae ∧
      out.reg 2 = s.reg 2 ∧ wordVector 64 out.mem (out.reg 2) = SHS.SHA256.schedule M ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨exec, exit, _, sp, words, frame⟩ := expansion_prefix base s M pc index 48 (by decide)
  exact ⟨exec, by simpa using exit, sp, words.trans (expanded_eq_schedule M _ initial), frame⟩

end Crypto.RISCV64
