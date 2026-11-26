import Proofs.RISCV64.Schedule

namespace Crypto.RISCV64

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Crypto.ARM64.Imported
  (wordVector wordVector_store64 workspace_store_outside vector_setBang_eq_setIfInBounds)
open SHS.Equiv.VecBridge (getElem_bang_eq_getElem)

def loadCycle : List Instruction := inputWordBody ++ latch 16#64 (-56)

def loadCode : Nat → List Instruction
  | 0 => []
  | n + 1 => loadCode n ++ loadCycle

def blockWords (m : Memory) (addr : Addr) : Vector Word 16 :=
  Vector.ofFn fun i => byteWord m (addr + BitVec.ofNat 64 (4*i.val))

private theorem load_code_no_return (n : Nat) (i : Instruction) (hi : i ∈ loadCode n) :
    i.op ≠ .ret := by
  induction n with
  | zero => simp [loadCode] at hi
  | succ n ih =>
    rcases List.mem_append.mp hi with older | one
    · exact ih older
    · have check : loadCycle.all (fun j => !(j.op == .ret)) = true := by decide +kernel
      simpa using List.all_eq_true.mp check i one

attribute [local irreducible] run wordVector

private theorem load_word_cycle (base : Addr) (s : CPU) (t : Fin 16)
    (pc : s.pc = base + 0xf8) (index : s.reg 15 = BitVec.ofNat 64 t.val) :
    let out := run loadCycle s
    let word := (blockWords s.mem (s.reg 12))[t.val]
    ImageExecution base s loadCycle out ∧
      out.pc = (if t.val + 1 < 16 then base + 0xf8 else base + 0x134) ∧
      out.reg 15 = BitVec.ofNat 64 (t.val + 1) ∧
      out.reg 2 = s.reg 2 ∧ out.reg 12 = s.reg 12 ∧
      wordVector 64 out.mem (out.reg 2) = (wordVector 64 s.mem (s.reg 2)).set! t.val word ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  have straight : inputWordBody.all Instruction.linear = true := by decide +kernel
  have entry := ImageExecution.linear_run base s inputWordBody 0xf8 pc
    (by decide) inputWordBody_decoded straight
  obtain ⟨sp, payload, idx, advance⟩ := input_word_frame s
  have atLatch : (run inputWordBody s).pc = base + 0x12c := by
    rw [advance, pc, BitVec.add_assoc]; rfl
  have tBound := t.isLt
  let slot : Fin 64 := ⟨t.val, by omega⟩
  have address := table_index s 2 slot index
  have value : (run inputWordBody s).mem =
      s.mem.write32 (s.reg 2 + BitVec.ofNat 64 (4*slot.val))
        ((blockWords s.mem (s.reg 12))[t.val]) := by
    rw [input_word, address, table_index s 12 slot index]
    simp only [blockWords, Vector.getElem_ofFn]
    rfl
  obtain ⟨pos, next, same, keep⟩ :=
    latch_state (run inputWordBody s) 16 (-56) t.val (by omega) (by decide) (idx.trans index)
  have keepSP := keep 2 (by decide) (by decide)
  have tail := latch_execution base (run inputWordBody s) 0x12c 16 (-56) atLatch
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  dsimp only [loadCycle]
  rw [run_append]
  refine ⟨entry.append tail ?_, ?_, next, keepSP.trans sp,
    (keep 12 (by decide) (by decide)).trans payload, ?_, ?_⟩
  · intro i hi
    exact Instruction.linear_ne_return (List.all_eq_true.mp straight i hi)
  · rw [pos, atLatch]
    split <;> simp (config := { decide := true }) [BitVec.add_assoc]
  · rw [keepSP, sp, same, value, wordVector_store64]
  · intro p hp
    rw [same, value]
    exact workspace_store_outside s.mem _ p slot _ hp

theorem byteWord_eq_of_cells {m m' : Memory} (addr : Addr)
    (same : ∀ d : Fin 4, m.cells (addr + BitVec.ofNat 64 d.val) =
      m'.cells (addr + BitVec.ofNat 64 d.val)) :
    byteWord m addr = byteWord m' addr := by
  have b0 := same ⟨0, by decide⟩
  have b1 := same ⟨1, by decide⟩
  have b2 := same ⟨2, by decide⟩
  have b3 := same ⟨3, by decide⟩
  simp only [BitVec.add_zero] at b0 b1 b2 b3
  simp [byteWord, Arm64.Memory.read8, b0, b1, b2, b3]

private theorem blockWords_preserved (s out : CPU)
    (apart : ∀ i : Fin 16, ∀ d : Fin 4,
      256 ≤ (s.reg 12 + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 d.val - s.reg 2).toNat)
    (ptr : out.reg 12 = s.reg 12)
    (frame : ∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) :
    blockWords out.mem (out.reg 12) = blockWords s.mem (s.reg 12) := by
  rw [ptr]
  apply Vector.ext
  intro j hj
  simp only [blockWords, Vector.getElem_ofFn]
  exact byteWord_eq_of_cells _ fun d => frame _ (apart ⟨j, hj⟩ d)

private theorem load_prefix (base : Addr) (s : CPU)
    (pc : s.pc = base + 0xf8) (index : s.reg 15 = 0)
    (apart : ∀ i : Fin 16, ∀ d : Fin 4,
      256 ≤ (s.reg 12 + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 d.val - s.reg 2).toNat)
    (n : Nat) (bound : n ≤ 16) :
    let out := run (loadCode n) s
    ImageExecution base s (loadCode n) out ∧
      out.pc = (if n < 16 then base + 0xf8 else base + 0x134) ∧
      out.reg 15 = BitVec.ofNat 64 n ∧ out.reg 2 = s.reg 2 ∧ out.reg 12 = s.reg 12 ∧
      (∀ j, j < n → (wordVector 64 out.mem (out.reg 2))[j]! = (blockWords s.mem (s.reg 12))[j]!) ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  change s.reg 15#5 = 0#64 at index
  induction n with
  | zero =>
    simpa [loadCode, run, pc, index] using (ImageExecution.nil (base := base) s)
  | succ n ih =>
    have small : n < 16 := by omega
    obtain ⟨prior, pos, idx, sp, ptr, words, frame⟩ := ih (by omega)
    let mid := run (loadCode n) s
    obtain ⟨cycle, next, idx', sp', ptr', written, frame'⟩ :=
      load_word_cycle base mid ⟨n, small⟩ (by simpa only [if_pos small] using pos) idx
    dsimp only [loadCode]
    rw [run_append]
    refine ⟨prior.append cycle (load_code_no_return n), next, idx', sp'.trans sp,
      ptr'.trans ptr, ?_, ?_⟩
    · intro j hj
      have readable : j < 64 := by omega
      rw [written, vector_setBang_eq_setIfInBounds,
        getElem_bang_eq_getElem _ _ readable, Vector.getElem_setIfInBounds readable]
      by_cases h : n = j
      · subst j
        rw [if_pos rfl, blockWords_preserved s mid apart ptr frame, getElem_bang_eq_getElem _ _ small]
      · rw [if_neg h, ← getElem_bang_eq_getElem _ _ readable]
        exact words j (by omega)
    · intro p hp
      exact (frame' p (by rw [sp]; exact hp)).trans (frame p hp)

/-- The 16 fetched input-load iterations fill the prefix of the schedule
from the arbitrary 64-byte block at a2, using big-endian word order. -/
theorem load_words (base : Addr) (s : CPU)
    (pc : s.pc = base + 0xf8) (index : s.reg 15 = 0)
    (apart : ∀ i : Fin 16, ∀ d : Fin 4,
      256 ≤ (s.reg 12 + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 d.val - s.reg 2).toNat) :
    let out := run (loadCode 16) s
    ImageExecution base s (loadCode 16) out ∧ out.pc = base + 0x134 ∧
      out.reg 15 = 16 ∧ out.reg 2 = s.reg 2 ∧ out.reg 12 = s.reg 12 ∧
      (∀ j, j < 16 → (wordVector 64 out.mem (out.reg 2))[j]! = (blockWords s.mem (s.reg 12))[j]!) ∧
      (∀ p, 256 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨exec, exit, idx, sp, ptr, words, frame⟩ := load_prefix base s pc index apart 16 (by decide)
  exact ⟨exec, by simpa using exit, idx, sp, ptr, words, frame⟩

end Crypto.RISCV64
