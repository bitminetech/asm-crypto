import Proofs.RISCV64.FeedForward
import Proofs.RISCV64.Execution
import Proofs.ARM64.ImportedCellFrame
import Proofs.ARM64.ImportedExit

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (reverseWord reverseWord_byte wordVector read32_of_cells
  read32_write32 read_word_store_other region_word_store_delta write32_cells_outside
  bytes_of_reversed_words digestBytes memoryBytes32)

private def emitByte (shift : BitVec 6) (off : Nat) : List Instruction :=
  [⟨.srli 6 5 shift, 4⟩, ⟨.store .byte 6 11 (BitVec.ofNat 64 off), 4⟩]

def emitWord (i : Nat) : List Instruction :=
  [⟨.load .word 5 2 (BitVec.ofNat 64 (256 + 4*i)), 4⟩] ++
    emitByte 24 (4*i) ++ emitByte 16 (4*i + 1) ++ emitByte 8 (4*i + 2) ++
    [⟨.store .byte 5 11 (BitVec.ofNat 64 (4*i + 3)), 4⟩]

def digestPrefix : Nat → List Instruction
  | 0 => []
  | n+1 => digestPrefix n ++ emitWord n

def digestCode : List Instruction := digestPrefix 8

private theorem emit_decoded : ∀ i : Fin 8,
    decodeSeq (0x300 + 32*i.val) 8 = some (emitWord i.val) := by decide +kernel

private theorem lowDigit (v : Word) (offset : Nat) (within : offset + 8 ≤ 32) :
    (v.signExtend 64).extractLsb' offset 8 = v.extractLsb' offset 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend, hi,
    decide_true, Bool.true_and]
  simp only [show offset + i < 64 by omega, show offset + i < 32 by omega,
    decide_true, if_true, Bool.true_and]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem emit_word (base : Addr) (s : CPU) (i : Fin 8)
    (pc : s.pc = base + BitVec.ofNat 64 (0x300 + 32*i.val)) :
    let out := run (emitWord i.val) s
    ImageExecution base s (emitWord i.val) out ∧
      out.pc = base + BitVec.ofNat 64 (0x300 + 32*(i.val+1)) ∧
      out.reg 2 = s.reg 2 ∧ out.reg 11 = s.reg 11 ∧
      out.mem = s.mem.write32 (s.reg 11 + BitVec.ofNat 64 (4*i.val))
        (reverseWord (s.mem.read32 (s.reg 2 + BitVec.ofNat 64 (256 + 4*i.val)))) := by
  have linear : (emitWord i.val).all Instruction.linear = true := by rfl
  have total : ((emitWord i.val).map Instruction.bytes).sum = 32 := rfl
  refine ⟨ImageExecution.linear_run base s _ _ pc (by rw [total]; have := i.isLt; omega)
    (emit_decoded i) linear, ?_, ?_⟩
  · rw [linear_end_pc _ s linear, total, pc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  · let w := s.mem.read32 (s.reg 2#5 + (256#64 + BitVec.ofNat 64 (4*i.val)))
    have b0 : (reverseWord w).extractLsb' 0 8 = w.extractLsb' 24 8 := reverseWord_byte w ⟨0, by decide⟩
    have b1 : (reverseWord w).extractLsb' 8 8 = w.extractLsb' 16 8 := reverseWord_byte w ⟨1, by decide⟩
    have b2 : (reverseWord w).extractLsb' 16 8 = w.extractLsb' 8 8 := reverseWord_byte w ⟨2, by decide⟩
    have b3 : (reverseWord w).extractLsb' 24 8 = w.extractLsb' 0 8 := reverseWord_byte w ⟨3, by decide⟩
    dsimp only [w] at b0 b1 b2 b3
    simp (config := { decide := true }) [emitWord, emitByte, run, Instruction.step, Width.store, Width.load,
      Arm64.Memory.write32, BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ofNat_add, BitVec.add_assoc,
      b0, b1, b2, b3, lowDigit]
    simp only [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64), lowDigit _ _ (by decide : 0 + 8 ≤ 32)]

private theorem no_return (n : Nat) (i : Instruction) (valid : i ∈ digestPrefix n) :
    i.op ≠ .ret := by
  induction n with
  | zero => simp [digestPrefix] at valid
  | succ n ih =>
    rcases List.mem_append.mp valid with before | one
    · exact ih before
    · exact Instruction.linear_ne_return (List.all_eq_true.mp (by rfl :
          (emitWord n).all Instruction.linear = true) i one)

attribute [local irreducible] run wordVector Arm64.Memory.read32 Arm64.Memory.write32

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 10000 in
private theorem digest_prefix (base : Addr) (s : CPU) (n : Nat) (bound : n ≤ 8)
    (pc : s.pc = base + 0x300)
    (apart : ∀ i : Fin 8, ∀ d : Fin 4,
      32 ≤ (s.reg 2 + BitVec.ofNat 64 (256+4*i.val) + BitVec.ofNat 64 d.val - s.reg 11).toNat) :
    ∃ out, ImageExecution base s (digestPrefix n) out ∧
      out.pc = base + BitVec.ofNat 64 (0x300+32*n) ∧ out.reg 2 = s.reg 2 ∧
      out.reg 11 = s.reg 11 ∧
      (∀ p, 32 ≤ (p-s.reg 11).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ i : Fin 8, i.val < n →
        out.mem.read32 (s.reg 11 + BitVec.ofNat 64 (4*i.val)) = reverseWord ((storedHash s)[i.val])) := by
  induction n with
  | zero =>
    exact ⟨s, .nil _, pc, rfl, rfl, fun _ _ => rfl, fun _ h => by omega⟩
  | succ n ih =>
    have small : n < 8 := by omega
    let idx : Fin 8 := ⟨n,small⟩
    obtain ⟨mid, before, pos, stack, dst, frame, words⟩ := ih (by omega)
    obtain ⟨one, advance, sp, ptr, write⟩ := emit_word base mid idx pos
    let out := run (emitWord n) mid
    let hashSlot := s.reg 2 + BitVec.ofNat 64 (256+4*n)
    have value : mid.mem.read32 hashSlot = (storedHash s)[n] := by
      rw [read32_of_cells hashSlot (fun d => frame _ (apart idx d))]
      simp [storedHash, wordVector, hashSlot, BitVec.ofNat_add, BitVec.add_assoc]
    have store : out.mem = mid.mem.write32 (s.reg 11 + BitVec.ofNat 64 (4*n))
        (reverseWord ((storedHash s)[n])) := by
      have fixed : out.mem = mid.mem.write32 (s.reg 11 + BitVec.ofNat 64 (4*n))
          (reverseWord (mid.mem.read32 hashSlot)) := by
        simpa only [stack, dst, idx, hashSlot] using write
      exact fixed.trans (congrArg (fun v => mid.mem.write32 (s.reg 11 + BitVec.ofNat 64 (4*n))
        (reverseWord v)) value)
    refine ⟨out, before.append one (no_return n), advance, sp.trans stack, ptr.trans dst, ?_, ?_⟩
    · intro p hp
      rw [store]
      exact (write32_cells_outside _ _ _ _ (region_word_store_delta _ _ _ 32 (by omega) hp)).trans (frame p hp)
    · intro i hi
      rw [store]
      by_cases same : i.val = n
      · simp only [same, read32_write32]
      · have distinct : idx.castLE (by decide : 8 ≤ 64) ≠ i.castLE (by decide : 8 ≤ 64) := by
          intro eq
          exact same (congrArg Fin.val eq.symm)
        have keep := read_word_store_other mid.mem (s.reg 11) _ _
          (reverseWord ((storedHash s)[n])) distinct
        exact keep.trans (words i (by omega))

/-- Serialize all 32 digest bytes from the stack hash words, and stop at
the epilogue. The destination's initial bytes are arbitrary. -/
theorem digest_written (base : Addr) (s : CPU) (pc : s.pc = base + 0x300)
    (apart : ∀ i : Fin 8, ∀ d : Fin 4,
      32 ≤ (s.reg 2 + BitVec.ofNat 64 (256+4*i.val) + BitVec.ofNat 64 d.val - s.reg 11).toNat) :
    ∃ out, ImageExecution base s digestCode out ∧ out.pc = base + 0x400 ∧
      out.reg 2 = s.reg 2 ∧ out.reg 11 = s.reg 11 ∧
      memoryBytes32 out.mem (s.reg 11) = digestBytes (storedHash s) ∧
      (∀ p, 32 ≤ (p-s.reg 11).toNat → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨out, ran, exit, sp, ptr, frame, written⟩ := digest_prefix base s 8 (by decide) pc apart
  refine ⟨out, ran, exit, sp, ptr, bytes_of_reversed_words _ _ _ ?_, frame⟩
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn, Vector.getElem_map]
  exact written ⟨i,hi⟩ hi

end Crypto.RISCV64
