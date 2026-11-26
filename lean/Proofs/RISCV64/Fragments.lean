import Models.RISCV64SHA256Decode
import Proofs.ARM64.Round
import Reference.WordModel

namespace Crypto.RISCV64

def inputWordBody : List Instruction := [
  ⟨.slli 6 15 2, 4⟩,
  ⟨.add 7 12 6, 4⟩,
  ⟨.load .byte 28 7 0, 4⟩,
  ⟨.load .byte 29 7 1, 4⟩,
  ⟨.load .byte 30 7 2, 4⟩,
  ⟨.load .byte 31 7 3, 4⟩,
  ⟨.slliw 28 28 24, 4⟩,
  ⟨.slli 29 29 16, 2⟩,
  ⟨.slli 30 30 8, 2⟩,
  ⟨.or 28 28 29, 4⟩,
  ⟨.or 28 28 30, 4⟩,
  ⟨.or 28 28 31, 4⟩,
  ⟨.add 7 2 6, 4⟩,
  ⟨.store .word 28 7 0, 4⟩
]

set_option maxRecDepth 10000 in
theorem inputWordBody_decoded :
    decodeSeq 0xf8 14 = some inputWordBody := by decide +kernel

def expansionBody : List Instruction := [
  ⟨.slli 6 15 2, 4⟩,
  ⟨.add 7 2 6, 4⟩,
  ⟨.load .word 5 7 (-60), 4⟩,
  ⟨.srliw 28 5 7, 4⟩,
  ⟨.slliw 29 5 25, 4⟩,
  ⟨.or 28 28 29, 4⟩,
  ⟨.srliw 29 5 18, 4⟩,
  ⟨.slliw 30 5 14, 4⟩,
  ⟨.or 29 29 30, 4⟩,
  ⟨.xor 28 28 29, 4⟩,
  ⟨.srliw 29 5 3, 4⟩,
  ⟨.xor 28 28 29, 4⟩,
  ⟨.load .word 5 7 (-8), 4⟩,
  ⟨.srliw 29 5 17, 4⟩,
  ⟨.slliw 30 5 15, 4⟩,
  ⟨.or 29 29 30, 4⟩,
  ⟨.srliw 30 5 19, 4⟩,
  ⟨.slliw 31 5 13, 4⟩,
  ⟨.or 30 30 31, 4⟩,
  ⟨.xor 29 29 30, 4⟩,
  ⟨.srliw 30 5 10, 4⟩,
  ⟨.xor 29 29 30, 4⟩,
  ⟨.load .word 5 7 (-64), 4⟩,
  ⟨.addw 28 28 5, 4⟩,
  ⟨.load .word 5 7 (-28), 4⟩,
  ⟨.addw 28 28 5, 4⟩,
  ⟨.addw 28 28 29, 4⟩,
  ⟨.store .word 28 7 0, 4⟩
]

set_option maxRecDepth 10000 in
theorem expansionBody_decoded :
    decodeSeq 0x134 28 = some expansionBody := by decide +kernel

def roundBody : List Instruction := [
  ⟨.srliw 5 20 6, 4⟩,
  ⟨.slliw 6 20 26, 4⟩,
  ⟨.or 5 5 6, 4⟩,
  ⟨.srliw 6 20 11, 4⟩,
  ⟨.slliw 7 20 21, 4⟩,
  ⟨.or 6 6 7, 4⟩,
  ⟨.xor 5 5 6, 4⟩,
  ⟨.srliw 6 20 25, 4⟩,
  ⟨.slliw 7 20 7, 4⟩,
  ⟨.or 6 6 7, 4⟩,
  ⟨.xor 5 5 6, 4⟩,
  ⟨.addw 23 23 5, 4⟩,
  ⟨.xor 5 21 22, 4⟩,
  ⟨.and 5 5 20, 4⟩,
  ⟨.xor 5 5 22, 4⟩,
  ⟨.addw 23 23 5, 4⟩,
  ⟨.slli 6 15 2, 4⟩,
  ⟨.add 7 10 6, 4⟩,
  ⟨.load .word 5 7 0, 4⟩,
  ⟨.addw 23 23 5, 4⟩,
  ⟨.add 7 2 6, 4⟩,
  ⟨.load .word 5 7 0, 4⟩,
  ⟨.addw 23 23 5, 4⟩,
  ⟨.addw 19 19 23, 4⟩,
  ⟨.srliw 5 8 2, 4⟩,
  ⟨.slliw 6 8 30, 4⟩,
  ⟨.or 5 5 6, 4⟩,
  ⟨.srliw 6 8 13, 4⟩,
  ⟨.slliw 7 8 19, 4⟩,
  ⟨.or 6 6 7, 4⟩,
  ⟨.xor 5 5 6, 4⟩,
  ⟨.srliw 6 8 22, 4⟩,
  ⟨.slliw 7 8 10, 4⟩,
  ⟨.or 6 6 7, 4⟩,
  ⟨.xor 5 5 6, 4⟩,
  ⟨.addw 23 23 5, 4⟩,
  ⟨.or 5 8 9, 4⟩,
  ⟨.and 5 5 18, 4⟩,
  ⟨.and 6 8 9, 4⟩,
  ⟨.or 5 5 6, 4⟩,
  ⟨.addw 28 23 5, 4⟩,
  ⟨.add 23 0 22, 2⟩,
  ⟨.add 22 0 21, 2⟩,
  ⟨.add 21 0 20, 2⟩,
  ⟨.add 20 0 19, 2⟩,
  ⟨.add 19 0 18, 2⟩,
  ⟨.add 18 0 9, 2⟩,
  ⟨.add 9 0 8, 2⟩,
  ⟨.add 8 0 28, 2⟩
]

set_option maxRecDepth 10000 in
theorem roundBody_decoded :
    decodeSeq 0x1d0 49 = some roundBody := by decide +kernel

def loadHashBody : List Instruction := [
  ⟨.load .word 8 2 256, 4⟩,
  ⟨.load .word 9 2 260, 4⟩,
  ⟨.load .word 18 2 264, 4⟩,
  ⟨.load .word 19 2 268, 4⟩,
  ⟨.load .word 20 2 272, 4⟩,
  ⟨.load .word 21 2 276, 4⟩,
  ⟨.load .word 22 2 280, 4⟩,
  ⟨.load .word 23 2 284, 4⟩,
  ⟨.addi 15 0 0, 2⟩
]

set_option maxRecDepth 10000 in
theorem loadHashBody_decoded :
    decodeSeq 0x1ae 9 = some loadHashBody := by decide +kernel

/-- The eight SHA working words occupy s0 through s7, in ABI order. -/
def working (s : CPU) : Vector Word 8 :=
  #v[(s.reg 8).setWidth 32, (s.reg 9).setWidth 32, (s.reg 18).setWidth 32,
     (s.reg 19).setWidth 32, (s.reg 20).setWidth 32, (s.reg 21).setWidth 32,
     (s.reg 22).setWidth 32, (s.reg 23).setWidth 32]

theorem narrow_sign (x : Word) : (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show i < 64 by omega, if_pos, decide_true, Bool.true_and]

private theorem smallSigma0 (x : Word) :
    ((x >>> (7 : Nat)) ||| (x <<< (25 : Nat))) ^^^
      ((x >>> (18 : Nat)) ||| (x <<< (14 : Nat))) ^^^ (x >>> (3 : Nat)) =
      EthLib.Cryptography.Hash.Sha256.Spec.small0 x := by
  simp only [EthLib.Cryptography.Hash.Sha256.Spec.small0, BitVec.rotateRight_def, BitVec.xor_assoc]

private theorem smallSigma1 (x : Word) :
    ((x >>> (17 : Nat)) ||| (x <<< (15 : Nat))) ^^^
      ((x >>> (19 : Nat)) ||| (x <<< (13 : Nat))) ^^^ (x >>> (10 : Nat)) =
      EthLib.Cryptography.Hash.Sha256.Spec.small1 x := by
  simp only [EthLib.Cryptography.Hash.Sha256.Spec.small1, BitVec.rotateRight_def, BitVec.xor_assoc]

private theorem bigSigma0 (x : Word) :
    ((x >>> (2 : Nat)) ||| (x <<< (30 : Nat))) ^^^
      ((x >>> (13 : Nat)) ||| (x <<< (19 : Nat))) ^^^
      ((x >>> (22 : Nat)) ||| (x <<< (10 : Nat))) = EthLib.Cryptography.Hash.Sha256.Spec.large0 x := by
  simp only [EthLib.Cryptography.Hash.Sha256.Spec.large0, BitVec.rotateRight_def, BitVec.xor_assoc]

private theorem bigSigma1 (x : Word) :
    ((x >>> (6 : Nat)) ||| (x <<< (26 : Nat))) ^^^
      ((x >>> (11 : Nat)) ||| (x <<< (21 : Nat))) ^^^
      ((x >>> (25 : Nat)) ||| (x <<< (7 : Nat))) = EthLib.Cryptography.Hash.Sha256.Spec.large1 x := by
  simp only [EthLib.Cryptography.Hash.Sha256.Spec.large1, BitVec.rotateRight_def, BitVec.xor_assoc]

private theorem choose (x y z : Word) :
    ((y ^^^ z) &&& x) ^^^ z = Crypto.Reference.WordModel.Ch x y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Crypto.Reference.WordModel.Ch, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

def tableAddress (s : CPU) (base : Reg) : Addr := s.reg base + (s.reg 15 <<< (2 : Nat))

def expandedWord (s : CPU) : Word :=
  let a := tableAddress s 2
  EthLib.Cryptography.Hash.Sha256.Spec.small1 (s.mem.read32 (a - 8)) + s.mem.read32 (a - 28) +
    EthLib.Cryptography.Hash.Sha256.Spec.small0 (s.mem.read32 (a - 60)) + s.mem.read32 (a - 64)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem round_value (s : CPU) :
    working (run roundBody s) = Crypto.ARM64.Round.fipsRound (working s)
      (s.mem.read32 (tableAddress s 10)) (s.mem.read32 (tableAddress s 2)) := by
  simp (config := { decide := true }) [run, roundBody, Instruction.step, Width.load, working,
    Crypto.ARM64.Round.fipsRound, tableAddress, narrow_sign, Crypto.Reference.WordModel.Maj,
    Crypto.ARM64.Round.maj_factored, choose, bigSigma0, bigSigma1, BitVec.add_assoc]

private theorem addLeftComm (x y z : Word) :
    x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem expansion_value (s : CPU) :
    (run expansionBody s).mem = s.mem.write32 (tableAddress s 2) (expandedWord s) := by
  simp (config := { decide := true }) [run, expansionBody, Instruction.step, Width.load,
    Width.store, tableAddress, expandedWord, narrow_sign, smallSigma0, smallSigma1,
    BitVec.sub_eq_add_neg, BitVec.add_assoc, addLeftComm, BitVec.add_comm]

theorem run_append (xs ys : List Instruction) (s : CPU) :
    run (xs ++ ys) s = run ys (run xs s) := by simp [run, List.foldl_append]

def byteWord (m : Memory) (a : Addr) : Word :=
  m.read8 a ++ m.read8 (a + 1) ++ m.read8 (a + 2) ++ m.read8 (a + 3)

private theorem assembleWord (a b c d : BitVec 8) :
    (a.setWidth 32 <<< (24 : Nat)) ||| (b.setWidth 32 <<< (16 : Nat)) |||
      (c.setWidth 32 <<< (8 : Nat)) ||| d.setWidth 32 = a ++ b ++ c ++ d := by
  exact (BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (b := a) (b' := b) (b'' := c) (b''' := d) (w'''' := 32)).symm

set_option maxHeartbeats 2000000 in
theorem input_word (s : CPU) :
    (run inputWordBody s).mem = s.mem.write32 (tableAddress s 2)
      (byteWord s.mem (tableAddress s 12)) := by
  simp (config := { decide := true }) [run, inputWordBody, Instruction.step, Width.load,
    Width.store, tableAddress, byteWord, narrow_sign, BitVec.setWidth_shiftLeft_of_le (by decide : 32 ≤ 64), assembleWord]

theorem load_hash (s : CPU) :
    working (run loadHashBody s) =
      #v[s.mem.read32 (s.reg 2 + 256), s.mem.read32 (s.reg 2 + 260),
         s.mem.read32 (s.reg 2 + 264), s.mem.read32 (s.reg 2 + 268),
         s.mem.read32 (s.reg 2 + 272), s.mem.read32 (s.reg 2 + 276),
         s.mem.read32 (s.reg 2 + 280), s.mem.read32 (s.reg 2 + 284)] := by
  simp (config := { decide := true }) [run, loadHashBody, Instruction.step,
    Width.load, working, narrow_sign]

set_option maxHeartbeats 3500000 in
theorem round_frame (s : CPU) :
    let out := run roundBody s
    out.mem = s.mem ∧ out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧
      out.reg 15 = s.reg 15 ∧ out.pc = s.pc + 0xb4 := by
  simp (config := { decide := true }) [run, roundBody, Instruction.step, BitVec.add_assoc]

theorem expansion_frame (s : CPU) :
    let out := run expansionBody s
    out.reg 2 = s.reg 2 ∧ out.reg 15 = s.reg 15 ∧ out.pc = s.pc + 0x70 := by
  simp (config := { decide := true }) [run, expansionBody, Instruction.step, BitVec.add_assoc]

theorem input_word_frame (s : CPU) :
    let out := run inputWordBody s
    out.reg 2 = s.reg 2 ∧ out.reg 12 = s.reg 12 ∧
      out.reg 15 = s.reg 15 ∧ out.pc = s.pc + 0x34 := by
  simp (config := { decide := true }) [run, inputWordBody, Instruction.step, BitVec.add_assoc]

end Crypto.RISCV64
