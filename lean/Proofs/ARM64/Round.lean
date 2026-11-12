import Models.ARM64Round
import spec.Functions

namespace Crypto.ARM64.Round

/-- The assembly uses disjoint OR terms for Ch; FIPS writes XOR. -/
theorem ch_or_eq_xor (x y z : Word) :
    (x &&& y) ||| (z &&& ~~~x) = (x &&& y) ^^^ ((~~~x) &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> simp

/-- The factored majority expression in the assembly has the FIPS meaning. -/
theorem maj_factored (x y z : Word) :
    ((x ||| y) &&& z) ||| (x &&& y) =
      (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

/-- ROR Wd,Wn,#n is the EXTR alias with equal source registers. -/
theorem extr_same (x : Word) (n : Nat) (hn : n < 32) :
    (((x ++ x) >>> n).truncate 32) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_rotateRight_of_lt hn, hi, decide_true, Bool.true_and]
  by_cases h : i < 32 - n
  · simp [h, show n + i < 32 by omega]
  · simp [h, show ¬n + i < 32 by omega, show n + i - 32 = i - (32 - n) by omega]

theorem narrow_shift (x : Word) (n : Nat) :
    ((x.zeroExtend 64) >>> n).truncate 32 = x >>> n := by
  change (x.setWidth 64 >>> n).setWidth 32 = x >>> n
  calc
    (x.setWidth 64 >>> n).setWidth 32 = ((x >>> n).setWidth 64).setWidth 32 := by
      rw [BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]
    _ = (x >>> n).setWidth 32 := BitVec.setWidth_setWidth_of_le _ (by decide)
    _ = x >>> n := rfl

def fipsRound (s : Vector Word 8) (k w : Word) : Vector Word 8 :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let t1 := h + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g + k + w
  let t2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

theorem code_length : code.length = 30 := by decide

set_option maxHeartbeats 2000000 in
/-- Functional result of the 30 recorded instruction words, under this local
restricted ISA model. Loop execution, entry/exit, permissions and confidentiality
are not consequences of this fragment theorem. -/
theorem round_computes (s : State) :
    (runWords code s).map working =
      some (fipsRound (working s)
        (read32 s.memory (readBase s 0 + (readX s 5 <<< 2)))
        (read32 s.memory (s.sp + (readX s 5 <<< 2)))) := by
  simp [code, imageWords, runWords, stepWord, field, readW, readX, writeW,
    readBase, working, shifted, fipsRound, BitVec.truncate_eq_setWidth,
    extr_same, SHS.SHA256.bigSigma0, SHS.SHA256.bigSigma1,
    SHS.SHA256.Ch, SHS.SHA256.Maj, SHS.ROTR,
    BitVec.add_assoc]
  simp (config := { decide := true }) [ ch_or_eq_xor, maj_factored, BitVec.add_assoc,
    BitVec.rotateRight_def, narrow_shift,
    BitVec.xor_assoc]

set_option maxHeartbeats 2000000 in
/-- This fragment preserves memory and SP, advances PC by 120 bytes, and reads
only the two four-byte words at the public base/index addresses. -/
theorem round_observations (s : State) :
    (runWords code s).map (fun out => (out.memory, out.sp, out.pc, out.reads)) =
      some (s.memory, s.sp, s.pc + 120,
        s.reads ++
          [readBase s 0 + (readX s 5 <<< 2),
           readBase s 0 + (readX s 5 <<< 2) + 1,
           readBase s 0 + (readX s 5 <<< 2) + 2,
           readBase s 0 + (readX s 5 <<< 2) + 3,
           s.sp + (readX s 5 <<< 2), s.sp + (readX s 5 <<< 2) + 1,
           s.sp + (readX s 5 <<< 2) + 2, s.sp + (readX s 5 <<< 2) + 3]) := by
  simp [code, imageWords, runWords, stepWord, field, readW, readX, writeW,
    readBase, BitVec.add_assoc, List.append_assoc]
  simp (config := { decide := true })

end Crypto.ARM64.Round
