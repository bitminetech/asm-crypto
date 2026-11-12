import Reference.SHA256Blocks
import Proofs.Reference

namespace Crypto.Reference

theorem repeatedBytes_size (content : ByteArray) (size : Nat) :
    (repeatedBytes content size).size = size := by
  change (Array.ofFn (fun i : Fin size => content[i.val % content.size]!)).size = size
  simp only [Array.size_ofFn]

theorem repeatedBytes_get (content : ByteArray) (size index : Nat) (h : index < size) :
    (repeatedBytes content size).get! index = content[index % content.size]! := by
  simp [repeatedBytes, ByteArray.get!, h]

theorem repeated_block_byte (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (i : Fin (size / 64)) (j : Fin 64) :
    (repeatedBytes content size).get! (i.val * 64 + j.val) = content[j.val % content.size]! := by
  rw [repeatedBytes_get _ _ _ (by have := i.isLt; have := j.isLt; omega)]
  congr 1
  simp [Nat.add_mod, Nat.mul_mod, period]

theorem repeated_block_words (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (i : Fin (size / 64)) :
    SHS.SHA256.Impl.toU32sFromBytes (repeatedBytes content size) (i.val * 64) =
      SHS.SHA256.Impl.toU32s
        (Vector.ofFn fun j : Fin 64 => content[j.val % content.size]!) := by
  apply Vector.ext
  intro j hj
  have getByte (k : Nat) (hk : k < 64) :
      (repeatedBytes content size).get! (i.val * 64 + k) = content[k % content.size]! :=
    repeated_block_byte content size period aligned i ⟨k, hk⟩
  have getZero := getByte 0 (by decide)
  simp only [Nat.add_zero, Nat.zero_mod] at getZero
  interval_cases j <;>
    simp [SHS.SHA256.Impl.toU32sFromBytes, SHS.SHA256.Impl.toU32s,
      SHS.SHA256.Impl.beU32FromBytes, SHS.SHA256.Impl.beU32, Nat.add_assoc, getByte, getZero]

set_option maxHeartbeats 2000000 in
/-- The test runner's repeated-block evaluator equals the unchanged imported
SHA-256 function for every supported repeated whole-block message. -/
theorem repeatedAlignedDigest_eq_reference (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (lengthBound : size < 2 ^ 61) :
    repeatedAlignedDigest content size = SHS.SHA256.Impl.sha256 (repeatedBytes content size) := by
  have hsize := repeatedBytes_size content size
  have loop :
      (fun state (i : Fin (size / 64)) =>
        SHS.SHA256.Impl.compress state
          (SHS.SHA256.Impl.toU32sFromBytes (repeatedBytes content size) (i.val * 64))) =
      (fun state (_ : Fin (size / 64)) =>
        SHS.SHA256.Impl.compress state
          (SHS.SHA256.Impl.toU32s (Vector.ofFn fun j : Fin 64 => content[j.val % content.size]!))) := by
    funext state i
    rw [repeated_block_words content size period aligned i]
  rw [SHS.SHA256.Impl.sha256, if_neg (show ¬2 ^ 61 ≤ (repeatedBytes content size).size by omega)]
  change emitDigest _ = emitDigest (SHS.SHA256.Impl.sha256State _ _)
  apply congrArg emitDigest
  simp only [SHS.SHA256.Impl.sha256State, hsize, aligned, Nat.not_lt_zero,
    if_false, show (0 : Nat) < 56 by decide, if_true]
  simp only [Fin.val_cast]
  rw [loop]
  rfl

end Crypto.Reference
