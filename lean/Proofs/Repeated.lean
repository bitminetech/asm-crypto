import Reference.SHA256Blocks
import Proofs.Reference

namespace Crypto.Reference
open EthLib.Cryptography.Hash.Sha256

theorem repeatedBytes_get (content : ByteArray) (size index : Nat) (h : index < size) :
    (repeatedBytes content size).get! index = content[index % content.size]! := by
  simp [repeatedBytes, ByteArray.get!, h]

private theorem repeat_get (content : ByteArray) (size index : Nat) (h : index < size) :
    (repeatedBytes content size)[index]! = content[index % content.size]! := by
  rw [getElem!_pos (repeatedBytes content size) index (by simpa using h)]
  simp only [ByteArray.getElem_eq_getElem_data, repeatedBytes, Array.getElem_ofFn]

theorem repeated_block_byte (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (i : Fin (size / 64)) (j : Fin 64) :
    (repeatedBytes content size)[i.val * 64 + j.val]! = content[j.val % content.size]! := by
  rw [repeat_get _ _ _ (by have := i.isLt; have := j.isLt; omega)]
  congr 1
  simp [Nat.add_mod, Nat.mul_mod, period]

private theorem pad_aligned (content : ByteArray) (size : Nat) (aligned : size % 64 = 0) :
    pad (repeatedBytes content size) = repeatedBytes content size ++ alignedPadding size := by
  apply ByteArray.ext
  have zeros : EthLib.Cryptography.Hash.Padding.paddingZeros size = 55 := by
    unfold EthLib.Cryptography.Hash.Padding.paddingZeros
    omega
  simp only [pad, EthLib.Cryptography.Hash.Padding.pad, alignedPadding, repeatedBytes_size,
    ByteArray.data_append, ByteArray.data_push, zeros, Array.push_eq_append, Array.append_assoc]

attribute [local irreducible] Spec.inputWord Spec.inputWords

private theorem inputWords_congr (a b : ByteArray) (start : Nat)
    (bytes : ∀ i : Fin 64, a[start + i.val]! = b[i.val]!) :
    Spec.inputWords a start = Spec.inputWords b 0 := by
  have word (i : Fin 16) : Spec.inputWord a (start + 4*i.val) = Spec.inputWord b (4*i.val) := by
    have byte (j : Nat) (hj : j < 64) : a[start+j]! = b[j]! := bytes ⟨j,hj⟩
    have hi := i.isLt
    simp only [Spec.inputWord, Nat.add_assoc start, byte (4*i.val) (by omega),
      byte (4*i.val+1) (by omega), byte (4*i.val+2) (by omega), byte (4*i.val+3) (by omega)]
  apply Vector.ext
  intro i hi
  simpa only [Spec.inputWords, Vector.getElem_ofFn, Nat.zero_add] using word ⟨i,hi⟩

theorem repeated_block_words (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (i : Fin (size / 64)) :
    Spec.inputWords (pad (repeatedBytes content size)) (i.val * 64) =
      Spec.inputWords (repeatedBytes content 64) 0 := by
  rw [pad_aligned content size aligned]
  apply inputWords_congr
  intro j
  have inside : i.val * 64 + j.val < size := by have := i.isLt; have := j.isLt; omega
  have whole : i.val * 64 + j.val < (repeatedBytes content size ++ alignedPadding size).size := by
    simp only [ByteArray.size_append, repeatedBytes_size, alignedPadding_size]; omega
  have msg : i.val * 64 + j.val < (repeatedBytes content size).size := by simpa using inside
  rw [getElem!_pos (repeatedBytes content size ++ alignedPadding size) _ whole, ByteArray.getElem_append_left msg,
    ← getElem!_pos (repeatedBytes content size) _ msg,
    repeated_block_byte content size period aligned i j, repeat_get _ _ _ j.isLt]

private theorem last_block_words (content : ByteArray) (size : Nat) (aligned : size % 64 = 0) :
    Spec.inputWords (pad (repeatedBytes content size)) size = Spec.inputWords (alignedPadding size) 0 := by
  rw [pad_aligned content size aligned]
  apply inputWords_congr
  intro j
  have inside : j.val < (alignedPadding size).size := by simpa only [alignedPadding_size] using j.isLt
  have whole : size + j.val < (repeatedBytes content size ++ alignedPadding size).size := by
    simp only [ByteArray.size_append, repeatedBytes_size, alignedPadding_size]
    have := j.isLt
    omega
  rw [getElem!_pos (repeatedBytes content size ++ alignedPadding size) _ whole, ByteArray.getElem_append_right (by simp),
    getElem!_pos (alignedPadding size) _ inside]
  simp only [repeatedBytes_size, Nat.add_sub_cancel_left]

private theorem repeatCompression_correct (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0) (blocks : Nat)
    (whole : blocks ≤ size / 64) :
    interpret (repeatCompression content blocks) =
      Spec.blocks (pad (repeatedBytes content size)) Spec.initial blocks := by
  induction blocks with
  | zero =>
    rw [repeatCompression, Fin.foldl_zero, Spec.blocks]
    decide +kernel
  | succ n ih =>
    have next : repeatCompression content (n+1) =
      compress (repeatCompression content n) (repeatedBytes content 64) 0 (by simp [BLOCK_SIZE_BYTES]) := by
      simp only [repeatCompression, Fin.foldl_succ_last]
    rw [next, compress_toState, ih (by omega), Spec.blocks, Nat.mul_comm 64 n]
    rw [repeated_block_words content size period aligned ⟨n, by omega⟩]

/-- The bounded-memory evaluator returns the pinned EthLib digest. -/
theorem repeatedAlignedDigest_eq_reference (content : ByteArray) (size : Nat)
    (period : 64 % content.size = 0) (aligned : size % 64 = 0)
    (lengthBound : size < 2 ^ 61) :
    repeatedAlignedDigest content size = Crypto.Reference.digest (repeatedBytes content size) := by
  have admitted : (repeatedBytes content size).size < 2^61 := by simpa using lengthBound
  have count : (pad (repeatedBytes content size)).size / 64 = size / 64 + 1 := by
    rw [pad_aligned content size aligned, ByteArray.size_append, repeatedBytes_size, alignedPadding_size]
    omega
  have index : 64 * (size / 64) = size := by omega
  apply Vector.toArray_inj.mp
  unfold repeatedAlignedDigest emitDigest Crypto.Reference.digest
  rw [if_neg (Nat.not_le.mpr admitted)]
  have eth := congrArg ByteArray.data (hash32_eq_spec (repeatedBytes content size) admitted)
  change (hash32 (repeatedBytes content size)).toArray = (Spec.hash (repeatedBytes content size)).data at eth
  change (EthLib.Cryptography.Hash.Sha256.digest
    (compress (repeatCompression content (size / 64)) (alignedPadding size) 0 _)).data = _
  rw [eth, digest_eq_spec, compress_toState, repeatCompression_correct content size period aligned _ (Nat.le_refl _),
    Spec.hash, ← pad_eq_spec _ admitted, count, Spec.blocks, index, last_block_words content size aligned]

end Crypto.Reference
