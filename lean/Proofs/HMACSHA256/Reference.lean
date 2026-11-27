import Reference.HMACSHA256

/-! Portable layout and digest lemmas for composing the two HMAC helpers
with calls to the existing SHA-256 reference. -/
namespace Crypto.Reference

open EthLib.Cryptography.Hash

theorem sha256_digest_eq_ethlib (input : ByteList)
    (admitted : input.bytes.size < 2 ^ 61) :
    (sha256 input).2 = Sha256.hash32 input.bytes := by
  simp only [sha256, digest, if_neg (Nat.not_le.mpr admitted)]

theorem sha256_bytes_eq_ethlib (input : ByteList) (admitted : input.bytes.size < 2 ^ 61) :
    EthLib.Base.packBytes (sha256 input).2 = Sha256.hash input.bytes := by
  rw [sha256_digest_eq_ethlib input admitted, Sha256.packBytes_hash32]

@[simp] theorem pack_hmacKey (key : ByteList) :
    EthLib.Base.packBytes (hmacKey key) = Hmac.blockKey key.bytes := by
  apply ByteArray.ext
  rfl

/-- On the copy path the helper's key prefix is already the input key. -/
theorem hmacKey_short (key : ByteList) (short : key.bytes.size ≤ 64) :
    EthLib.Base.packBytes (hmacKey key) =
      key.bytes ++ ⟨Array.replicate (64 - key.bytes.size) 0⟩ := by
  rw [pack_hmacKey]
  exact Hmac.blockKey_of_le short

/-- The long-key path can use the digest returned by the checked SHA-256 call. -/
theorem hmacKey_long (key : ByteList) (long : 64 < key.bytes.size)
    (admitted : key.bytes.size < 2 ^ 61) :
    EthLib.Base.packBytes (hmacKey key) =
      EthLib.Base.packBytes (sha256 key).2 ++ ⟨Array.replicate 32 0⟩ := by
  rw [pack_hmacKey, sha256_bytes_eq_ethlib key admitted]
  exact Hmac.blockKey_of_lt long

private theorem zeroPaddedByte (prefixBytes : ByteArray) (zeros i : Nat)
    (valid : i < prefixBytes.size + zeros) :
    (prefixBytes ++ ⟨Array.replicate zeros 0⟩)[i]! =
      if i < prefixBytes.size then prefixBytes[i]! else 0 := by
  have getData (a : ByteArray) (j : Nat) : a[j]! = a.data[j]! := by
    have h : a.size = a.data.size := rfl
    by_cases inside : j < a.size
    · rw [getElem!_pos a j inside, getElem!_pos a.data j (h ▸ inside)] <;> rfl
    · rw [getElem!_neg a j inside, getElem!_neg a.data j (h ▸ inside)] <;> rfl
  rw [getData (prefixBytes ++ ⟨Array.replicate zeros 0⟩) i, ByteArray.data_append]
  simp only [ByteArray.size]
  have whole : i < (prefixBytes.data ++ Array.replicate zeros (0 : UInt8)).size := by
    rw [Array.size_append, Array.size_replicate, ByteArray.size_data]
    exact valid
  rw [getElem!_pos (prefixBytes.data ++ Array.replicate zeros 0) i whole]
  by_cases inside : i < prefixBytes.data.size
  · rw [if_pos inside, Array.getElem_append_left inside]
    exact (getElem!_pos prefixBytes.data i inside).symm.trans (getData prefixBytes i).symm
  · rw [if_neg inside, Array.getElem_append_right (Nat.le_of_not_gt inside)]
    simp

theorem hmacKey_short_byte (key : ByteList) (short : key.bytes.size ≤ 64) (i : Fin 64) :
    (EthLib.Base.packBytes (hmacKey key))[i.val]! =
      if i.val < key.bytes.size then key.bytes[i.val]! else 0 := by
  rw [hmacKey_short key short, zeroPaddedByte]
  exact Nat.lt_of_lt_of_le i.isLt (by omega)

theorem hmacKey_long_byte (key : ByteList) (long : 64 < key.bytes.size)
    (admitted : key.bytes.size < 2 ^ 61) (i : Fin 64) :
    (EthLib.Base.packBytes (hmacKey key))[i.val]! =
      if i.val < 32 then (EthLib.Base.packBytes (sha256 key).2)[i.val]! else 0 := by
  have size : (EthLib.Base.packBytes (sha256 key).2).size = 32 := (sha256 key).2.size_toArray
  rw [hmacKey_long key long admitted, zeroPaddedByte]
  · rw [size]
  · rw [size]
    exact i.isLt

private theorem packedSize {n : Nat} (bytes : Vector UInt8 n) :
    (EthLib.Base.packBytes bytes).size = n := bytes.size_toArray

@[simp] theorem hmacInner_length (message : ByteList) (k0 : HmacKeyBlock) (scratchSize : Nat) :
    (hmacInner message k0 scratchSize).bytes.size = 64 + message.bytes.size := by
  simp only [hmacInner, ByteArray.size_append, Hmac.xorPad_size, packedSize]

@[simp] theorem hmacOuter_length (k0 : HmacKeyBlock) (innerDigest : Digest) :
    (hmacOuter k0 innerDigest).bytes.size = 96 := by
  simp only [hmacOuter, ByteArray.size_append, Hmac.xorPad_size, packedSize]

theorem hmacInner_layout (message : ByteList) (k0 : HmacKeyBlock) (scratchSize : Nat)
    (room : hmacScratchRequired message ≤ scratchSize) :
    (hmacInner message k0 scratchSize).WellFormed := by
  refine ⟨by change 24 ≤ 24; decide, by change 24 % 8 = 0; decide, ?_, ?_⟩
  · change 24 ≤ scratchSize - 8
    unfold hmacScratchRequired at room
    omega
  · simp only [hmacInner_length]
    change 64 + message.bytes.size ≤ scratchSize - 8 - 24
    unfold hmacScratchRequired at room
    omega

theorem hmacOuter_layout (k0 : HmacKeyBlock) (innerDigest : Digest) :
    (hmacOuter k0 innerDigest).WellFormed := by
  unfold ByteList.WellFormed
  rw [hmacOuter_length]
  change 24 ≤ 24 ∧ 24 % 8 = 0 ∧ 24 ≤ 120 ∧ 96 ≤ 120 - 24
  decide

/-- The helper should pass this length condition to the inner SHA-256 call. -/
theorem hmacInner_sha256_length (message : ByteList) (k0 : HmacKeyBlock) (scratchSize : Nat)
    (admitted : message.bytes.size < 2 ^ 61 - 64) :
    (hmacInner message k0 scratchSize).bytes.size < 2 ^ 61 := by
  rw [hmacInner_length]
  omega

/-- An independently established accessible extent gives the SHA-256
length bound for a well-formed list, even with arbitrary room and offset. -/
theorem sha256_length_of_extent (list : ByteList) (extent : Nat)
    (wellFormed : list.WellFormed) (fits : list.size ≤ extent) (extentBound : extent ≤ 2 ^ 61) :
    list.bytes.size < 2 ^ 61 := by
  obtain ⟨offsetMin, _, offsetBound, lengthBound⟩ := wellFormed
  omega

/-- On the successful path, scratch capacity also bounds the length of the
internal SHA-256 input, including its 64-byte prefix. -/
theorem hmacInner_length_of_extent (message : ByteList) (scratchSize extent : Nat)
    (room : hmacScratchRequired message ≤ scratchSize)
    (fits : scratchSize ≤ extent) (extentBound : extent ≤ 2 ^ 61) :
    message.bytes.size < 2 ^ 61 - 64 := by
  unfold hmacScratchRequired at room
  omega

/-- Portable composition of the two SHA-256 calls in the finishing helper. -/
theorem hmacFinish_calls (inner : ByteList) (k0 : HmacKeyBlock)
    (admitted : inner.bytes.size < 2 ^ 61) :
    hmacFinish inner k0 = (sha256 (hmacOuter k0 (sha256 inner).2)).2 := by
  have outerBound : (hmacOuter k0 (sha256 inner).2).bytes.size < 2 ^ 61 := by
    rw [hmacOuter_length]
    decide
  rw [sha256_digest_eq_ethlib _ outerBound]
  simp only [hmacFinish, hmacOuter, sha256_bytes_eq_ethlib inner admitted]

theorem hmacFinish_hmacInner (key message : ByteList) (scratchSize : Nat) :
    hmacFinish (hmacInner message (hmacKey key) scratchSize) (hmacKey key) =
      Hmac.hmac32 key.bytes message.bytes := by
  apply Vector.toArray_inj.mp
  simp only [hmacFinish, hmacInner, pack_hmacKey]
  rfl

theorem hmacSha256_success (key message : ByteList) (scratchSize : Nat)
    (room : hmacScratchRequired message ≤ scratchSize)
    (admitted : message.bytes.size < 2 ^ 61 - 64) :
    let inner := hmacInner message (hmacKey key) scratchSize
    let outer := hmacOuter (hmacKey key) (sha256 inner).2
    hmacSha256 key message scratchSize = .ok (sha256 outer).2 inner := by
  dsimp only
  rw [hmacSha256, if_neg (Nat.not_lt.mpr room), ← hmacFinish_hmacInner key message scratchSize,
    hmacFinish_calls _ _ (hmacInner_sha256_length _ _ _ admitted)]

theorem hmacSha256_insufficient (key message : ByteList) (scratchSize : Nat)
    (short : scratchSize < hmacScratchRequired message) :
    hmacSha256 key message scratchSize = .bufferTooSmall := by
  rw [hmacSha256, if_pos short]

end Crypto.Reference
