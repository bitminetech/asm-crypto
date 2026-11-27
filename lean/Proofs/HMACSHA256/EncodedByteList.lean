import Proofs.HMACSHA256.Reference
import Proofs.HMACSHA256.ARM64Memory
import Proofs.ARM64.ImportedCallerEntry

namespace Crypto.HMACSHA256

open Crypto.Reference EthLib.Cryptography.Hash

/-- The byte interpretation shared by the HMAC stages and the SHA-256
entry predicates. The accessible extent and its permissions are supplied
separately by the caller. -/
structure EncodedByteList (m : Arm64.Memory) (base : BitVec 64) (value : Crypto.Reference.ByteList) : Prop where
  size : m.read64 base = BitVec.ofNat 64 value.size
  offset : m.read64 (base + 8#64) = BitVec.ofNat 64 value.offset
  count : m.read64 (base + 16#64) = BitVec.ofNat 64 value.bytes.size
  bytes : ∀ i : Fin value.bytes.size,
    m.read8 (base + BitVec.ofNat 64 (value.offset + i.val)) = value.bytes[i.val]!.toBitVec

theorem EncodedByteList.preserved {before after : Arm64.Memory} {base : BitVec 64}
    {value : ByteList} {extent : Nat} (encoded : EncodedByteList before base value)
    (layout : value.WellFormed) (accessible : value.size ≤ extent)
    (valid : (⟨base, extent⟩ : Crypto.Baseline.Region).Valid)
    (cells : ∀ p, (⟨base, extent⟩ : Crypto.Baseline.Region).Contains p →
      after.cells p = before.cells p) :
    EncodedByteList after base value := by
  let region : Crypto.Baseline.Region := ⟨base, extent⟩
  obtain ⟨header, _, offset, payload⟩ := layout
  have fixed (off : Nat) (fits : off < extent) :
      after.cells (base + BitVec.ofNat 64 off) = before.cells (base + BitVec.ofNat 64 off) :=
    cells _ (Crypto.ARM64.Imported.caller_region_contains_offset region valid off fits)
  have word (off : Nat) (fits : off + 8 ≤ extent) :
      after.read64 (base + BitVec.ofNat 64 off) = before.read64 (base + BitVec.ofNat 64 off) := by
    apply Crypto.HMACSHA256.ARM64.read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact fixed _ (by have := i.isLt; omega)
  refine ⟨?_, (word 8 (by omega)).trans encoded.offset,
    (word 16 (by omega)).trans encoded.count, ?_⟩
  · have same := word 0 (by omega)
    change after.read64 (base + 0#64) = before.read64 (base + 0#64) at same
    rw [BitVec.add_zero] at same
    exact same.trans encoded.size
  · intro i
    unfold Arm64.Memory.read8
    rw [fixed (value.offset + i.val) (by have := i.isLt; omega)]
    exact encoded.bytes i

theorem copy_offset_distance (p base : BitVec 64) (off : Nat) (within : off ≤ (p - base).toNat) :
    (p - (base + BitVec.ofNat 64 off)).toNat = (p - base).toNat - off := by
  have eq : p - (base + BitVec.ofNat 64 off) = (p - base) - BitVec.ofNat 64 off := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]
    ac_rfl
  have small : off < 2 ^ 64 := by have := (p - base).isLt; omega
  rw [eq, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have distBound := (p - base).isLt
  omega

theorem outside_span_of_offset (base : BitVec 64) (off start size : Nat)
    (away : off < start ∨ start + size ≤ off)
    (validStart : start + size < 2 ^ 64) (validOff : off < 2 ^ 64) :
    size ≤ (base + BitVec.ofNat 64 off - (base + BitVec.ofNat 64 start)).toNat := by
  rw [Crypto.ARM64.Imported.bv_add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt validOff, Nat.mod_eq_of_lt (by omega : start < 2 ^ 64)]
  rcases away with earlier | later <;> omega

theorem opad_lane (i : Nat) :
    (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * (i % 8)) 8 = Hmac.OPAD.toBitVec := by
  have lanes : ∀ j : Fin 8, (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * j.val) 8 =
      Hmac.OPAD.toBitVec := by decide +kernel
  exact lanes ⟨i % 8, Nat.mod_lt _ (by decide)⟩

private theorem appended_bytes (m : Arm64.Memory) (base : BitVec 64) (left right : ByteArray)
    (leftAt : ∀ i : Fin left.size, m.read8 (base + BitVec.ofNat 64 i.val) = left[i.val]!.toBitVec)
    (rightAt : ∀ i : Fin right.size,
      m.read8 (base + BitVec.ofNat 64 left.size + BitVec.ofNat 64 i.val) = right[i.val]!.toBitVec)
    (i : Fin (left ++ right).size) :
    m.read8 (base + BitVec.ofNat 64 i.val) = (left ++ right)[i.val]!.toBitVec := by
  have inside : i.val < left.size + right.size := by simpa only [ByteArray.size_append] using i.isLt
  rw [getElem!_pos (left ++ right) i.val i.isLt]
  by_cases first : i.val < left.size
  · rw [ByteArray.getElem_append_left first]
    simpa only [getElem!_pos left i.val first] using leftAt ⟨i.val, first⟩
  · have second : left.size ≤ i.val := by omega
    rw [ByteArray.getElem_append_right second]
    let j : Fin right.size := ⟨i.val - left.size, by omega⟩
    have index : left.size + j.val = i.val := by dsimp [j]; omega
    have read := rightAt j
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, index, getElem!_pos right j.val j.isLt] at read
    exact read

theorem encoded_hmac_outer (m : Arm64.Memory) (base : BitVec 64) (k0 : HmacKeyBlock)
    (inner : Digest)
    (size : m.read64 base = 120#64)
    (offset : m.read64 (base + 8#64) = 24#64)
    (count : m.read64 (base + 16#64) = 96#64)
    (bytePad : ∀ i : Fin 64, m.read8 (base + 24#64 + BitVec.ofNat 64 i.val) =
      (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD)[i.val]!.toBitVec)
    (byteInner : ∀ i : Fin 32, m.read8 (base + 88#64 + BitVec.ofNat 64 i.val) = inner[i.val].toBitVec) :
    EncodedByteList m base (hmacOuter k0 inner) := by
  have byteCount : BitVec.ofNat 64 (hmacOuter k0 inner).bytes.size = 96#64 :=
    congrArg (BitVec.ofNat 64) (hmacOuter_length k0 inner)
  refine ⟨size, offset, count.trans byteCount.symm, ?_⟩
  intro i
  let pad := Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD
  let dig := EthLib.Base.packBytes inner
  have padSize : pad.size = 64 := by
    change (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD).size = 64
    rw [Hmac.xorPad_size]
    exact k0.size_toArray
  change m.read8 (base + BitVec.ofNat 64 (24 + i.val)) = (pad ++ dig)[i.val]!.toBitVec
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  refine appended_bytes m (base + 24#64) pad dig ?_ ?_ i
  · intro j
    exact bytePad ⟨j.val, by rw [← padSize]; exact j.isLt⟩
  · intro j
    have within : j.val < 32 := by simpa only [show dig.size = 32 from inner.size_toArray] using j.isLt
    rw [padSize, BitVec.add_assoc base]
    rw [getElem!_pos dig _ j.isLt]
    exact byteInner ⟨j.val, within⟩

theorem encoded_hmac_inner (m : Arm64.Memory) (base : BitVec 64) (message : ByteList)
    (k0 : HmacKeyBlock) (capacity : Nat)
    (size : m.read64 base = BitVec.ofNat 64 (capacity - 8))
    (offset : m.read64 (base + 8#64) = 24#64)
    (count : m.read64 (base + 16#64) = BitVec.ofNat 64 (64 + message.bytes.size))
    (bytePad : ∀ i : Fin 64, m.read8 (base + 24#64 + BitVec.ofNat 64 i.val) =
      (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD)[i.val]!.toBitVec)
    (messageAt : ∀ i : Fin message.bytes.size,
      m.read8 (base + 88#64 + BitVec.ofNat 64 i.val) = message.bytes[i.val]!.toBitVec) :
    EncodedByteList m base (hmacInner message k0 capacity) := by
  have byteCount := congrArg (BitVec.ofNat 64) (hmacInner_length message k0 capacity)
  refine ⟨size, offset, count.trans byteCount.symm, ?_⟩
  intro i
  let pad := Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD
  have padSize : pad.size = 64 := by
    change (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD).size = 64
    rw [Hmac.xorPad_size]
    exact k0.size_toArray
  change m.read8 (base + BitVec.ofNat 64 (24 + i.val)) = (pad ++ message.bytes)[i.val]!.toBitVec
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  refine appended_bytes m (base + 24#64) pad message.bytes ?_ ?_ i
  · intro j
    exact bytePad ⟨j.val, by rw [← padSize]; exact j.isLt⟩
  · intro j
    rw [padSize, BitVec.add_assoc base]
    exact messageAt j

end Crypto.HMACSHA256
