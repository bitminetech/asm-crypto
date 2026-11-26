import Proofs.RISCV64.PaddingSuffix
import Proofs.RISCV64.EntryMemory
import Proofs.ARM64.ImportedPaddingReference

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (lengthOffset lengthOffset_bounds address_delta region_store_delta
  cells_write8_outside write64_cells_outside read8_write8 write64_byte rev64_byte
  read8_write64_outside_ne byte128_address_inj)
open SHS.Equiv.SHA256.Padding.Layout (implPaddedBytes)

private theorem writeLength_eq (m : Memory) (dst nBits : Addr) :
    writeLength m dst nBits = m.write64 dst (Arm64.rev64 nBits) := by
  have byte (i : Fin 8) := rev64_byte nBits i
  have b0 := byte ⟨0, by decide⟩
  have b1 := byte ⟨1, by decide⟩
  have b2 := byte ⟨2, by decide⟩
  have b3 := byte ⟨3, by decide⟩
  have b4 := byte ⟨4, by decide⟩
  have b5 := byte ⟨5, by decide⟩
  have b6 := byte ⟨6, by decide⟩
  have b7 := byte ⟨7, by decide⟩
  simp only [Nat.reduceMul, Nat.reduceSub] at b0 b1 b2 b3 b4 b5 b6 b7
  simp [writeLength, List.range_succ, Arm64.Memory.write64, b0, b1, b2, b3, b4, b5, b6, b7]

theorem marker_frame (m : Memory) (dst : Addr) (rem : Nat) (hr : rem < 128) :
    CellFrame (m.write8 (dst + BitVec.ofNat 64 rem) 128) m dst 128 := by
  intro p hp
  apply cells_write8_outside
  intro hit
  rw [hit, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hp
  omega

theorem length_frame (m : Memory) (dst nBits : Addr) (rem : Nat) (hr : rem < 64) :
    CellFrame (writeLength m (dst + BitVec.ofNat 64 (lengthOffset rem)) nBits) m dst 128 := by
  rw [writeLength_eq]
  intro p hp
  apply write64_cells_outside
  exact region_store_delta dst p _ 128 8 (lengthOffset_bounds rem hr).2 hp

/-- The tail copy and the two suffix stores implement the FIPS padding bytes
given the original message view and the zeroed part of the workspace. -/
theorem padding_bytes (m : Memory) (dst : Addr) (data : ByteArray)
    (countBound : data.size < 2^61)
    (copiedBytes : ∀ i : Fin (data.size % 64), m.read8 (dst + BitVec.ofNat 64 i.val) =
      (data.get! (data.size / 64 * 64 + i.val)).toBitVec)
    (zero : ∀ i : Fin 128, data.size % 64 ≤ i.val → m.read8 (dst + BitVec.ofNat 64 i.val) = 0)
    (i : Fin (lengthOffset (data.size % 64) + 8)) :
    let rem := data.size % 64
    let marked := m.write8 (dst + BitVec.ofNat 64 rem) 128
    let final := writeLength marked (dst + BitVec.ofNat 64 (lengthOffset rem))
      (BitVec.ofNat 64 data.size <<< (3 : Nat))
    final.read8 (dst + BitVec.ofNat 64 i.val) =
      ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec := by
  dsimp only
  let rem := data.size % 64
  let start := lengthOffset rem
  let bits : Addr := BitVec.ofNat 64 data.size <<< (3 : Nat)
  let mark := m.write8 (dst + BitVec.ofNat 64 rem) 128
  have rb : rem < 64 := Nat.mod_lt _ (by decide)
  have limits := lengthOffset_bounds rem rb
  have ib : i.val < start + 8 := i.isLt
  have full : data.size / 64 * 64 + rem = data.size := by dsimp [rem]; omega
  have lenStart : data.size + 1 + SHS.Equiv.SHA256.Padding.Layout.zerosCount data =
      data.size / 64 * 64 + start := Crypto.ARM64.Imported.padded_tail_length_start data
  have total : data.size / 64 * 64 + i.val < (implPaddedBytes data).size := by
    rw [Crypto.ARM64.Imported.padded_tail_size]
    change _ < data.size / 64 * 64 + start + 8
    omega
  rw [SHS.Equiv.SHA256.Padding.Layout.get!_implPaddedBytes_eq data _ total]
  change (writeLength mark (dst + BitVec.ofNat 64 start) bits).read8 _ = _
  rw [writeLength_eq]
  by_cases digit : start ≤ i.val
  · let k : Fin 8 := ⟨i.val - start, by omega⟩
    have addr : dst + BitVec.ofNat 64 i.val =
        dst + BitVec.ofNat 64 start + BitVec.ofNat 64 k.val := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      dsimp [k]
      omega
    have before : ¬data.size / 64 * 64 + i.val < data.size := by omega
    have beyond : data.size / 64 * 64 + i.val ≠ data.size := by omega
    have zeroEnd : ¬data.size / 64 * 64 + i.val <
        data.size + 1 + SHS.Equiv.SHA256.Padding.Layout.zerosCount data := by omega
    have index : data.size / 64 * 64 + i.val -
        (data.size + 1 + SHS.Equiv.SHA256.Padding.Layout.zerosCount data) = k.val := by dsimp [k]; omega
    rw [addr, write64_byte, rev64_byte, if_neg before, if_neg beyond, if_neg zeroEnd, index]
    have same := Crypto.ARM64.Imported.count_length_bits (BitVec.ofNat 64 data.size)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : data.size < 2^64)] at same
    rw [← same]
    exact (Crypto.ARM64.Imported.reference_length_byte _ k).symm
  · have outside (k : Fin 8) : dst + BitVec.ofNat 64 i.val ≠
        dst + BitVec.ofNat 64 start + BitVec.ofNat 64 k.val := by
      intro eq
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at eq
      have same := (byte128_address_inj dst ⟨i.val, by omega⟩
        ⟨start + k.val, by have := k.isLt; omega⟩).mp eq
      change i.val = start + k.val at same
      omega
    rw [read8_write64_outside_ne _ _ _ _ outside]
    unfold mark
    rw [read8_write8]
    have idem : (dst + BitVec.ofNat 64 i.val = dst + BitVec.ofNat 64 rem) ↔ i.val = rem :=
      byte128_address_inj dst ⟨i.val, by omega⟩ ⟨rem, by omega⟩
    simp only [idem]
    by_cases copied : i.val < rem
    · rw [if_neg (by omega : i.val ≠ rem), if_pos (by omega : data.size / 64 * 64 + i.val < data.size)]
      exact copiedBytes ⟨i.val,copied⟩
    · have le : rem ≤ i.val := by omega
      rw [if_neg (by omega : ¬data.size / 64 * 64 + i.val < data.size)]
      by_cases atMarker : i.val = rem
      · rw [if_pos atMarker, if_pos (by omega : data.size / 64 * 64 + i.val = data.size)]
        rfl
      · rw [if_neg atMarker, if_neg (by omega : data.size / 64 * 64 + i.val ≠ data.size),
          if_pos (by omega : data.size / 64 * 64 + i.val <
            data.size + 1 + SHS.Equiv.SHA256.Padding.Layout.zerosCount data)]
        exact zero ⟨i.val, by omega⟩ le

end Crypto.RISCV64
