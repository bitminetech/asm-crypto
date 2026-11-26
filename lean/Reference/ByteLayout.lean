import EthLib.Cryptography.Proofs.Hash.Sha256
import Mathlib.Tactic.IntervalCases

/-! Byte offsets used to compare the assembly's one or two tail blocks with EthLib padding. -/
namespace Crypto.Reference.ByteLayout

open EthLib.Cryptography.Hash.Sha256

abbrev implPaddedBytes := pad
abbrev zerosCount (data : ByteArray) := EthLib.Cryptography.Hash.Padding.paddingZeros data.size

theorem zerosCount_eq (data : ByteArray) : zerosCount data =
    if data.size % 64 < 56 then 55 - data.size % 64 else 119 - data.size % 64 := by
  unfold zerosCount EthLib.Cryptography.Hash.Padding.paddingZeros
  split <;> omega

def lengthBE64 (bits : UInt64) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 8 => ((bits >>> ((7 - i.val) * 8).toUInt64) &&& 0xff).toUInt8⟩

private theorem get_in_bounds (a : ByteArray) (i : Nat) (bound : i < a.size) :
    a.get! i = a.data[i]'(ByteArray.size_data ▸ bound) := by
  cases a with
  | mk data => exact getElem!_pos data i bound

theorem lengthBE64_get!_eq (bits : UInt64) (i : Nat) (bound : i < 8) :
    (lengthBE64 bits).get! i = ((bits >>> ((7 - i) * 8).toUInt64) &&& 0xff).toUInt8 := by
  have inside : i < (lengthBE64 bits).size := by simpa only [lengthBE64, ByteArray.size, Array.size_ofFn]
  rw [get_in_bounds _ i inside]
  simp only [lengthBE64, Array.getElem_ofFn]

private theorem length_agrees (size : Nat) : lengthBE64 (size.toUInt64 <<< 3) = lengthBytes size := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [lengthBE64, lengthBytes, Array.size_ofFn]
  · intro i left right
    have bound : i < 8 := by simpa only [lengthBE64, Array.size_ofFn] using left
    simp only [lengthBE64, lengthBytes, Array.getElem_ofFn]
    have amount : ((7-i)*8 : Nat).toUInt64 = 56 - 8 * UInt64.ofNat i := by
      interval_cases i <;> rfl
    have shift : size.toUInt64 <<< 3 = UInt64.ofNat size * 8 := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul, Nat.toUInt64_eq, UInt64.toNat_ofNat,
        Nat.shiftLeft_eq]
    rw [amount, shift]
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_and]
    change (_ &&& (2^8 - 1)) % 2^8 = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 8 := by
  simp only [pad, EthLib.Cryptography.Hash.Padding.pad,
    ByteArray.size, ByteArray.data_append, ByteArray.data_push, Array.size_append,
    Array.size_push, Array.size_replicate, lengthBytes, Array.size_ofFn, zerosCount]

private theorem pad_data (data : ByteArray) : (pad data).data =
    data.data.push 0x80 ++ Array.replicate (zerosCount data) 0 ++ (lengthBytes data.size).data := by
  simp only [pad, EthLib.Cryptography.Hash.Padding.pad, ByteArray.data_append,
    ByteArray.data_push, zerosCount]

private theorem get!_data (a : ByteArray) (i : Nat) : a.get! i = a.data[i]! := by cases a; rfl

private theorem append_get_left (left right : Array UInt8) (i : Nat) (h : i < left.size) :
    (left ++ right)[i]! = left[i]! := by
  have whole : i < (left ++ right).size := by rw [Array.size_append]; omega
  rw [getElem!_pos (left ++ right) i whole, getElem!_pos left i h, Array.getElem_append_left h]

private theorem append_get_right (left right : Array UInt8) (i : Nat)
    (h : left.size ≤ i) (whole : i < (left ++ right).size) :
    (left ++ right)[i]! = right[i - left.size]! := by
  have digit : i - left.size < right.size := by rw [Array.size_append] at whole; omega
  rw [getElem!_pos (left ++ right) i whole, getElem!_pos right _ digit, Array.getElem_append_right h]

theorem get!_implPaddedBytes_eq (data : ByteArray) (i : Nat) (bound : i < (implPaddedBytes data).size) :
    (implPaddedBytes data).get! i =
      if i < data.size then data.get! i else
      if i = data.size then 0x80 else
      if i < data.size + 1 + zerosCount data then 0 else
      (lengthBE64 (data.size.toUInt64 <<< 3)).get! (i - (data.size + 1 + zerosCount data)) := by
  rw [get!_data, pad_data]
  let payloadAndZeros := data.data.push (0x80 : UInt8) ++ Array.replicate (zerosCount data) 0
  have prefixSize : payloadAndZeros.size = data.size + 1 + zerosCount data := by
    simp only [payloadAndZeros, Array.size_append, Array.size_push, Array.size_replicate, ByteArray.size]
  have pushed : (data.data.push (0x80 : UInt8)).size = data.size + 1 := by rw [Array.size_push, ByteArray.size_data]
  change (payloadAndZeros ++ (lengthBytes data.size).data)[i]! = _
  by_cases beforeLength : i < data.size + 1 + zerosCount data
  · rw [append_get_left payloadAndZeros _ i (by rwa [prefixSize])]
    by_cases beforeZeros : i < data.size + 1
    · rw [append_get_left (data.data.push 0x80) _ i (by rwa [pushed])]
      by_cases input : i < data.size
      · rw [if_pos input, get!_data,
          getElem!_pos (data.data.push 0x80) i (by rw [pushed]; omega),
          getElem!_pos data.data i input, Array.getElem_push_lt input]
      · have marker : i = data.size := by omega
        subst i
        rw [if_neg (Nat.lt_irrefl _), if_pos rfl,
          getElem!_pos (data.data.push 0x80) _ (by rw [pushed]; omega)]
        exact Array.getElem_push_eq
    · rw [append_get_right (data.data.push 0x80) _ i (by rw [pushed]; omega)
          (show i < payloadAndZeros.size by rwa [prefixSize]),
        if_neg (by omega : ¬i < data.size), if_neg (by omega : i ≠ data.size), if_pos beforeLength]
      have index : i - (data.data.push (0x80 : UInt8)).size < (Array.replicate (zerosCount data) (0 : UInt8)).size := by
        rw [pushed, Array.size_replicate]
        omega
      rw [getElem!_pos (Array.replicate (zerosCount data) (0 : UInt8)) _ index, Array.getElem_replicate]
  · have whole : i < (payloadAndZeros ++ (lengthBytes data.size).data).size := by
      rw [Array.size_append, prefixSize]
      simp only [lengthBytes, Array.size_ofFn]
      rwa [size_implPaddedBytes_eq] at bound
    rw [append_get_right payloadAndZeros _ i (by rw [prefixSize]; omega) whole,
      if_neg (by omega : ¬i < data.size), if_neg (by omega : i ≠ data.size), if_neg beforeLength,
      ← length_agrees, prefixSize, get!_data]

def paddedBlock (data : ByteArray) (k : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun j => (implPaddedBytes data).get! (k * 64 + j.val)

theorem paddedBlock_complete (data : ByteArray) (k : Nat) (whole : k < data.size / 64) :
    paddedBlock data k = Vector.ofFn (fun j : Fin 64 => data.get! (k * 64 + j.val)) := by
  apply Vector.ext
  intro j hj
  have input : k * 64 + j < data.size := by omega
  have inside : k * 64 + j < (implPaddedBytes data).size := by rw [size_implPaddedBytes_eq]; omega
  simp only [paddedBlock, Vector.getElem_ofFn, get!_implPaddedBytes_eq _ _ inside, if_pos input]

end Crypto.Reference.ByteLayout
