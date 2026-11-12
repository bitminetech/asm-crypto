import Models.ARM64Machine
import Mathlib.Tactic.IntervalCases

namespace Crypto.ARM64.Machine

open Round (Address Memory Word read32)

theorem storeLE_outside (m : Memory) (base p : Address) (size : Nat) (value : Address)
    (h : size ≤ (p - base).toNat) : storeLE m base size value p = m p := by
  simp only [storeLE, if_neg (show ¬ (p - base).toNat < size by omega)]

theorem storeLE_inside (m : Memory) (base p : Address) (size : Nat) (value : Address)
    (h : (p - base).toNat < size) :
    storeLE m base size value p = byteAt value (p - base).toNat := by
  simp only [storeLE, if_pos h]

theorem addresses_length (base : Address) (size : Nat) : (addresses base size).length = size := by
  simp [addresses]

theorem read32_loadLE (m : Memory) (base : Address) :
    (loadLE m base 4).truncate 32 = read32 m base := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [loadLE, read32, List.range_succ, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
      BitVec.truncate_eq_setWidth]
  all_goals simp (config := { decide := true })

theorem add_offset_sub (base offset : Address) : base + offset - base = offset := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem read32_storeLE (m : Memory) (base : Address) (value : Address) :
    read32 (storeLE m base 4 value) base = value.truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [read32, storeLE, byteAt, add_offset_sub, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth]
  all_goals simp (config := { decide := true })

end Crypto.ARM64.Machine
