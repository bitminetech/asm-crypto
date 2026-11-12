import Proofs.ARM64.ImportedOuterLoop
import equiv.SHA256.ToU32s

/-!
The exact imported-memory block decoder equals the pinned byte-oriented FIPS
implementation's block decoder. All four byte positions of every big-endian
word agree. Whole-call preparation, fetched execution and equal are separate.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Bridge

theorem beU32_bytes (bytes : Vector UInt8 64) (i : Fin 16) :
    (SHS.SHA256.Impl.beU32 bytes i).toBitVec =
      (bytes[4 * i.val]'(by omega)).toBitVec ++
      (bytes[4 * i.val + 1]'(by omega)).toBitVec ++
      (bytes[4 * i.val + 2]'(by omega)).toBitVec ++
      (bytes[4 * i.val + 3]'(by omega)).toBitVec := by
  simp only [SHS.SHA256.Impl.beU32, UInt32.toBitVec_or]
  rw [toBitVec_shl_of_lt _ 24 (by decide), toBitVec_shl_of_lt _ 16 (by decide),
    toBitVec_shl_of_lt _ 8 (by decide)]
  simp only [UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  interval_cases k <;> simp (config := { decide := true })

def memoryBytes64 (m : Arm64.Memory) (base : BitVec 64) : Vector UInt8 64 :=
  Vector.ofFn fun i => UInt8.ofBitVec (m.read8 (base + BitVec.ofNat 64 i.val))

set_option maxHeartbeats 2000000 in
theorem memoryBlock_reference (m : Arm64.Memory) (base : BitVec 64) :
    memoryBlock m base = toSpecBlock (SHS.SHA256.Impl.toU32s (memoryBytes64 m base)) := by
  apply Vector.ext
  intro i hi
  simp only [toSpecBlock, SHS.SHA256.Impl.toU32s, Vector.getElem_map, Vector.getElem_ofFn]
  rw [beU32_bytes]
  simp only [memoryBlock, Vector.getElem_ofFn, Arm64.Memory.read32, reverseWord_bytes,
    memoryBytes64, UInt8.toBitVec_ofBitVec, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero]



end Crypto.ARM64.Imported
