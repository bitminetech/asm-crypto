import Proofs.ARM64.ImportedOuterLoop
import Reference.ReferenceFold

namespace Crypto.ARM64.Imported

def memoryBytes64 (m : Arm64.Memory) (base : BitVec 64) : Vector UInt8 64 :=
  Vector.ofFn fun i => UInt8.ofBitVec (m.read8 (base + BitVec.ofNat 64 i.val))

set_option maxHeartbeats 2000000 in
theorem memoryBlock_reference (m : Arm64.Memory) (base : BitVec 64) :
    memoryBlock m base = Crypto.Reference.WordModel.blockWords (memoryBytes64 m base) := by
  apply Vector.ext
  intro i hi
  simp only [Crypto.Reference.WordModel.blockWords, memoryBlock, Vector.getElem_ofFn, Arm64.Memory.read32, reverseWord_bytes,
    memoryBytes64, UInt8.toBitVec_ofBitVec, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero]



end Crypto.ARM64.Imported
