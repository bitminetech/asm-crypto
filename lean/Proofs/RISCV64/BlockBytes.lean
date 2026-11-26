import Proofs.RISCV64.InputWords
import Proofs.ARM64.ImportedReferenceLayout

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (memoryBlock memoryBlock_reference memoryBytes64 reverseWord_bytes
  lengthOffset paddingBlockCount paddingBlockCount_bytes paddedSpecBlock)
open Crypto.Reference.ByteLayout (paddedBlock paddedBlock_complete implPaddedBytes)

theorem blockWords_memoryBlock (m : Memory) (base : Addr) :
    blockWords m base = memoryBlock m base := by
  apply Vector.ext
  intro i hi
  simp only [blockWords, memoryBlock, Vector.getElem_ofFn, byteWord,
    Arm64.Memory.read32, reverseWord_bytes, BitVec.add_zero]
  rfl

private theorem blockWords_bytes (m : Memory) (base : Addr) (data : ByteArray) (i : Nat)
    (bytes : memoryBytes64 m base = paddedBlock data i) :
    blockWords m base = paddedSpecBlock data i :=
  (blockWords_memoryBlock m base).trans <| (memoryBlock_reference m base).trans <|
    congrArg (fun b => Crypto.Reference.WordModel.blockWords b) bytes

theorem complete_block_bytes (m : Memory) (base : Addr) (data : ByteArray)
    (input : ∀ i : Fin data.size, m.read8 (base + BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec)
    (i : Fin (data.size / 64)) :
    blockWords m (base + BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data i.val := by
  apply blockWords_bytes
  rw [paddedBlock_complete data i.val i.isLt]
  apply Vector.ext
  intro j hj
  simp only [memoryBytes64, Vector.getElem_ofFn]
  apply UInt8.eq_of_toBitVec_eq
  have enough : 64*i.val + j < data.size := by have := i.isLt; omega
  simpa only [UInt8.toBitVec_ofBitVec, BitVec.ofNat_add, BitVec.add_assoc, Nat.mul_comm]
    using input ⟨64*i.val+j, enough⟩

theorem padding_block_bytes (m : Memory) (base : Addr) (data : ByteArray)
    (input : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
      m.read8 (base + BitVec.ofNat 64 i.val) =
        ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec)
    (i : Fin (paddingBlockCount data)) :
    blockWords m (base + BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data (data.size / 64 + i.val) := by
  apply blockWords_bytes
  apply Vector.ext
  intro j hj
  simp only [memoryBytes64, paddedBlock, Vector.getElem_ofFn]
  apply UInt8.eq_of_toBitVec_eq
  have enough : 64*i.val + j < lengthOffset (data.size % 64) + 8 := by
    rw [← paddingBlockCount_bytes]
    have := i.isLt
    omega
  simpa only [UInt8.toBitVec_ofBitVec, BitVec.ofNat_add, BitVec.add_assoc, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_assoc]
    using input ⟨64*i.val+j, enough⟩

end Crypto.RISCV64
