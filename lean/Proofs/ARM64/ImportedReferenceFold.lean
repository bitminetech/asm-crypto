import Proofs.ARM64.ImportedHashBody
import Proofs.ARM64.ImportedBlockReference
import Proofs.ARM64.ImportedPaddingReference
import Reference.SHA256

namespace Crypto.ARM64.Imported
open Crypto.Reference.ByteLayout
open Crypto.Reference.WordModel (fin_foldl_ext)

abbrev paddedSpecBlock := Crypto.Reference.WordModel.paddedSpecBlock
abbrev paddedSpecFold := Crypto.Reference.WordModel.paddedSpecFold

theorem reference_digest_bytes (data : ByteArray) (bound : data.size < 2 ^ 61) :
    (Crypto.Reference.digest data).map UInt8.toBitVec =
      digestBytes (paddedSpecFold data ((implPaddedBytes data).size / 64)) := by
  rw [Crypto.Reference.digest, if_neg (Nat.not_le.mpr bound)]
  exact Crypto.Reference.WordModel.reference_digest_bytes data bound

def paddingBlockCount (data : ByteArray) : Nat := if data.size % 64 < 56 then 1 else 2

theorem padded_block_count (data : ByteArray) :
    (implPaddedBytes data).size / 64 = data.size / 64 + paddingBlockCount data := by
  rw [padded_tail_size]
  unfold lengthOffset paddingBlockCount
  split <;> omega

theorem phasesHash_reference (s : Arm64.State) (data : ByteArray)
    (initial : savedHash s = Crypto.Reference.WordModel.H0_256)
    (fullBlocks : ∀ i : Fin (data.size / 64),
      memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)) = paddedSpecBlock data i.val)
    (paddingBlocks : ∀ i : Fin (paddingBlockCount data),
      memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) =
        paddedSpecBlock data (data.size / 64 + i.val)) :
    phasesHash s (data.size / 64) (paddingBlockCount data) =
      paddedSpecFold data ((implPaddedBytes data).size / 64) := by
  rw [padded_block_count]
  unfold paddedSpecFold Crypto.Reference.WordModel.paddedSpecFold phasesHash
  rw [Fin.foldl_add, initial]
  have full := fin_foldl_ext (data.size / 64)
    (fun H i => Crypto.Reference.WordModel.compress H (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val))))
    (fun H i => Crypto.Reference.WordModel.compress H (paddedSpecBlock data i.val)) Crypto.Reference.WordModel.H0_256
    (fun H i => congrArg (Crypto.Reference.WordModel.compress H) (fullBlocks i))
  rw [full]
  apply fin_foldl_ext
  intro H i
  exact congrArg (Crypto.Reference.WordModel.compress H) (paddingBlocks i)

end Crypto.ARM64.Imported
