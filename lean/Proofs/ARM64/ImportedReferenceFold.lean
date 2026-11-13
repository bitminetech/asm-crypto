import Proofs.ARM64.ImportedHashBody
import Proofs.ARM64.ImportedBlockReference
import Proofs.ARM64.ImportedPaddingReference
import equiv.SHA256.Pipeline
import equiv.SHA256.Padding.Equiv

/-!
The two native-memory compression folds are connected to the pinned FIPS
padded-block fold and to its exact 32-byte sha256 result. The input block
identities and initialized IV remain explicit layout/value hypotheses.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Padding.Layout
open SHS.Equiv.SHA256.Padding.Equiv
open SHS.Equiv.SHA256.Digest
open SHS.Equiv.ArrayFold

def paddedSpecBlock (data : ByteArray) (i : Nat) : Vector (BitVec 32) 16 :=
  toSpecBlock (SHS.SHA256.Impl.toU32s (paddedBlock data i))

def paddedSpecFold (data : ByteArray) (count : Nat) : Vector (BitVec 32) 8 :=
  Fin.foldl count (fun H i => SHS.SHA256.compress H (paddedSpecBlock data i.val)) SHS.SHA256.H0_256

theorem reference_state_fold (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
      (fun H block => SHS.SHA256.Impl.compress H (SHS.SHA256.Impl.toU32s block))
      SHS.SHA256.Impl.H256_256) = paddedSpecFold data ((implPaddedBytes data).size / 64) := by
  rw [SHS.Equiv.SHA256.Pipeline.foldl_compress_lift, Array.foldl_map]
  unfold implPaddedBlocks
  rw [array_foldl_ofFn_eq_fin_foldl]
  rfl

theorem reference_word_byte (w : UInt32) (k : Fin 4) :
    (((w >>> UInt32.ofNat ((3 - k.val) * 8)) &&& 0xff).toUInt8).toBitVec =
      w.toBitVec.extractLsb' (8 * (3 - k.val)) 8 := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;>
    simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_and,
      UInt32.toBitVec_shiftRight, UInt32.toBitVec_ofNat, UInt32.toBitVec_ofNat']
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro i hi
  all_goals interval_cases i <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and]
  all_goals simp (config := { decide := true })

theorem digestBytes_toSpecState (H : SHS.SHA256.Impl.State) :
    digestBytes (toSpecState H) = (extractDigest H).map UInt8.toBitVec := by
  apply Vector.ext
  intro i hi
  simp only [digestBytes, extractDigest, Vector.getElem_map, Vector.getElem_ofFn]
  rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ (by omega : i / 4 < 8)]
  simp only [toSpecState, Vector.getElem_map]
  exact (reference_word_byte (H[i / 4]'(by omega)) ⟨i % 4, by omega⟩).symm

theorem reference_digest_bytes (data : ByteArray) (bound : data.size < 2 ^ 61) :
    (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec =
      digestBytes (paddedSpecFold data ((implPaddedBytes data).size / 64)) := by
  rw [impl_sha256_eq_refactored data bound, implSha256Refactored_eq_extractDigest]
  have bytes := digestBytes_toSpecState ((implPaddedBlocks data).foldl
      (fun H block => SHS.SHA256.Impl.compress H (SHS.SHA256.Impl.toU32s block))
      SHS.SHA256.Impl.H256_256)
  rw [reference_state_fold] at bytes
  exact bytes.symm

def paddingBlockCount (data : ByteArray) : Nat := if data.size % 64 < 56 then 1 else 2

theorem padded_block_count (data : ByteArray) :
    (implPaddedBytes data).size / 64 = data.size / 64 + paddingBlockCount data := by
  rw [padded_tail_size]
  unfold lengthOffset paddingBlockCount
  split <;> omega

theorem phasesHash_reference (s : Arm64.State) (data : ByteArray)
    (initial : savedHash s = SHS.SHA256.H0_256)
    (fullBlocks : ∀ i : Fin (data.size / 64),
      memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)) = paddedSpecBlock data i.val)
    (paddingBlocks : ∀ i : Fin (paddingBlockCount data),
      memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) =
        paddedSpecBlock data (data.size / 64 + i.val)) :
    phasesHash s (data.size / 64) (paddingBlockCount data) =
      paddedSpecFold data ((implPaddedBytes data).size / 64) := by
  rw [padded_block_count]
  unfold paddedSpecFold phasesHash
  rw [Fin.foldl_add, initial]
  have full := fin_foldl_ext (data.size / 64)
    (fun H i => SHS.SHA256.compress H (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val))))
    (fun H i => SHS.SHA256.compress H (paddedSpecBlock data i.val)) SHS.SHA256.H0_256
    (fun H i => congrArg (SHS.SHA256.compress H) (fullBlocks i))
  rw [full]
  apply fin_foldl_ext
  intro H i
  exact congrArg (SHS.SHA256.compress H) (paddingBlocks i)

end Crypto.ARM64.Imported
