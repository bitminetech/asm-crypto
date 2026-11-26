import Proofs.X86_64.BlockPhase
import Proofs.ARM64.ImportedReferenceLayout

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (memoryBlock memoryBytes64 paddedSpecBlock paddedSpecFold paddingBlockCount digestBytes)
open Crypto.Reference.ByteLayout
open Crypto.Reference.WordModel (fin_foldl_ext)

attribute [local irreducible] Crypto.Reference.WordModel.compress wordsFrom Crypto.Reference.WordModel.paddedSpecBlock

private theorem fold_fin (m : Mem) (ptr : Val) (n : Nat) (h : Vector Word 8) :
    foldBlocks m ptr n h = Fin.foldl n
      (fun a i => Crypto.Reference.WordModel.compress a (wordsFrom m (ptr+BitVec.ofNat 64 (64*i.val)))) h := by
  induction n generalizing ptr h with
  | zero => simp [foldBlocks]
  | succ n ih =>
    rw [foldBlocks, Fin.foldl_succ, ih]
    simp
    apply fin_foldl_ext
    intro a i
    have addr : ptr+64+BitVec.ofNat 64 (64*i.val) = ptr+BitVec.ofNat 64 (64*i.succ.val) := by
      rw [Fin.val_succ, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (64 : Val)]; rfl
    exact congrArg (fun p => Crypto.Reference.WordModel.compress a (wordsFrom m p)) addr

private theorem words_of_bytes (m : Mem) (ptr : Val) (data : ByteArray) (t : Nat)
    (bytes : memoryBytes64 (byteView m) ptr = paddedBlock data t) :
    wordsFrom m ptr = paddedSpecBlock data t := by
  have eq : wordsFrom m ptr = memoryBlock (byteView m) ptr := by
    apply Vector.ext
    intro i hi
    simp [wordsFrom, memoryBlock, Vector.getElem_ofFn, Arm64.Memory.read32,
      Crypto.ARM64.Imported.reverseWord_bytes, byteView_read, BitVec.add_zero]
  unfold paddedSpecBlock Crypto.Reference.WordModel.paddedSpecBlock
  exact eq.trans ((Crypto.ARM64.Imported.memoryBlock_reference _ _).trans
    (congrArg (fun b => Crypto.Reference.WordModel.blockWords b) bytes))

private theorem full_words (m : Mem) (ptr : Val) (data : ByteArray)
    (bytes : ∀ i : Fin data.size, m.read (ptr+BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec)
    (i : Fin (data.size/64)) :
    wordsFrom m (ptr+BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data i.val := by
  apply words_of_bytes
  rw [paddedBlock_complete data i.val i.isLt]
  apply Vector.ext
  intro j hj
  apply UInt8.eq_of_toBitVec_eq
  have bound : 64*i.val+j < data.size := by have := i.isLt; omega
  simpa only [memoryBytes64, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec, byteView_read,
    BitVec.ofNat_add, BitVec.add_assoc, Nat.mul_comm] using bytes ⟨64*i.val+j,bound⟩

private theorem padding_words (m : Mem) (ptr : Val) (data : ByteArray)
    (bytes : ∀ i : Fin (64*paddingBlockCount data), m.read (ptr+BitVec.ofNat 64 i.val) =
      ((implPaddedBytes data).get! (data.size/64*64+i.val)).toBitVec)
    (i : Fin (paddingBlockCount data)) :
    wordsFrom m (ptr+BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data (data.size/64+i.val) := by
  apply words_of_bytes
  apply Vector.ext
  intro j hj
  apply UInt8.eq_of_toBitVec_eq
  have bound : 64*i.val+j < 64*paddingBlockCount data := by have := i.isLt; omega
  simpa only [memoryBytes64, paddedBlock, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec, byteView_read,
    BitVec.ofNat_add, BitVec.add_assoc, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_assoc] using bytes ⟨64*i.val+j,bound⟩

/-- The two concrete memory folds, using their respective input snapshots,
produce the pinned SHA-256 reference digest once the prepared bytes are known. -/
theorem folds_reference (data : ByteArray) (bound : data.size < 2^61) (message padding : Mem)
    (ptr pad : Val)
    (source : ∀ i : Fin data.size, message.read (ptr+BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec)
    (prepared : ∀ i : Fin (64*paddingBlockCount data), padding.read (pad+BitVec.ofNat 64 i.val) =
      ((implPaddedBytes data).get! (data.size/64*64+i.val)).toBitVec) :
    digestBytes (foldBlocks padding pad (paddingBlockCount data)
      (foldBlocks message ptr (data.size/64) Crypto.Reference.WordModel.H0_256)) =
      (Crypto.Reference.digest data).map UInt8.toBitVec := by
  rw [Crypto.ARM64.Imported.reference_digest_bytes data bound, Crypto.ARM64.Imported.padded_block_count]
  apply congrArg digestBytes
  rw [fold_fin, fold_fin, paddedSpecFold, Crypto.Reference.WordModel.paddedSpecFold, Fin.foldl_add]
  have full := fin_foldl_ext (data.size/64)
    (fun h i => Crypto.Reference.WordModel.compress h (wordsFrom message (ptr+BitVec.ofNat 64 (64*i.val))))
    (fun h i => Crypto.Reference.WordModel.compress h (paddedSpecBlock data i.val)) Crypto.Reference.WordModel.H0_256
    (fun h i => congrArg (Crypto.Reference.WordModel.compress h) (full_words _ _ _ source i))
  rw [full]
  apply fin_foldl_ext
  intro h i
  exact congrArg (Crypto.Reference.WordModel.compress h) (padding_words _ _ _ prepared i)

end Crypto.X86_64
