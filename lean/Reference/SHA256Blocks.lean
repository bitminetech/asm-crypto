import Reference.SHA256

namespace Crypto.Reference

open EthLib.Cryptography.Hash.Sha256

/-- The byte array denoted by a repeated-content test vector. -/
def repeatedBytes (content : ByteArray) (size : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin size => content[i.val % content.size]!⟩

def alignedPadding (size : Nat) : ByteArray :=
  ⟨#[0x80] ++ Array.replicate 55 0 ++ (lengthBytes size).data⟩

@[simp] theorem repeatedBytes_size (content : ByteArray) (size : Nat) :
    (repeatedBytes content size).size = size := Array.size_ofFn

@[simp] theorem alignedPadding_size (size : Nat) : (alignedPadding size).size = 64 := by
  simp [alignedPadding, ByteArray.size, lengthBytes]

def emitDigest (state : State) : Vector UInt8 32 :=
  ⟨(EthLib.Cryptography.Hash.Sha256.digest state).data, by rfl⟩

def repeatCompression (content : ByteArray) (count : Nat) : State :=
  let block := repeatedBytes content 64
  Fin.foldl count (fun state _ => compress state block 0 (by simp [BLOCK_SIZE_BYTES, block])) initial

/-- A bounded-memory evaluation path for aligned, repeated test vectors. -/
def repeatedAlignedDigest (content : ByteArray) (size : Nat) : Vector UInt8 32 :=
  emitDigest (compress (repeatCompression content (size / 64)) (alignedPadding size) 0 (by simp [BLOCK_SIZE_BYTES]))

end Crypto.Reference
