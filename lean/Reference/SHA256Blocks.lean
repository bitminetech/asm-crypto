import impl.SHA256

namespace Crypto.Reference

/-- The mathematical byte array denoted by a repeated-content test vector.
Only proofs construct this array for large messages; the runner uses blocks. -/
def repeatedBytes (content : ByteArray) (size : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin size => content[i.val % content.size]!)

def alignedPadding (size : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 =>
    if i.val < 56 then (if i.val = 0 then 0x80 else 0)
    else (((size.toUInt64 <<< 3) >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8

def emitDigest (state : SHS.SHA256.Impl.State) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 =>
    let word : Fin 8 := ⟨i.val / 4, by omega⟩
    ((state[word] >>> (UInt32.ofNat ((3 - i.val % 4) * 8))) &&& 0xff).toUInt8

/-- A bounded-memory evaluation path for whole-block repetition. The equality
with the imported whole-message reference is proved in Proofs.Repeated. -/
def repeatedAlignedDigest (content : ByteArray) (size : Nat) : Vector UInt8 32 :=
  let block : Vector UInt8 64 := Vector.ofFn fun i => content[i.val % content.size]!
  let words := SHS.SHA256.Impl.toU32s block
  let state := Fin.foldl (size / 64)
    (fun state _ => SHS.SHA256.Impl.compress state words) SHS.SHA256.Impl.H256_256
  emitDigest (SHS.SHA256.Impl.compress state (SHS.SHA256.Impl.toU32s (alignedPadding size)))

end Crypto.Reference
