import Reference.SHA256
import EthLib.Cryptography.Proofs.Hash.Hmac

namespace Crypto.Reference

open EthLib.Cryptography.Hash

/-- The 64-byte output of the local key-normalization helper. -/
abbrev HmacKeyBlock := Vector UInt8 64

def hmacKey (key : ByteList) : HmacKeyBlock :=
  ⟨(Hmac.blockKey key.bytes).data, Hmac.blockKey_size key.bytes⟩

/-- Size of the scratch extent, including its eight-byte size field and the
inner ByteList's header and 64-byte pad. -/
def hmacScratchRequired (message : ByteList) : Nat := 96 + message.bytes.size

/-- The inner ByteList recorded by the public entry at scratch + 8. -/
def hmacInner (message : ByteList) (k0 : HmacKeyBlock) (scratchSize : Nat) : ByteList :=
  ⟨scratchSize - 8, 24, Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD ++ message.bytes⟩

/-- The 120-byte stack ByteList constructed by the finishing helper. -/
def hmacOuter (k0 : HmacKeyBlock) (innerDigest : Digest) : ByteList :=
  ⟨120, 24, Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD ++ EthLib.Base.packBytes innerDigest⟩

/-- The result of the finishing helper on its supplied inner ByteList. -/
def hmacFinish (inner : ByteList) (k0 : HmacKeyBlock) : Digest :=
  Sha256.hash32 (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD ++ Sha256.hash inner.bytes)

inductive HmacResult where
  | bufferTooSmall
  | ok (mac : Digest) (inner : ByteList)

def HmacResult.status : HmacResult → Nat
  | .bufferTooSmall => 1
  | .ok _ _ => 0

/-- The public result and the inner list written into scratch on success. -/
def hmacSha256 (key message : ByteList) (scratchSize : Nat) : HmacResult :=
  if scratchSize < hmacScratchRequired message then .bufferTooSmall
  else .ok (Hmac.hmac32 key.bytes message.bytes) (hmacInner message (hmacKey key) scratchSize)

end Crypto.Reference
