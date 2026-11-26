import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
The portable ByteList interface uses the pinned EthLib SHA-256 reference.
-/

namespace Crypto.Reference

/-- The value of a ByteList after reading its three little-endian header fields
and independently establishing its accessible extent. Addresses and permissions
belong in the machine entry predicate, not in this portable value. -/
structure ByteList where
  size : Nat
  offset : Nat
  bytes : ByteArray

/-- The portable layout conditions. The actual allocation must independently
supply `size` accessible bytes; this proposition alone grants no permission. -/
def ByteList.WellFormed (message : ByteList) : Prop :=
  24 ≤ message.offset ∧ message.offset % 8 = 0 ∧
  message.offset ≤ message.size ∧
  message.bytes.size ≤ message.size - message.offset

/-- Fixed-size big-endian digest, matching docs/reference/sha-256.md. -/
abbrev Digest := Vector UInt8 32

/-- The reference result. The only successful status is zero. No modeled machine
execution, memory safety or constant-time claim follows from this definition. -/
def digest (bytes : ByteArray) : Digest :=
  if 2 ^ 61 ≤ bytes.size then
    panic! s!"SHA-256 input size {bytes.size} exceeds the FIPS 180-4 limit"
  else EthLib.Cryptography.Hash.Sha256.hash32 bytes

def sha256 (message : ByteList) : Nat × Digest :=
  (0, digest message.bytes)

/-- Digest conformance to EthLib's FIPS 180-4 specification. -/
def MatchesFIPS (message : ByteList) (result : Digest)
    (_lengthBound : message.bytes.size < 2 ^ 61) : Prop :=
  EthLib.Base.packBytes result = EthLib.Cryptography.Hash.Sha256.Spec.hash message.bytes

end Crypto.Reference
