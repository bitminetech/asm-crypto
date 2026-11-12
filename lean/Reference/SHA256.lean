import equiv.SHA256.Main

/-!
The imported definitions remain unchanged at the dependency pin in lakefile.toml.
This module adapts the byte-oriented reference to the library's portable values.
It does not model or verify assembly execution.
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
def sha256 (message : ByteList) : Nat × Digest :=
  (0, SHS.SHA256.Impl.sha256 message.bytes)

/-- Independent FIPS bit-oriented statement expected of the byte adapter. -/
def MatchesFIPS (message : ByteList) (digest : Digest)
    (lengthBound : message.bytes.size < 2 ^ 61) : Prop :=
  SHS.Equiv.SHA256.Digest.digestBitVec digest =
    SHS.SHA256.sha256
      (SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage message.bytes)
      (SHS.Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt message.bytes lengthBound)

end Crypto.Reference
