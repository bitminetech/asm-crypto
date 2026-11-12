import Reference.SHA256

namespace Crypto.Reference

/-- The byte-oriented reference matches the pinned bit-oriented FIPS
transcription for every message in the SHA-256 byte-length domain. -/
theorem sha256_matches_fips (message : ByteList)
    (lengthBound : message.bytes.size < 2 ^ 61) :
    MatchesFIPS message (sha256 message).2 lengthBound := by
  exact SHS.Equiv.SHA256.sha256_correct message.bytes lengthBound

theorem sha256_status (message : ByteList) : (sha256 message).1 = 0 := rfl

theorem sha256_digest_size (message : ByteList) :
    (sha256 message).2.toArray.size = 32 := (sha256 message).2.size_toArray

/-- The reference uses the message's used bytes, not its unused capacity or
pre-call digest bytes. Machine-level independence is a separate obligation. -/
theorem sha256_same_bytes (left right : ByteList) (h : left.bytes = right.bytes) :
    sha256 left = sha256 right := by
  simp only [sha256, h]

/-- The target profile's stricter buffer bound implies the SHA-256 limit. -/
theorem sha256_length_domain (message : ByteList)
    (wellFormed : message.WellFormed) (extentBound : message.size < 2 ^ 57) :
    message.bytes.size < 2 ^ 61 := by
  rcases wellFormed with ⟨_, _, _, hcount⟩
  have : message.bytes.size ≤ message.size := le_trans hcount (Nat.sub_le _ _)
  omega

end Crypto.Reference
