import Proofs
import Lean.Util.CollectAxioms

/-! This audit covers only the registered supporting theorems below. It cannot
certify `equal`: that theorem and the full machine baseline do not yet exist.
The statement checks here must not be substituted for the independently
reviewed expected statement/dependency closure required for `equal` by §8. -/

example (message : Crypto.Reference.ByteList) (h : message.bytes.size < 2 ^ 61) :
    Crypto.Reference.MatchesFIPS message (Crypto.Reference.sha256 message).2 h :=
  Crypto.Reference.sha256_matches_fips message h

example (s : Crypto.ARM64.Round.State) :
    (Crypto.ARM64.Round.runWords Crypto.ARM64.Round.code s).map
      Crypto.ARM64.Round.working =
    some (Crypto.ARM64.Round.fipsRound (Crypto.ARM64.Round.working s)
      (Crypto.ARM64.Round.read32 s.memory
        (Crypto.ARM64.Round.readBase s 0 + (Crypto.ARM64.Round.readX s 5 <<< 2)))
      (Crypto.ARM64.Round.read32 s.memory (s.sp + (Crypto.ARM64.Round.readX s 5 <<< 2)))) :=
  Crypto.ARM64.Round.round_computes s

open Lean Elab Command in
run_cmd do
  let names := #[
    ``SHS.Equiv.SHA256.sha256_correct,
    ``SHS.Equiv.SHA256.compress_correct,
    ``Crypto.Reference.sha256_matches_fips,
    ``Crypto.Reference.sha256_status,
    ``Crypto.Reference.sha256_digest_size,
    ``Crypto.Reference.sha256_same_bytes,
    ``Crypto.Reference.sha256_length_domain,
    ``Crypto.Reference.repeatedBytes_size,
    ``Crypto.Reference.repeatedBytes_get,
    ``Crypto.Reference.repeated_block_byte,
    ``Crypto.Reference.repeated_block_words,
    ``Crypto.Reference.repeatedAlignedDigest_eq_reference,
    ``Crypto.ARM64.image_round_constants,
    ``Crypto.ARM64.image_initial_hash,
    ``Crypto.ARM64.Round.ch_or_eq_xor,
    ``Crypto.ARM64.Round.maj_factored,
    ``Crypto.ARM64.Round.extr_same,
    ``Crypto.ARM64.Round.narrow_shift,
    ``Crypto.ARM64.Round.code_length,
    ``Crypto.ARM64.Round.round_computes,
    ``Crypto.ARM64.Round.round_observations]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun dependency => !allowed.contains dependency
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
    logInfo m!"AXIOMS PASS {name}: {axioms}"
