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
    ``Crypto.ARM64.Round.round_observations,
    ``Crypto.ARM64.Machine.program_vocabulary,
    ``Crypto.ARM64.Machine.storeLE_outside,
    ``Crypto.ARM64.Machine.storeLE_inside,
    ``Crypto.ARM64.Machine.addresses_length,
    ``Crypto.ARM64.Machine.read32_loadLE,
    ``Crypto.ARM64.Machine.add_offset_sub,
    ``Crypto.ARM64.Machine.read32_storeLE,
    ``Crypto.ARM64.Imported.all_instructions_decode,
    ``Crypto.ARM64.Imported.all_instructions_permitted,
    ``Crypto.ARM64.Imported.program_no_hooks,
    ``Crypto.ARM64.Imported.runToReturn_steps,
    ``Crypto.ARM64.Imported.runWords_decode,
    ``Crypto.ARM64.Imported.round_computes,
    ``Crypto.ARM64.Imported.round_frame,
    ``Crypto.ARM64.Imported.round_matches_spec,
    ``Crypto.ARM64.Imported.schedule_computes,
    ``Crypto.ARM64.Imported.schedule_frame,
    ``Crypto.ARM64.Imported.schedule_update_matches_spec,
    ``Crypto.ARM64.Imported.perm_write32,
    ``Crypto.ARM64.Imported.read32_write32,
    ``Crypto.ARM64.Imported.write32_cells_outside,
    ``Crypto.ARM64.Imported.read_word_store_other,
    ``Crypto.ARM64.Imported.wordVector_store64,
    ``Crypto.ARM64.Imported.canRead_write32,
    ``Crypto.ARM64.Imported.canWrite_write32,
    ``Crypto.ARM64.Imported.canExec_write32,
    ``Crypto.ARM64.Imported.schedule_ram_step,
    ``Crypto.ARM64.Imported.counter64_carry,
    ``Crypto.ARM64.Imported.round_control_step,
    ``Crypto.ARM64.Imported.schedule_control_step,
    ``Crypto.ARM64.Imported.round_cycle,
    ``Crypto.ARM64.Imported.iterateStep_invariant,
    ``Crypto.ARM64.Imported.runCycles_words,
    ``Crypto.ARM64.Imported.round_loop_prefix,
    ``Crypto.ARM64.Imported.round_loop,
    ``Crypto.ARM64.Imported.schedule_cycle,
    ``Crypto.ARM64.Imported.schedule_step_prefix,
    ``Crypto.ARM64.Imported.expanded_prefix,
    ``Crypto.ARM64.Imported.expanded_eq_schedule,
    ``Crypto.ARM64.Imported.schedule_loop_prefix,
    ``Crypto.ARM64.Imported.schedule_loop,
    ``Crypto.ARM64.Imported.schedule_loop_matches_spec,
    ``Crypto.ARM64.Imported.workspace_store_outside,
    ``Crypto.ARM64.Imported.read32_write32_disjoint,
    ``Crypto.ARM64.Imported.initial_load,
    ``Crypto.ARM64.Imported.feed_forward,
    ``Crypto.ARM64.Imported.compress_eq_rounds,
    ``Crypto.ARM64.Imported.compression]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun dependency => !allowed.contains dependency
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
    logInfo m!"AXIOMS PASS {name}: {axioms}"
