import Proofs.HMACSHA256
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let names := #[
    ``Crypto.HMACSHA256.ARM64.hmac_sha256.equal,
    ``Crypto.HMACSHA256.ARM64.hmac_key.equal,
    ``Crypto.HMACSHA256.ARM64.hmac_finish.equal,
    ``Crypto.HMACSHA256.X86_64.hmac_sha256.equal,
    ``Crypto.HMACSHA256.X86_64.hmac_key.equal,
    ``Crypto.HMACSHA256.X86_64.hmac_finish.equal,
    ``Crypto.HMACSHA256.RISCV64.hmac_sha256.equal,
    ``Crypto.HMACSHA256.RISCV64.hmac_key.equal,
    ``Crypto.HMACSHA256.RISCV64.hmac_finish.equal]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun dependency => !allowed.contains dependency
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
    logInfo m!"AXIOMS PASS {name}: {axioms}"
