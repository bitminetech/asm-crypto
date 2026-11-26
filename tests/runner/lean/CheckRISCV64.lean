import Proofs.RISCV64
import Lean.Util.CollectAxioms

example : Crypto.Baseline.Stateless.Equal Crypto.RISCV64.modeledRequirements :=
  Crypto.RISCV64.modeled_baseline

open Lean Elab Command in
run_cmd do
  let names := #[``Crypto.RISCV64.modeled_baseline, ``Crypto.RISCV64.complete_layout,
    ``Crypto.RISCV64.jumpTargets_are_boundaries]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun dependency => !allowed.contains dependency
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
    logInfo m!"AXIOMS PASS {name}: {axioms}"
