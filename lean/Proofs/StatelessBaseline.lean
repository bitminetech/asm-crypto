/-!
Shared baseline assembly for a stateless, effect-free leaf function. The
target statement supplies the FULL propositions below, including quantified
caller/environment conditions, the reference, native execution relation and
observable guarantees. These propositions and their semantic closure are part
of the independently reviewed expected statement required by §8; this wrapper
does not authenticate a candidate-supplied contract.

State rollback, action delivery and OS completion are discharged by a proof of
the recorded leaf/effect-free domain, rather than by assuming successful SHA
results or silently omitting those obligations. Stateful or effectful entries
require a different baseline with the corresponding interaction obligations.
-/
namespace Crypto.Baseline.Stateless

structure Requirements where
  referenceAndSafety : Prop
  concurrentExecution : Prop
  publicControlAndAddresses : Prop
  permittedDisclosures : Prop
  instructionTiming : Prop
  leafAndEffects : Prop

structure Equal (requirements : Requirements) : Prop where
  referenceAndSafety : requirements.referenceAndSafety
  concurrentExecution : requirements.concurrentExecution
  publicControlAndAddresses : requirements.publicControlAndAddresses
  permittedDisclosures : requirements.permittedDisclosures
  instructionTiming : requirements.instructionTiming
  leafAndEffects : requirements.leafAndEffects

end Crypto.Baseline.Stateless
