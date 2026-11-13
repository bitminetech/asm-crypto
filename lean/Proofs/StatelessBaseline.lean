/-!
Shared baseline for a stateless, effect-free leaf function. Target requirements
specify caller/environment conditions, the reference, native execution and
observable guarantees. Equal combines functional safety, concurrency,
confidentiality, timing and leaf-effect proofs for those requirements.

The leaf/effect-free domain discharges state rollback, action delivery and OS
completion obligations. Stateful or effectful entries use a baseline with the
corresponding interaction obligations.
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
