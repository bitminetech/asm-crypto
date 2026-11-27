import Proofs.Borrow
import Proofs.StatelessBaseline

namespace Crypto.HMACSHA256

open Crypto.Baseline

/-- A stateless native routine under a borrowed-buffer boundary. The
invocation values contain the concrete loaded-code and caller premises.
The schedule relations start at the invocation's actual machine state. -/
structure BorrowedNative where
  State : Type
  Event : Type
  Call : Address → Type
  Environment : {base : Address} → Call base → Type
  Profile : Address → Type
  scope : {base : Address} → Call base → BorrowScope
  accesses : Event → List AccessEvent
  environmentAccess : ∀ {base : Address} {call : Call base}, Environment call → Nat → State → AccessEvent
  permittedEnvironment : ∀ {base : Address} {call : Call base} (env : Environment call) tick state,
    EnvironmentAccess (scope call) (environmentAccess env tick state)
  result : {base : Address} → Call base → State → Prop
  stepBound : {base : Address} → Call base → Nat
  scheduled : {base : Address} → (call : Call base) → Environment call → List Event → State → Prop
  costed : {base : Address} → (call : Call base) → Environment call → Profile base → List Event → State → Nat → Prop
  samePublic : {base : Address} → Call base → Call base → Prop

def BorrowedNative.Complete (spec : BorrowedNative) : Prop :=
  ∀ {base : Address} (call : spec.Call base) (env : spec.Environment call),
    ∃ out events, spec.scheduled call env events out ∧ events.length ≤ spec.stepBound call ∧
      spec.result call out ∧
      ∀ event ∈ events, ∀ access ∈ spec.accesses event, CallAccess (spec.scope call) access

def BorrowedNative.Timing (spec : BorrowedNative) : Prop :=
  ∀ {base : Address} (a b : spec.Call base) (envA : spec.Environment a) (envB : spec.Environment b),
    spec.samePublic a b → ∀ profile : spec.Profile base,
      ∃ outA outB events cost, spec.costed a envA profile events outA cost ∧ spec.costed b envB profile events outB cost

def BorrowedNative.requirements (spec : BorrowedNative) : Stateless.Requirements where
  referenceAndSafety := spec.Complete
  concurrentExecution :=
    ∀ {base : Address} (call : spec.Call base) (env : spec.Environment call),
      ∃ out events, spec.scheduled call env events out ∧ spec.result call out ∧
        ∀ event ∈ events, ∀ access ∈ spec.accesses event, ∀ tick state,
          ¬DataRace access (spec.environmentAccess env tick state)
  publicControlAndAddresses :=
    ∀ {base : Address} (a b : spec.Call base) (envA : spec.Environment a) (envB : spec.Environment b),
      spec.samePublic a b →
        ∃ outA outB events, spec.scheduled a envA events outA ∧ spec.scheduled b envB events outB
  permittedDisclosures :=
    ∀ {base : Address} (call : spec.Call base) (env : spec.Environment call),
      ∃ out events, spec.scheduled call env events out ∧ spec.result call out
  instructionTiming := spec.Timing
  leafAndEffects :=
    ∀ {base : Address} (call : spec.Call base) (env : spec.Environment call),
      ∃ out events, spec.scheduled call env events out ∧
        ∀ event ∈ events, ∀ access ∈ spec.accesses event,
          (∀ p, ¬access.releases p) ∧ (∀ p, ¬access.changesProtection p)

theorem BorrowedNative.equal (spec : BorrowedNative)
    (complete : spec.Complete) (timing : spec.Timing)
    (units : ∀ base, spec.Profile base)
    (erase : ∀ {base : Address} {call : spec.Call base} {env profile events out cost},
      spec.costed call env profile events out cost → spec.scheduled call env events out) :
    Stateless.Equal spec.requirements := by
  refine ⟨complete, ?_, ?_, ?_, timing, ?_⟩
  · intro base call env
    obtain ⟨out, events, executed, _, result, owned⟩ := complete call env
    exact ⟨out, events, executed, result, fun event hit access seen tick state =>
      borrow_accesses_race_free _ _ _ (owned event hit access seen) (spec.permittedEnvironment env tick state)⟩
  · intro base a b envA envB same
    obtain ⟨outA, outB, events, _, one, other⟩ := timing a b envA envB same (units base)
    exact ⟨outA, outB, events, erase one, erase other⟩
  · intro base call env
    obtain ⟨out, events, executed, _, result, _⟩ := complete call env
    exact ⟨out, events, executed, result⟩
  · intro base call env
    obtain ⟨out, events, executed, _, _, owned⟩ := complete call env
    exact ⟨out, events, executed, fun event hit access seen => (owned event hit access seen).2.2⟩

end Crypto.HMACSHA256
