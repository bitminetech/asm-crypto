import Models.ARM64PlatformProfile
import Proofs.ARM64.ImportedABI

namespace Crypto.ARM64.PlatformProfile

/-- ABI-valid NEP survives the proved native restricted framed return, although
FPCR's other bits remain arbitrary. HardwareFPCRFrames supplies physical framing. -/
theorem framed_nep_clear {base : BitVec 64} {fuel : Nat} {before after : CallFrame.State}
    (returned : CallFrame.FramedReturn base fuel before after) (entry : NEPClear before.fpcr) :
    NEPClear after.fpcr := by
  rw [returned.fpcr_preserved]
  exact entry

theorem framed_ordinary_interface {Payload : Type} {base : BitVec 64} {fuel : Nat}
    {before after : CallFrame.State} {smeBefore smeAfter : SMEContext Payload}
    (returned : CallFrame.FramedReturn base fuel before after)
    (smePreserved : smeAfter = smeBefore) (entry : OrdinaryScalarEntry before.fpcr smeBefore) :
    OrdinaryScalarEntry after.fpcr smeAfter := by
  rw [returned.fpcr_preserved, smePreserved]
  exact entry

/-- The omitted interface facts are preserved conditionally on the explicit
primitive framing law; no whole-function result is an assumption of that law. -/
theorem hardware_sme_interface_preserved {Hardware Lease Payload : Type}
    (project : Hardware → SMEContext Payload)
    (hardwareStep : Arm64.Instr → Hardware → List (OwnedView.BackingByteEvent Lease) → Hardware → Prop)
    (frames : HardwareSMEFrames project hardwareStep)
    (instruction : Arm64.Instr) (before after : Hardware)
    (events : List (OwnedView.BackingByteEvent Lease)) (admitted : CallFrame.Admissible instruction)
    (actual : hardwareStep instruction before events after)
    (entry : (project before).streaming = false ∧
      ((project before).zaClass = .off ∨ (project before).zaClass = .dormant)) :
    (project after).streaming = false ∧
      ((project after).zaClass = .off ∨ (project after).zaClass = .dormant) := by
  rw [frames instruction before events after admitted actual]
  exact entry

/-- Truthful alias-saturated event reporting and the checked borrow policy
exclude even a byte-preserving physical read of an exclusively borrowed byte. -/
theorem environment_no_exclusive_read {Hardware Lease : Type}
    (profile : OwnedView.Profile Hardware Lease)
    (actualEnvironment : OwnedView.Scope → Hardware → List (EnvironmentBackingEvent Lease) → Hardware → Prop)
    (reported : OwnedView.Scope → Hardware → Hardware → Crypto.Baseline.AccessEvent)
    (sound : EnvironmentEventSoundness profile actualEnvironment reported)
    (scope : OwnedView.Scope) (borrow : Crypto.Baseline.BorrowScope)
    (before after : Hardware) (events : List (EnvironmentBackingEvent Lease))
    (actual : actualEnvironment scope before events after)
    (allowed : Crypto.Baseline.EnvironmentAccess borrow (reported scope before after))
    (event : EnvironmentBackingEvent Lease) (present : event ∈ events) (reading : event.kind = .read)
    (accessKind : OwnedView.AccessKind) (address : BitVec 64)
    (owned : scope.owns accessKind address) (exclusive : borrow.exclusive address)
    (resolved : profile.resolve before accessKind address = some event.location) : False := by
  have observed := sound scope before events after actual event present accessKind address owned resolved
  rw [reading] at observed
  exact allowed.1 address exclusive observed

end Crypto.ARM64.PlatformProfile
