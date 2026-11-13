import Models.ARM64OwnedView
import Proofs.Borrow

/-!
Pointer-only ordinary scalar-leaf profile, pinned to AAPCS64 2026Q3:
https://github.com/ARM-software/abi-aa/blob/a1b53459479e88f3492ca9b11a161313764ab138/aapcs64/aapcs64.rst

These are conditional target/caller obligations, not a physical instance.
The modeled CPU already preserves more than this signature's required vector
register portion. No scalable-vector argument PCS is imposed. Arbitrary FPCR
preservation remains valid; ABI entry additionally requires only NEP clear,
not FPCR zero. Omitted SME state is explicitly framed under the exact admitted
ordinary instructions, including permitted dormant state; it is not forced off.

No blanket preservation of every omitted architectural field is asserted.
Optional control-flow mechanisms may have their own legitimate return effects;
the target return-context obligation must account for them. Active exceptions,
longjmp and cancellation cannot escape the operation under this profile.
-/
namespace Crypto.ARM64.PlatformProfile
universe u v w

/-- Semantic ZA classification supplied by the target's SME projection. -/
inductive ZAClass where
  | off | dormant | active
  deriving DecidableEq

/-- Payload contains the remaining architectural SME storage/control state;
caller-owned lazy-save descriptors/buffers are protected separately. -/
structure SMEContext (Payload : Type u) where
  streaming : Bool
  zaClass : ZAClass
  tpidr2El0 : BitVec 64
  payload : Payload

def NEPClear (fpcr : BitVec 32) : Prop := fpcr.getLsbD 2 = false

/-- Ordinary non-streaming/private-ZA interface. It accepts dormant ZA rather
than excluding all SME callers. Exact projection validity remains target-owned. -/
def OrdinaryScalarEntry {Payload : Type u} (fpcr : BitVec 32) (sme : SMEContext Payload) : Prop :=
  NEPClear fpcr ∧ sme.streaming = false ∧ (sme.zaClass = .off ∨ sme.zaClass = .dormant)

/-- Only the enumerated omitted SME ABI state is framed. No timing assumption,
FPCR value restriction, global PTE equality or guarded-return-state framing is
hidden in this obligation. The admitted domain is exactly the recorded image. -/
def HardwareSMEFrames {Hardware : Type u} {Lease : Type v} {Payload : Type w}
    (project : Hardware → SMEContext Payload)
    (hardwareStep : Arm64.Instr → Hardware → List (OwnedView.BackingByteEvent Lease) → Hardware → Prop) : Prop :=
  ∀ instruction before events after, CallFrame.Admissible instruction →
    hardwareStep instruction before events after → project after = project before

/-- Completed environment actions in the chosen context-restoring boundary
also restore omitted current-thread ABI state. Other threads, memory outside
owned leases and process resources may progress. Broader context-changing
callbacks need a different explicit ABI/environment correspondence law. -/
def EnvironmentOpaqueABIRestores {Hardware : Type u} {Payload : Type v}
    (fpcrProjection : Hardware → BitVec 32) (smeProjection : Hardware → SMEContext Payload)
    (environmentStep : OwnedView.Scope → Hardware → Hardware → Prop) : Prop :=
  ∀ scope before after, environmentStep scope before after →
    fpcrProjection after = fpcrProjection before ∧ smeProjection after = smeProjection before

inductive EnvironmentEventKind where
  | read | write | release | protectionChange
  deriving DecidableEq

structure EnvironmentBackingEvent (Lease : Type u) where
  kind : EnvironmentEventKind
  location : OwnedView.LeaseByte Lease

def EventReported (event : Crypto.Baseline.AccessEvent) (kind : EnvironmentEventKind)
    (address : BitVec 64) : Prop :=
  match kind with
  | .read => event.reads address
  | .write => event.writes address
  | .release => event.releases address
  | .protectionChange => event.changesProtection address

/-- Primitive event adequacy, in addition to CPU/cell preservation. Every real
external access or effective lease/grant invalidation is covered at EVERY owned
alias in the abstract AccessEvent. Thus a secret digest read cannot be hidden
merely because bytes and the current thread's CPU were preserved. Changes of
unused alias metadata that leave an owned lease/grant valid are not effective
protectionChange events on that owned lease. The actual event-bearing physical
relation and this law require independent target review; no instance is asserted. -/
def EnvironmentEventSoundness {Hardware : Type u} {Lease : Type v}
    (profile : OwnedView.Profile Hardware Lease)
    (actualEnvironment : OwnedView.Scope → Hardware → List (EnvironmentBackingEvent Lease) → Hardware → Prop)
    (reported : OwnedView.Scope → Hardware → Hardware → Crypto.Baseline.AccessEvent) : Prop :=
  ∀ scope before events after, actualEnvironment scope before events after →
    ∀ event ∈ events, ∀ accessKind address, scope.owns accessKind address →
    profile.resolve before accessKind address = some event.location →
    EventReported (reported scope before after) event.kind address

/-- Each predicate is an explicit target-owned adequacy obligation. Their
physical implementations/assumption IDs are fixed outside the candidate, not
proved by choosing these predicates or by serial CPU register preservation. -/
structure BoundaryPredicates (Hardware : Type u) where
  /-- Caller X29 denotes a valid caller frame chain whose live records are
  protected from this call's output/private-stack writable backing footprint. -/
  callerFrameChainValid : Hardware → BitVec 64 → Prop
  /-- The target permits this LR-preserving, call-free leaf to omit a new X29
  frame record while preserving the existing caller chain. -/
  leafFrameException : Hardware → BitVec 64 → Prop
  /-- Required caller ABI memory, including any live/dormant SME lazy-save
  descriptor/buffer and platform TLS, remains valid and protected from this
  invocation's writable backing footprint. No ZA-off condition is imposed. -/
  callerABIMemoryProtected : Hardware → Prop
  /-- Required current-thread stack bytes are mapped, committed/touched under
  guard/probing rules, with separate native/handler headroom. -/
  preparedStack : Hardware → BitVec 64 → Nat → Nat → Prop
  /-- Runtime unwind registration/load relocation describes this exact function
  range and allocation/restoration, under the OS's accepted unwind format. -/
  unwindBinding : Hardware → BitVec 64 → Nat → Prop
  /-- Armv8.0-A baseline instructions and required execution state are available
  through enforced deployment prerequisites or supported checks. -/
  executionFeatures : Hardware → Prop
  /-- Owned buffers/image are ordinary byte-addressable memory under the
  declared ISA view, without MMIO/device effects or retained pending accesses. -/
  ordinaryByteAddressableMemory : Hardware → Prop
  /-- Caller/environment borrow acquisition, cross-thread publication and
  release use the target's required synchronization/ownership-transfer rules.
  A normal RET is not assumed to drain stores globally. -/
  synchronizedOwnershipHandoff : Hardware → Prop
  /-- Normal LR return is valid under enabled return/branch protection and
  address translation; implicit protected control state is accounted for. -/
  normalReturnContext : Hardware → BitVec 64 → Prop
  /-- Environment policy excludes escape through the active operation by
  exception, longjmp or cancellation; normal asynchronous restoration is allowed. -/
  noEscapingControlTransfer : Hardware → Prop

/-- A target-profile entry obligation, separate from the proved logical typed
caller contract. The loader clause binds the actual symbol/code/pool bytes.
Handler headroom is explicit rather than inferred from the callee's 416 bytes. -/
def BoundaryEntry {Hardware : Type u} {Lease : Type v} {Payload : Type w}
    (profile : OwnedView.Profile Hardware Lease) (boundary : BoundaryPredicates Hardware)
    (fpcrProjection : Hardware → BitVec 32) (smeProjection : Hardware → SMEContext Payload)
    (hardware : Hardware) (base : BitVec 64) (logical : Arm64.State)
    (fpcr : BitVec 32) (sme : SMEContext Payload) (handlerHeadroom : Nat) : Prop :=
  fpcrProjection hardware = fpcr ∧ smeProjection hardware = sme ∧
  profile.cpu hardware = OwnedView.cpuContext logical ∧
  base.toNat % 16 = 0 ∧
  OrdinaryScalarEntry fpcr sme ∧
  boundary.callerFrameChainValid hardware (logical.readReg64 .x29) ∧
  boundary.leafFrameException hardware base ∧
  boundary.callerABIMemoryProtected hardware ∧
  boundary.preparedStack hardware logical.sp 416 handlerHeadroom ∧
  boundary.unwindBinding hardware base 604 ∧
  boundary.executionFeatures hardware ∧
  boundary.ordinaryByteAddressableMemory hardware ∧
  boundary.synchronizedOwnershipHandoff hardware ∧
  boundary.normalReturnContext hardware (logical.readReg64 .x30) ∧
  boundary.noEscapingControlTransfer hardware ∧
  OwnedView.LoadedProgramBinding profile hardware base

end Crypto.ARM64.PlatformProfile
