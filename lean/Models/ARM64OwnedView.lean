import Models.ARM64CallFrame
import Proofs.ARM64.ImportedAccess

/-!
A narrow, conditional physical/profile boundary for the exact SHA instruction
vocabulary. This file defines obligations, not a hardware/OS instance or axiom.
There is no SHA result/reference premise in any obligation.

A location is a stable lease/object byte, not a fixed physical frame address;
page migration may preserve it. Only currently owned logical accesses constrain
bytes, liveness and semantic grants. Raw virtual addresses need not be globally
injective, untagged, or globally byte-equal to this logical view. Permission bits
are conservative logical capabilities, not prescribed physical PTE bits.

Scopes are dynamic. Inactive future/deallocated stack bytes need not be owned;
an environment transition may refresh logical cells there before acquisition.
Newly acquired bytes require a truthful view at the instruction boundary. This
separates reservation/grant validity from freezing inactive stack contents.
Physical timing and omitted FPCR framing have separate named profile laws.
-/
namespace Crypto.ARM64.OwnedView
universe u v

inductive AccessKind where
  | read | write | fetch
  deriving DecidableEq

structure LeaseByte (Lease : Type u) where
  lease : Lease
  offset : Nat

structure CPUContext where
  regs : Arm64.RegFile
  vregs : Arm64.VRegFile
  sp : BitVec 64
  pc : BitVec 64
  pstate : Arm64.PState
  tpidrEl0 : BitVec 64
  fpsr : BitVec 32
  status : Arm64.ExecStatus

def cpuContext (s : Arm64.State) : CPUContext :=
  ⟨s.regs, s.vregs, s.sp, s.pc, s.pstate, s.tpidrEl0, s.fpsr, s.status⟩

structure Profile (Hardware : Type u) (Lease : Type v) where
  cpu : Hardware → CPUContext
  resolve : Hardware → AccessKind → BitVec 64 → Option (LeaseByte Lease)
  contents : Hardware → LeaseByte Lease → BitVec 8
  live : Hardware → LeaseByte Lease → Prop
  grant : Hardware → AccessKind → LeaseByte Lease → Prop
  entrySymbol : Hardware → Option (BitVec 64)

/-- The caller/profile determines this scope from its active ownership phase;
there is no fixed requirement to own all 416 stack bytes throughout the call. -/
structure Scope where
  owns : AccessKind → BitVec 64 → Prop

/-- Agreement only at owned addresses, with true semantic grants and live
backing bytes. No condition is imposed on unrelated virtual addresses/PTEs. -/
def MemoryViewRel {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (scope : Scope) (hardware : Hardware) (logical : Arm64.State) : Prop :=
  ∀ kind address, scope.owns kind address → ∃ location,
    profile.resolve hardware kind address = some location ∧
    profile.live hardware location ∧ profile.grant hardware kind location ∧
    profile.contents hardware location = logical.mem.read8 address

def OwnedViewRel {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (scope : Scope) (hardware : Hardware) (logical : Arm64.State) : Prop :=
  profile.cpu hardware = cpuContext logical ∧ MemoryViewRel profile scope hardware logical

def BackingFootprint {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (scope : Scope) (location : LeaseByte Lease) : Prop :=
  ∃ kind address, scope.owns kind address ∧ profile.resolve hardware kind address = some location

def WritableFootprint {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (scope : Scope) (location : LeaseByte Lease) : Prop :=
  ∃ address, scope.owns .write address ∧ profile.resolve hardware .write address = some location

/-- Apply this to each pair of output/private-stack writable roles and their
other borrowed roles. Shared read-only aliases require no disjointness law. -/
def AliasSeparated {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (left right : Scope) : Prop :=
  ∀ location, ¬(BackingFootprint profile hardware left location ∧
    BackingFootprint profile hardware right location)

/-- Read/write/fetch translation may differ globally, including tagging rules.
Only access kinds jointly owned at this same address must name one lease byte. -/
def OwnedKindCoherent {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (scope : Scope) : Prop :=
  ∀ left right address, scope.owns left address → scope.owns right address →
    profile.resolve hardware left address = profile.resolve hardware right address

/-- Writable ownership excludes a conflicting second OWNED address for the
same backing byte. It permits same-address RW, arbitrary unowned aliases and
arbitrary shared read-only aliases; it is not global virtual-map injectivity. -/
def WritableAliasSafe {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (scope : Scope) : Prop :=
  ∀ writeAddress kind address location,
    scope.owns .write writeAddress → scope.owns kind address →
    profile.resolve hardware .write writeAddress = some location →
    profile.resolve hardware kind address = some location → writeAddress = address

structure LogicalByteEvent where
  kind : AccessKind
  address : BitVec 64

structure BackingByteEvent (Lease : Type u) where
  kind : AccessKind
  location : LeaseByte Lease

/-- Actual fetched instruction bytes and actual native data-access bytes.
Ordering of separate pair accesses follows Imported.dataAccesses. -/
def instructionEvents (instruction : Arm64.Instr) (s : Arm64.State) : List LogicalByteEvent :=
  (List.range 4).map (fun i => ⟨.fetch, s.pc + BitVec.ofNat 64 i⟩) ++
    (Imported.dataAccesses instruction s).flatMap (fun access =>
      (List.range access.bytes).map (fun i =>
        ⟨if access.write then .write else .read, access.address + BitVec.ofNat 64 i⟩))

def EventsOwned (scope : Scope) (events : List LogicalByteEvent) : Prop :=
  ∀ event ∈ events, scope.owns event.kind event.address

def ResolvedEvents {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware)
    (logicalEvents : List LogicalByteEvent) (hardwareEvents : List (BackingByteEvent Lease)) : Prop :=
  List.Forall₂ (fun logicalEvent hardwareEvent =>
    hardwareEvent.kind = logicalEvent.kind ∧
    profile.resolve hardware logicalEvent.kind logicalEvent.address = some hardwareEvent.location)
    logicalEvents hardwareEvents

/-- All backing bytes outside the alias-saturated OWNED writable set are
framed. This intentionally is not a frame theorem over raw virtual addresses. -/
def WritesFramed {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (scope : Scope) (before after : Hardware) : Prop :=
  ∀ location, ¬WritableFootprint profile before scope location →
    profile.contents after location = profile.contents before location

/-- A load/binding obligation for the final runtime symbol and recorded bytes.
The 604 fetched code bytes and 288 K/H data bytes have their distinct roles;
4 alignment bytes are not spuriously required as fetched or constant data.
This does not claim a checked final consuming application or installed loader. -/
def LoadedProgramBinding {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (hardware : Hardware) (base : BitVec 64) : Prop :=
  profile.entrySymbol hardware = some base ∧
  (∀ i, i < 604 → ∃ location,
    profile.resolve hardware .fetch (base + BitVec.ofNat 64 i) = some location ∧
    profile.live hardware location ∧ profile.grant hardware .fetch location ∧
    profile.contents hardware location = (Imported.program base).code[i]!) ∧
  (∀ i, 608 ≤ i → i < 896 → ∃ location,
    profile.resolve hardware .read (base + BitVec.ofNat 64 i) = some location ∧
    profile.live hardware location ∧ profile.grant hardware .read location ∧
    profile.contents hardware location = (Imported.program base).code[i]!)

/-- Successful outcomes must match the actual imported instruction update and
resolved events, and frame unrelated backing storage. -/
def MatchingOutcome {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (beforeScope afterScope : Scope)
    (instruction : Arm64.Instr) (logical : Arm64.State)
    (before after : Hardware) (events : List (BackingByteEvent Lease)) : Prop :=
  OwnedViewRel profile afterScope after (Arm64.execInstWithSvc Arm64.noSyscalls instruction logical) ∧
    ResolvedEvents profile before (instructionEvents instruction logical) events ∧
    WritesFramed profile beforeScope before after ∧
    (∀ kind address, afterScope.owns kind address →
      profile.resolve after kind address = profile.resolve before kind address)

/-- Reviewed target-profile obligation, restricted to exact admitted image
forms. Both progress and ALL hardware outcomes are required; an always-false
hardware step relation cannot satisfy the progress clause at valid entries.

MemoryViewRel for afterScope before execution is acquisition readiness, not a
SHA result premise: newly activated storage has truthful initial bytes/grants.
Unowned logical cells may be refreshed at environment boundaries to supply it.
The native after-state must be running, established by native call proofs. -/
def InstructionConformance {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease)
    (hardwareStep : Arm64.Instr → Hardware → List (BackingByteEvent Lease) → Hardware → Prop) : Prop :=
  ∀ base instruction logical before beforeScope afterScope,
    CallFrame.Admissible instruction →
    logical.status = .Running →
    (Imported.program base).fetchMem logical.mem logical.pc = some instruction →
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction logical).status = .Running →
    OwnedViewRel profile beforeScope before logical →
    MemoryViewRel profile afterScope before logical →
    OwnedKindCoherent profile before beforeScope →
    OwnedKindCoherent profile before afterScope →
    WritableAliasSafe profile before beforeScope →
    WritableAliasSafe profile before afterScope →
    EventsOwned beforeScope (instructionEvents instruction logical) →
    (∃ events after, hardwareStep instruction before events after) ∧
    (∀ events after, hardwareStep instruction before events after →
      MatchingOutcome profile beforeScope afterScope instruction logical before after events)

/-- A completed environment action restores the current thread's CPU context,
preserves live ownership and owned cells/resolution, and can change unrelated
memory or process/global resources. Scopes can omit inactive stack bytes;
logical cells outside the scope may be refreshed/rebased without restriction.
Fair scheduling/eventual current-thread progress is a separate execution law. -/
def EnvironmentConformance {Hardware : Type u} {Lease : Type v}
    (profile : Profile Hardware Lease) (environmentStep : Scope → Hardware → Hardware → Prop) : Prop :=
  ∀ scope before after logical,
    OwnedViewRel profile scope before logical → environmentStep scope before after →
    ∃ refreshed : Arm64.State,
      cpuContext refreshed = cpuContext logical ∧
      (∀ kind address, scope.owns kind address → refreshed.mem.cells address = logical.mem.cells address) ∧
      (∀ kind address, scope.owns kind address →
        profile.resolve after kind address = profile.resolve before kind address) ∧
      OwnedViewRel profile scope after refreshed

end Crypto.ARM64.OwnedView
