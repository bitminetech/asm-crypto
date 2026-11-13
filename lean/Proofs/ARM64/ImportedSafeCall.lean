import Proofs.ARM64.ImportedVerifiedCall
import Proofs.ARM64.ImportedPermissionView
import Proofs.ARM64.ImportedStackBound
import Proofs.ARM64.ImportedFetchTrace

/-!
Compose bounded fetched correctness with logical data-access and stack-trace
bounds. The permission view preserves caller bytes and expresses borrowed
semantic grants. Physical permissions and address interpretation follow the
target profile documented in arm64-sha256-native-profile.md.
-/
namespace Crypto.ARM64.Imported

structure LogicalCallResult (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (authority : Crypto.Baseline.Authority)
    (out : Arm64.State) (observations : List InstructionObservation) : Prop where
  returned : runToReturn (program base) (512 + 4000 * ((message.bytes.size + 8) / 64 + 1))
    (logicalState base s message) = some out
  steps : Arm64.Steps (program base) (logicalState base s message) out
  observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
    (logicalState base s message) = some (out, observations)
  state : returnStable out = returnStable s
  nonvolatile : Crypto.ARM64.Imported.nonvolatile out = Crypto.ARM64.Imported.nonvolatile s
  stackRestored : out.sp = s.sp
  returnAddress : out.pc = s.readReg64 .x30
  status : out.readReg64 .x0 = 0#64
  running : out.status = .Running
  digest : memoryBytes32 out.mem (s.readReg64 .x1) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  finalMemory : ∀ p, 416 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.readReg64 .x1).toNat →
    out.mem.read8 p = s.mem.read8 p
  confined : ∀ observation ∈ observations, ∀ access ∈ observation.accesses, access.WithinView base s message
  grants : ∀ observation ∈ observations, ∀ access ∈ observation.accesses, ∀ i, i < access.bytes →
    if access.write then authority.writable (access.address + BitVec.ofNat 64 i)
    else authority.readable (access.address + BitVec.ofNat 64 i)
  fetches : ∀ observation ∈ observations, ∀ i, i < 4 →
    (callerImage base).Contains (observation.pc + BitVec.ofNat 64 i)
  fetchGrants : ∀ observation ∈ observations, ∀ i, i < 4 →
    authority.executable (observation.pc + BitVec.ofNat 64 i)
  stackBound : ∀ observation ∈ observations,
    s.sp.toNat - 416 ≤ observation.sp.toNat ∧ observation.sp.toNat ≤ s.sp.toNat ∧
    s.sp.toNat - 416 ≤ observation.nextSP.toNat ∧ observation.nextSP.toNat ≤ s.sp.toNat ∧
    observation.sp.toNat % 16 = 0 ∧ observation.nextSP.toNat % 16 = 0

theorem sha256_logical_safe (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    ∃ out observations, LogicalCallResult base s message authority out observations := by
  let view := logicalState base s message
  have inputs := permission_view_inputs base s message extent authority entry
  obtain ⟨out, returned, steps, state, nv, sp, pc, zero, running, digest, frame, _, observations, observed⟩ :=
    sha256_fetched base view message.bytes inputs
  have executed : runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) view = some out := by
    rw [← runWordsObserved_erases _ view, observed]
    rfl
  obtain ⟨known, knownObserved, confined, grants⟩ := logical_runWords_observed_authority base s message extent authority
    entry (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) out (whole_call_permitted _) executed running
  have same : known = observations := (Prod.mk.inj (Option.some.inj (knownObserved.symm.trans observed))).2
  subst known
  have path := whole_call_staticPath base view message.bytes inputs out executed running
  obtain ⟨fetches, fetchGrants⟩ := logical_observed_fetch_bounds base s message extent authority entry
    (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) out observations (whole_call_permitted _) path observed running
  have stableView : returnStable view = returnStable s := by cases s; rfl
  refine ⟨out, observations, returned, steps, observed, state.trans stableView, nv, sp, pc, zero, running,
    digest, ?_, confined, grants, fetches, fetchGrants, ?_⟩
  · intro p stackOutside outputOutside
    have cell := frame p stackOutside outputOutside
    exact (read8_of_cell p cell).trans (logicalMemory_read8 base s message p)
  · exact whole_call_observed_stack_bound _ view out observations observed entry.stackAvailable entry.stackAligned

end Crypto.ARM64.Imported
