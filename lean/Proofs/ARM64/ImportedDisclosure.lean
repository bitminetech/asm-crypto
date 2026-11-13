import Proofs.ARM64.ImportedSafeCall

/-!
Permitted final-byte disclosures for the logical SHA-256 call. Equal public
context, public pre-bytes and permitted reference digests imply equal final
read8 observations outside the used payload and private 416-byte stack,
including every one of the 32 digest bytes. Prior payload, stack and digest
bytes need not agree. Status, execution status, return PC and restored SP are
also compared.
This observation excludes private stack/payload bytes, private caller-clobbered
registers and memory permission/ghost metadata. It asserts no zeroization,
physical timing or additional noninterference assumption. The constructive
corollary obtains actual LogicalCallResults from both valid permission views.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure SameDisclosureContext (left right : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) : Prop where
  input : left.readReg64 .x0 = right.readReg64 .x0
  output : left.readReg64 .x1 = right.readReg64 .x1
  stack : left.sp = right.sp
  link : left.readReg64 .x30 = right.readReg64 .x30
  offset : leftMessage.offset = rightMessage.offset
  count : leftMessage.bytes.size = rightMessage.bytes.size

theorem SameDisclosureContext.payload {left right : Arm64.State}
    {leftMessage rightMessage : Crypto.Reference.ByteList}
    (context : SameDisclosureContext left right leftMessage rightMessage) :
    callerPayload left leftMessage = callerPayload right rightMessage := by
  simp only [callerPayload, context.input, context.offset, context.count]

theorem SameDisclosureContext.stackRegion {left right : Arm64.State}
    {leftMessage rightMessage : Crypto.Reference.ByteList}
    (context : SameDisclosureContext left right leftMessage rightMessage) : callerStack left = callerStack right := by
  simp only [callerStack, entryStack, context.stack]

theorem SameDisclosureContext.outputRegion {left right : Arm64.State}
    {leftMessage rightMessage : Crypto.Reference.ByteList}
    (context : SameDisclosureContext left right leftMessage rightMessage) : callerOutput left = callerOutput right := by
  simp only [callerOutput, context.output]

def ByteObservable (s : Arm64.State) (message : Crypto.Reference.ByteList) (p : BitVec 64) : Prop :=
  ¬(callerPayload s message).Contains p ∧ ¬(callerStack s).Contains p

def PublicPreBytesAgree (left right : Arm64.State) (leftMessage : Crypto.Reference.ByteList) : Prop :=
  ∀ p, ByteObservable left leftMessage p → ¬(callerOutput left).Contains p →
    left.mem.read8 p = right.mem.read8 p

structure FinalByteObservationAgree (left right leftOut rightOut : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) : Prop where
  domain : ∀ p, ByteObservable left leftMessage p ↔ ByteObservable right rightMessage p
  status : leftOut.readReg64 .x0 = rightOut.readReg64 .x0
  executionStatus : leftOut.status = rightOut.status
  pc : leftOut.pc = rightOut.pc
  sp : leftOut.sp = rightOut.sp
  outputBytes : ∀ p, (callerOutput left).Contains p → leftOut.mem.read8 p = rightOut.mem.read8 p
  bytes : ∀ p, ByteObservable left leftMessage p → leftOut.mem.read8 p = rightOut.mem.read8 p

theorem SameDisclosureContext.observable {left right : Arm64.State}
    {leftMessage rightMessage : Crypto.Reference.ByteList}
    (context : SameDisclosureContext left right leftMessage rightMessage) (p : BitVec 64) :
    ByteObservable left leftMessage p ↔ ByteObservable right rightMessage p := by
  simp only [ByteObservable, context.payload, context.stackRegion]

theorem disclosure_region_offset (region : Region) (p : BitVec 64) (inside : region.Contains p) :
    ∃ i : Fin region.bytes, p = region.base + BitVec.ofNat 64 i.val := by
  let offset := p.toNat - region.base.toNat
  have bound : offset < region.bytes := by unfold Region.Contains at inside; dsimp [offset]; omega
  have offset64 : offset < 2 ^ 64 := by have := p.isLt; dsimp [offset]; omega
  have sum : region.base.toNat + offset = p.toNat := by unfold Region.Contains at inside; dsimp [offset]; omega
  have sum64 : region.base.toNat + offset < 2 ^ 64 := by rw [sum]; exact p.isLt
  refine ⟨⟨offset, bound⟩, ?_⟩
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offset64, Nat.mod_eq_of_lt sum64]
  exact sum.symm

theorem disclosure_memoryBytes32_point (left right : Arm64.Memory) (leftBase rightBase : BitVec 64)
    (same : memoryBytes32 left leftBase = memoryBytes32 right rightBase) (i : Fin 32) :
    left.read8 (leftBase + BitVec.ofNat 64 i.val) = right.read8 (rightBase + BitVec.ofNat 64 i.val) := by
  have point := congrArg (fun bytes : Vector (BitVec 8) 32 => bytes[i.val]!) same
  simpa [memoryBytes32, i.isLt] using point

theorem logical_results_digest_bytes (base : BitVec 64) (left right leftOut rightOut : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftAuthority rightAuthority : Authority)
    (leftObs rightObs : List InstructionObservation)
    (leftResult : LogicalCallResult base left leftMessage leftAuthority leftOut leftObs)
    (rightResult : LogicalCallResult base right rightMessage rightAuthority rightOut rightObs)
    (digestEqual : (Crypto.Reference.sha256 leftMessage).2 = (Crypto.Reference.sha256 rightMessage).2) :
    memoryBytes32 leftOut.mem (left.readReg64 .x1) = memoryBytes32 rightOut.mem (right.readReg64 .x1) := by
  rw [leftResult.digest, rightResult.digest, digestEqual]

theorem logical_results_output_bytes (base : BitVec 64) (left right leftOut rightOut : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftAuthority rightAuthority : Authority)
    (leftObs rightObs : List InstructionObservation)
    (leftResult : LogicalCallResult base left leftMessage leftAuthority leftOut leftObs)
    (rightResult : LogicalCallResult base right rightMessage rightAuthority rightOut rightObs)
    (outputEqual : left.readReg64 .x1 = right.readReg64 .x1)
    (digestEqual : (Crypto.Reference.sha256 leftMessage).2 = (Crypto.Reference.sha256 rightMessage).2) :
    ∀ p, (callerOutput left).Contains p → leftOut.mem.read8 p = rightOut.mem.read8 p := by
  have digest := logical_results_digest_bytes base left right leftOut rightOut leftMessage rightMessage
    leftAuthority rightAuthority leftObs rightObs leftResult rightResult digestEqual
  intro p inside
  obtain ⟨i, address⟩ := disclosure_region_offset (callerOutput left) p inside
  have point := disclosure_memoryBytes32_point leftOut.mem rightOut.mem (left.readReg64 .x1) (right.readReg64 .x1) digest i
  change p = left.readReg64 .x1 + BitVec.ofNat 64 i.val at address
  rw [← outputEqual] at point
  rw [address]
  exact point

theorem logical_results_disclosure (base : BitVec 64) (left right leftOut rightOut : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
    (leftAuthority rightAuthority : Authority) (leftObs rightObs : List InstructionObservation)
    (leftEntry : PermissionViewInputs base left leftMessage leftExtent leftAuthority)
    (rightEntry : PermissionViewInputs base right rightMessage rightExtent rightAuthority)
    (context : SameDisclosureContext left right leftMessage rightMessage)
    (publicBytes : PublicPreBytesAgree left right leftMessage)
    (digestEqual : (Crypto.Reference.sha256 leftMessage).2 = (Crypto.Reference.sha256 rightMessage).2)
    (leftResult : LogicalCallResult base left leftMessage leftAuthority leftOut leftObs)
    (rightResult : LogicalCallResult base right rightMessage rightAuthority rightOut rightObs) :
    FinalByteObservationAgree left right leftOut rightOut leftMessage rightMessage := by
  have outputBytes := logical_results_output_bytes base left right leftOut rightOut leftMessage rightMessage
    leftAuthority rightAuthority leftObs rightObs leftResult rightResult context.output digestEqual
  refine ⟨context.observable, leftResult.status.trans rightResult.status.symm,
    leftResult.running.trans rightResult.running.symm, ?_, ?_, outputBytes, ?_⟩
  · exact leftResult.returnAddress.trans (context.link.trans rightResult.returnAddress.symm)
  · exact leftResult.stackRestored.trans (context.stack.trans rightResult.stackRestored.symm)
  · intro p observable
    by_cases output : (callerOutput left).Contains p
    · exact outputBytes p output
    · have rightObservable := (context.observable p).mp observable
      have rightOutput : ¬(callerOutput right).Contains p := by rw [← context.outputRegion]; exact output
      have leftFrame := leftResult.finalMemory p
        (caller_outside_delta (callerStack left) leftEntry.stackValid p observable.2)
        (caller_outside_delta (callerOutput left) leftEntry.outputValid p output)
      have rightFrame := rightResult.finalMemory p
        (caller_outside_delta (callerStack right) rightEntry.stackValid p rightObservable.2)
        (caller_outside_delta (callerOutput right) rightEntry.outputValid p rightOutput)
      exact leftFrame.trans ((publicBytes p observable output).trans rightFrame.symm)

theorem sha256_logical_disclosure (base : BitVec 64) (left right : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
    (leftAuthority rightAuthority : Authority)
    (leftEntry : PermissionViewInputs base left leftMessage leftExtent leftAuthority)
    (rightEntry : PermissionViewInputs base right rightMessage rightExtent rightAuthority)
    (context : SameDisclosureContext left right leftMessage rightMessage)
    (publicBytes : PublicPreBytesAgree left right leftMessage)
    (digestEqual : (Crypto.Reference.sha256 leftMessage).2 = (Crypto.Reference.sha256 rightMessage).2) :
    ∃ leftOut rightOut leftObs rightObs,
      LogicalCallResult base left leftMessage leftAuthority leftOut leftObs ∧
      LogicalCallResult base right rightMessage rightAuthority rightOut rightObs ∧
      FinalByteObservationAgree left right leftOut rightOut leftMessage rightMessage := by
  obtain ⟨leftOut, leftObs, leftResult⟩ := sha256_logical_safe base left leftMessage leftExtent leftAuthority leftEntry
  obtain ⟨rightOut, rightObs, rightResult⟩ := sha256_logical_safe base right rightMessage rightExtent rightAuthority rightEntry
  exact ⟨leftOut, rightOut, leftObs, rightObs, leftResult, rightResult,
    logical_results_disclosure base left right leftOut rightOut leftMessage rightMessage leftExtent rightExtent
      leftAuthority rightAuthority leftObs rightObs leftEntry rightEntry context publicBytes digestEqual leftResult rightResult⟩

end Crypto.ARM64.Imported
