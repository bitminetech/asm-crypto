import Proofs.ARM64.ImportedConcurrentCall
import Proofs.ARM64.ImportedSerialContract
import Proofs.ARM64.ImportedDynamicEnvironment
import Proofs.ARM64.ImportedInterleavingCore

namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Every event is paired with its actual scheduling boundary and its actual
instruction observation. This predicate says nothing about external steps
between invocation boundaries or the physical interpretation of access events. -/
def RaceFreeScheduledPath {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) :
    Nat → List (BitVec 32) → Arm64.State → List InstructionObservation → Prop
  | _, [], _, [] => True
  | tick, word :: rest, before, observation :: observations =>
      ¬DataRace (observedAccessEvent observation) (environment.event tick before) ∧
      match Arm64.decode word with
      | none => False
      | some instruction => RaceFreeScheduledPath environment (tick + 1) rest
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before)) observations
  | _, _, _, _ => False

theorem scheduled_path_race_free {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) {base : BitVec 64} {tick : Nat}
    {words : List (BitVec 32)} {before out : Arm64.State} {observations : List InstructionObservation}
    (scheduled : ScheduledWords environment base tick words before out observations)
    (safePath : EnvironmentSafePath environment tick words before)
    (localAccess : ∀ observation ∈ observations, CallAccess scope (observedAccessEvent observation)) :
    RaceFreeScheduledPath environment tick words before observations := by
  induction scheduled with
  | done => exact True.intro
  | @step tick word rest before out observations instruction decoded allowed beforeRunning fetched afterRunning globals tail ih =>
    have safe : enabled before ∧ EnvironmentAccess scope (environment.event tick before) ∧
        EnvironmentSafePath environment (tick + 1) rest
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick before)) := by
      simpa only [EnvironmentSafePath, decoded] using safePath
    simp only [RaceFreeScheduledPath, decoded]
    exact ⟨borrow_accesses_race_free scope _ _ (localAccess _ (by simp)) safe.2.1,
      ih safe.2.2 (fun observation present => localAccess observation (by simp [present]))⟩

theorem static_schedule_safe_path (base : BitVec 64) (s : Arm64.State) (extent : Nat)
    (environment : DynamicEnvironment base s extent) {tick : Nat} {words : List (BitVec 32)}
    {before out : Arm64.State} {observations : List InstructionObservation}
    (scheduled : ScheduledWords environment.static base tick words before out observations) :
    EnvironmentSafePath environment.static tick words before := by
  induction scheduled with
  | done => exact True.intro
  | @step tick word rest before out observations instruction decoded allowed beforeRunning fetched afterRunning globals tail ih =>
    simp only [EnvironmentSafePath, decoded]
    exact ⟨True.intro, environment.static.accesses tick before True.intro, ih⟩

theorem modeled_abi_of_projection (before serialBefore serialAfter after : Arm64.State)
    (entryCPU : CPUProjection serialBefore = CPUProjection before)
    (finalCPU : CPUProjection serialAfter = CPUProjection after)
    (abi : ModeledCPUABI serialBefore serialAfter) : ModeledCPUABI before after := by
  have readBefore (reg : Arm64.Reg) : serialBefore.readReg64 reg = before.readReg64 reg := by
    simpa only [projection_read64] using congrArg (fun state : Arm64.State => state.readReg64 reg) entryCPU
  have readAfter (reg : Arm64.Reg) : serialAfter.readReg64 reg = after.readReg64 reg := by
    simpa only [projection_read64] using congrArg (fun state : Arm64.State => state.readReg64 reg) finalCPU
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    exact (readAfter _).symm.trans ((congrFun abi.nonvolatile i).trans (readBefore _))
  · have initial := congrArg Arm64.State.sp entryCPU
    have final := congrArg Arm64.State.sp finalCPU
    simp only [projection_sp] at initial final
    exact final.symm.trans (abi.stack.trans initial)
  · have initial := congrArg Arm64.State.vregs entryCPU
    have final := congrArg Arm64.State.vregs finalCPU
    change serialBefore.vregs = before.vregs at initial
    change serialAfter.vregs = after.vregs at final
    exact final.symm.trans (abi.vectors.trans initial)
  · have initial := congrArg Arm64.State.fpsr entryCPU
    have final := congrArg Arm64.State.fpsr finalCPU
    change serialBefore.fpsr = before.fpsr at initial
    change serialAfter.fpsr = after.fpsr at final
    exact final.symm.trans (abi.fpsr.trans initial)
  · have initial := congrArg Arm64.State.tpidrEl0 entryCPU
    have final := congrArg Arm64.State.tpidrEl0 finalCPU
    change serialBefore.tpidrEl0 = before.tpidrEl0 at initial
    change serialAfter.tpidrEl0 = after.tpidrEl0 at final
    exact final.symm.trans (abi.threadPointer.trans initial)


theorem static_call_access_of_no_data (base : BitVec 64) (s : Arm64.State) (extent : Nat)
    (observation : InstructionObservation) (empty : observation.accesses = [])
    (fetches : ∀ byte, byte < 4 → (callerImage base).Contains (observation.pc + BitVec.ofNat 64 byte)) :
    CallAccess (staticBorrowScope base s extent) (observedAccessEvent observation) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro p (⟨i, bound, address⟩ | ⟨access, present, writing, i, bound, address⟩)
    · subst p
      exact Or.inl (Or.inr (fetches i bound))
    · rw [empty] at present
      contradiction
  · rintro p ⟨access, present, writing, i, bound, address⟩
    rw [empty] at present
    contradiction
  · intro p impossible; exact impossible
  · intro p impossible; exact impossible

theorem scheduled_single_no_data {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) {base : BitVec 64} {tick : Nat}
    (word : BitVec 32) (instruction : Arm64.Instr)
    {before out : Arm64.State} {observations : List InstructionObservation}
    (decoded : Arm64.decode word = some instruction)
    (empty : ∀ state, dataAccesses instruction state = [])
    (scheduled : ScheduledWords environment base tick [word] before out observations) :
    ∀ observation ∈ observations, observation.accesses = [] := by
  cases scheduled with
  | @step _ _ _ _ _ _ actual decodedActual allowed beforeRunning fetched afterRunning globals tail =>
    have same : actual = instruction := Option.some.inj (decodedActual.symm.trans decoded)
    subst actual
    cases tail
    intro observation member
    have same : observation = instructionObservation instruction (environment.advance tick before) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    subst observation
    exact empty _


theorem serial_contract_of_logical_result (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority) (fpcr : BitVec 32)
    (entry : PermissionViewInputs base s message extent authority)
    (out : Arm64.State) (observations : List InstructionObservation)
    (safe : LogicalCallResult base s message authority out observations) :
    SerialCallResult base s message extent authority fpcr out observations := by
  obtain ⟨knownOut, knownObs, result⟩ := sha256_serial_contract base s message extent authority fpcr entry
  have sameOut : knownOut = out := Option.some.inj (result.safe.returned.symm.trans safe.returned)
  subst knownOut
  have sameObs : knownObs = observations :=
    (Prod.mk.inj (Option.some.inj (result.safe.observed.symm.trans safe.observed))).2
  subst knownObs
  exact result

theorem scheduled_digest_from_static_cells (base : BitVec 64) (s serialOut actualOut : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat)
    (valid : (callerOutput s).Valid)
    (cells : SameCellsOn (staticBorrowScope base s extent).protected serialOut.mem actualOut.mem)
    (digest : memoryBytes32 serialOut.mem (s.readReg64 .x1) =
      (Crypto.Reference.sha256 message).2.map UInt8.toBitVec) :
    memoryBytes32 actualOut.mem (s.readReg64 .x1) =
      (Crypto.Reference.sha256 message).2.map UInt8.toBitVec := by
  have same : memoryBytes32 serialOut.mem (s.readReg64 .x1) =
      memoryBytes32 actualOut.mem (s.readReg64 .x1) := by
    apply Vector.ext
    intro i bound
    simp only [memoryBytes32, Vector.getElem_ofFn]
    exact read8_of_cell _ (cells _ (Or.inr (caller_region_contains_offset (callerOutput s) valid i bound)))
  exact same.symm.trans digest

/-- Guarantees of the constructed concurrent call, on its actual final CPU,
output bytes and common actual instruction observations. Unborrowed memory
and unrelated global state may advance under the environment. -/
structure ScheduledCallGuarantees (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) : Prop where
  cpuABI : ModeledCPUABI s call.schedule.actualOut
  stackRestored : call.schedule.actualOut.sp = s.sp
  returnAddress : call.schedule.actualOut.pc = s.readReg64 .x30
  status : call.schedule.actualOut.readReg64 .x0 = 0#64
  running : call.schedule.actualOut.status = .Running
  digest : memoryBytes32 call.schedule.actualOut.mem (s.readReg64 .x1) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  strictData : ObservedDataFootprint (strictReadFootprint base s message)
    (permissionWriteFootprint s) call.observations
  functionFetches : ∀ observation ∈ call.observations, ∀ byte, byte < 4 →
    (callerFunction base).Contains (observation.pc + BitVec.ofNat 64 byte)
  stackBound : ∀ observation ∈ call.observations,
    s.sp.toNat - 416 ≤ observation.sp.toNat ∧ observation.sp.toNat ≤ s.sp.toNat ∧
    s.sp.toNat - 416 ≤ observation.nextSP.toNat ∧ observation.nextSP.toNat ≤ s.sp.toNat ∧
    observation.sp.toNat % 16 = 0 ∧ observation.nextSP.toNat % 16 = 0
  stackAccess : ∀ observation ∈ call.observations, StackAccessNotBelowSP s observation
  observationLength : call.observations.length = (wholeCallCode (BitVec.ofNat 64 message.bytes.size)).length
  instructionBound : call.observations.length ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1)
  allocationRaceFree : RaceFreeScheduledPath environment.static 0 concurrentAllocateCode
    (logicalState base s message) call.schedule.allocationObservations
  activeRaceFree : RaceFreeScheduledPath environment.active 1
    (concurrentActiveCode (BitVec.ofNat 64 message.bytes.size)) call.schedule.allocated call.schedule.activeObservations
  returnRaceFree : RaceFreeScheduledPath environment.static
    (1 + (concurrentActiveCode (BitVec.ofNat 64 message.bytes.size)).length) concurrentReturnCode
    call.schedule.actualRestored call.schedule.returnObservations

theorem concurrent_call_guarantees (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (environment : DynamicEnvironment base s extent)
    (entry : PermissionViewInputs base s message extent authority)
    (call : ConcurrentCallCore base s message extent authority environment) :
    ScheduledCallGuarantees base s message extent authority environment call := by
  have certified := serial_contract_of_logical_result base s message extent authority 0#32 entry
    call.safeOut call.observations call.safe
  have initialCPU : CPUProjection (environment.advance 0 (logicalState base s message)) = CPUProjection s := by
    have original : CPUProjection (logicalState base s message) = CPUProjection s := by cases s; rfl
    exact call.rebasedCPU.trans original
  have abi := modeled_abi_of_projection s (environment.advance 0 (logicalState base s message))
    call.serialOut call.schedule.actualOut initialCPU call.schedule.cpu
    (modeled_cpu_abi _ _ call.serialState call.serialNV call.serialSP)
  have initialRead (reg : Arm64.Reg) :
      (environment.advance 0 (logicalState base s message)).readReg64 reg = s.readReg64 reg := by
    simpa only [projection_read64] using congrArg (fun state : Arm64.State => state.readReg64 reg) initialCPU
  have finalRead (reg : Arm64.Reg) : call.serialOut.readReg64 reg = call.schedule.actualOut.readReg64 reg := by
    simpa only [projection_read64] using congrArg (fun state : Arm64.State => state.readReg64 reg) call.schedule.cpu
  have finalPC : call.serialOut.pc = call.schedule.actualOut.pc := by
    simpa only [projection_pc] using congrArg Arm64.State.pc call.schedule.cpu
  have serialDigest : memoryBytes32 call.serialOut.mem (s.readReg64 .x1) =
      (Crypto.Reference.sha256 message).2.map UInt8.toBitVec := by
    exact (congrArg (memoryBytes32 call.serialOut.mem) (initialRead .x1)).symm.trans call.serialDigest
  have allocationMember (observation : InstructionObservation)
      (member : observation ∈ call.schedule.allocationObservations) : observation ∈ call.observations := by
    rw [call.schedule.observedSplit]
    exact List.mem_append.mpr (Or.inl member)
  have activeMember (observation : InstructionObservation)
      (member : observation ∈ call.schedule.activeObservations) : observation ∈ call.observations := by
    rw [call.schedule.observedSplit]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member)))
  have returnMember (observation : InstructionObservation)
      (member : observation ∈ call.schedule.returnObservations) : observation ∈ call.observations := by
    rw [call.schedule.observedSplit]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member)))
  have allocationEmpty := scheduled_single_no_data environment.static imageWords[0]!
    (.addSubImm .W64 .SUB .sp .sp 416#12 false) stack_allocate_decode (by intro state; rfl) call.schedule.allocation
  have returnEmpty := scheduled_single_no_data environment.static imageWords[150]!
    (.ret .x30) stack_return_decode (by intro state; rfl) call.schedule.returned
  refine ⟨abi, abi.stack, finalPC.symm.trans (call.serialPC.trans (initialRead .x30)),
    (finalRead .x0).symm.trans call.serialStatus, call.schedule.running,
    scheduled_digest_from_static_cells base s call.serialOut call.schedule.actualOut message extent
      entry.outputValid call.schedule.cells serialDigest,
    certified.strictData, certified.functionFetches, call.safe.stackBound, certified.stackAccess,
    call.schedule.countExact, certified.instructionBound, ?_, ?_, ?_⟩
  · apply scheduled_path_race_free environment.static call.schedule.allocation call.schedule.allocationSafe
    intro observation member
    exact static_call_access_of_no_data base s extent observation (allocationEmpty observation member)
      (call.safe.fetches observation (allocationMember observation member))
  · apply scheduled_path_race_free environment.active call.schedule.active call.schedule.activeSafe
    intro observation member
    exact observed_call_access base s message extent authority entry call.safeOut call.observations call.safe
      observation (activeMember observation member)
  · apply scheduled_path_race_free environment.static call.schedule.returned call.schedule.returnSafe
    intro observation member
    exact static_call_access_of_no_data base s extent observation (returnEmpty observation member)
      (call.safe.fetches observation (returnMember observation member))


theorem sha256_scheduled_guarantees (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent) :
    ∃ call : ConcurrentCallCore base s message extent authority environment,
      ScheduledCallGuarantees base s message extent authority environment call := by
  obtain ⟨call⟩ := sha256_concurrent_call_core base s message extent authority entry environment
  exact ⟨call, concurrent_call_guarantees base s message extent authority environment entry call⟩

end Crypto.ARM64.Imported
