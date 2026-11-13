import Proofs.ARM64.ImportedInterleavingCore
import Proofs.ARM64.ImportedRebasedCall

/-!
Construct the complete native scheduled SHA-256 call from typed caller facts.
The serial witness is rebased after the first environment boundary, so future
stack bytes may change before SUB. Full stack bytes are borrowed only through
the active prefix; after ADD restores SP, RET uses only static input/image/
digest borrows. Each native step retains its latest environment global tail.

The resulting schedule has the original safe observation list, exact code
length/budget and no early RET, with final projected CPU and static-cell
agreement. Allocation, active-prefix and return admissibility are explicit
witnesses. No execution, trace equality or digest result is a caller premise.
Physical/profile and independently pinned equal validation remain separate.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def concurrentActiveCode (count : BitVec 64) := stackMiddleCode count ++ [imageWords[149]!]
def concurrentAllocateCode := [imageWords[0]!]
def concurrentReturnCode := [imageWords[150]!]

theorem concurrent_code_shape (count : BitVec 64) : wholeCallCode count =
    concurrentAllocateCode ++ (concurrentActiveCode count ++ concurrentReturnCode) := by
  rw [whole_call_stack_shape]
  simp only [concurrentAllocateCode, concurrentActiveCode, concurrentReturnCode, List.append_assoc,
    List.cons_append, List.nil_append]

theorem concurrent_permitted_cast (left right : List (BitVec 32)) (equal : left = right)
    (permitted : PermittedWords left) : PermittedWords right := by cases equal; exact permitted

theorem concurrent_permitted_prefix (left right : List (BitVec 32)) (permitted : PermittedWords (left ++ right)) :
    PermittedWords left := by
  intro word member instruction decoded
  exact permitted word (List.mem_append.mpr (Or.inl member)) instruction decoded

theorem concurrent_permitted_suffix (left right : List (BitVec 32)) (permitted : PermittedWords (left ++ right)) :
    PermittedWords right := by
  intro word member instruction decoded
  exact permitted word (List.mem_append.mpr (Or.inr member)) instruction decoded

theorem concurrent_protected_cast (footprint : BitVec 64 → Prop) (left right : List (BitVec 32))
    (s : Arm64.State) (equal : left = right) (path : ProtectedPath footprint left s) :
    ProtectedPath footprint right s := by cases equal; exact path

theorem concurrent_enabled_cast (enabled : Arm64.State → Prop) (left right : List (BitVec 32))
    (s : Arm64.State) (equal : left = right) (path : EnabledPath enabled left s) :
    EnabledPath enabled right s := by cases equal; exact path

theorem concurrent_scheduled_cast {scope : BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (base : BitVec 64) (tick : Nat)
    (left right : List (BitVec 32)) (before out : Arm64.State) (observations : List InstructionObservation)
    (equal : left = right) (scheduled : ScheduledWords environment base tick left before out observations) :
    ScheduledWords environment base tick right before out observations := by cases equal; exact scheduled

theorem concurrent_single_exec (word : BitVec 32) (instruction : Arm64.Instr) (s : Arm64.State)
    (decoded : Arm64.decode word = some instruction) :
    runWords [word] s = some (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
  simp only [runWords, decoded, Option.bind_some]

theorem concurrent_single_observed (word : BitVec 32) (instruction : Arm64.Instr) (s : Arm64.State)
    (decoded : Arm64.decode word = some instruction) :
    runWordsObserved [word] s = some (Arm64.execInstWithSvc Arm64.noSyscalls instruction s,
      [instructionObservation instruction s]) := by
  simp only [runWordsObserved, decoded, Bind.bind, Option.bind, pure, Pure.pure]

theorem concurrent_static_full (base : BitVec 64) (s : Arm64.State) (extent : Nat) (p : BitVec 64)
    (inside : (staticBorrowScope base s extent).protected p) : (shaBorrowScope base s extent).protected p := by
  rcases inside with (input | image) | output
  · exact Or.inl (Or.inl input)
  · exact Or.inl (Or.inr image)
  · exact Or.inr (Or.inl output)

theorem concurrent_return_protected (footprint : BitVec 64 → Prop) (s : Arm64.State) :
    ProtectedPath footprint concurrentReturnCode s := by
  simp [concurrentReturnCode, ProtectedPath, stack_return_decode, ProtectedAccesses, dataAccesses]

theorem concurrent_active_restores (count : BitVec 64) (original allocated restored : Arm64.State)
    (bottom : allocated.sp = entryStack original)
    (executed : runWords (concurrentActiveCode count) allocated = some restored) : restored.sp = original.sp := by
  have expanded := runWords_code_cast (concurrentActiveCode count)
    (stackMiddleCode count ++ [imageWords[149]!]) allocated restored rfl executed
  obtain ⟨middle, middleExec, restoreExec⟩ := runWords_append_split (stackMiddleCode count)
    [imageWords[149]!] allocated restored expanded
  obtain ⟨observations, observed⟩ := runWords_observed (stackMiddleCode count) allocated middle middleExec
  have stack := (runWordsObserved_stack_preserved (stackMiddleCode count) allocated middle observations
    (stack_middle_preserving count) observed).1
  have known := concurrent_single_exec imageWords[149]! (.addSubImm .W64 .ADD .sp .sp 416#12 false) middle stack_restore_decode
  have state := Option.some.inj (restoreExec.symm.trans known)
  rw [state, stack_restore_sp, stack, bottom]
  exact BitVec.sub_add_cancel _ _

structure ConcurrentScheduleWitness (base : BitVec 64) (original : Arm64.State) (extent : Nat)
    (environment : DynamicEnvironment base original extent) (count : BitVec 64)
    (view serialStart serialOut : Arm64.State) (observations : List InstructionObservation) where
  allocated : Arm64.State
  serialRestored : Arm64.State
  actualRestored : Arm64.State
  actualOut : Arm64.State
  activeObservations : List InstructionObservation
  allocationObservations : List InstructionObservation
  returnObservations : List InstructionObservation
  allocatedSP : allocated.sp = entryStack original
  serialRestoredSP : serialRestored.sp = original.sp
  actualRestoredSP : actualRestored.sp = original.sp
  allocation : ScheduledWords environment.static base 0 concurrentAllocateCode view allocated allocationObservations
  allocationSafe : EnvironmentSafePath environment.static 0 concurrentAllocateCode view
  active : ScheduledWords environment.active base 1 (concurrentActiveCode count) allocated actualRestored activeObservations
  activeSafe : EnvironmentSafePath environment.active 1 (concurrentActiveCode count) allocated
  returned : ScheduledWords environment.static base (1 + (concurrentActiveCode count).length)
    concurrentReturnCode actualRestored actualOut returnObservations
  returnSafe : EnvironmentSafePath environment.static (1 + (concurrentActiveCode count).length)
    concurrentReturnCode actualRestored
  observedSplit : observations = allocationObservations ++ (activeObservations ++ returnObservations)
  scheduled : ScheduledWords environment.static base 0 (wholeCallCode count) view actualOut observations
  cpu : CPUProjection serialOut = CPUProjection actualOut
  cells : SameCellsOn (staticBorrowScope base original extent).protected serialOut.mem actualOut.mem
  running : actualOut.status = .Running
  countExact : observations.length = (wholeCallCode count).length
  noEarlyReturn : NoReturns (wholeCallBeforeReturnCode count)

/-- Assemble allocation, the active frame phase, and RET under the same
physical scheduling function while applying each phase's separate borrow law. -/
theorem concurrent_schedule_from_serial (base : BitVec 64) (original : Arm64.State) (extent : Nat)
    (environment : DynamicEnvironment base original extent) (count : BitVec 64)
    (view serialStart serialOut : Arm64.State) (observations : List InstructionObservation)
    (advanced : serialStart = environment.advance 0 view)
    (entrySP : serialStart.sp = original.sp)
    (loaded : (program base).CodeLoaded serialStart.mem)
    (codeProtectedStatic : ∀ i, i < (program base).code.length →
      (staticBorrowScope base original extent).protected (base + BitVec.ofNat 64 i))
    (executed : runWords (wholeCallCode count) serialStart = some serialOut)
    (observed : runWordsObserved (wholeCallCode count) serialStart = some (serialOut, observations))
    (path : StaticPath base (wholeCallCode count) serialStart)
    (protectedPath : ProtectedPath (shaBorrowScope base original extent).protected (wholeCallCode count) serialStart)
    (running : serialOut.status = .Running) :
    Nonempty (ConcurrentScheduleWitness base original extent environment count view serialStart serialOut observations) := by
  let allocate : Arm64.Instr := .addSubImm .W64 .SUB .sp .sp 416#12 false
  let allocated := Arm64.execInstWithSvc Arm64.noSyscalls allocate serialStart
  have allocateAllowed : permittedInstruction allocate = true := by rfl
  have allocateExec : runWords concurrentAllocateCode serialStart = some allocated :=
    concurrent_single_exec imageWords[0]! allocate serialStart stack_allocate_decode
  have allocateObserved : runWordsObserved concurrentAllocateCode serialStart =
      some (allocated, [instructionObservation allocate serialStart]) :=
    concurrent_single_observed imageWords[0]! allocate serialStart stack_allocate_decode
  have expanded := runWords_code_cast (wholeCallCode count)
    (concurrentAllocateCode ++ (concurrentActiveCode count ++ concurrentReturnCode)) serialStart serialOut
    (concurrent_code_shape count) executed
  have restExec := padding_runWords_suffix concurrentAllocateCode (concurrentActiveCode count ++ concurrentReturnCode)
    serialStart allocated serialOut allocateExec expanded
  obtain ⟨serialRestored, activeExec, returnExec⟩ := runWords_append_split (concurrentActiveCode count)
    concurrentReturnCode allocated serialOut restExec
  have permittedExpanded := concurrent_permitted_cast _ _ (concurrent_code_shape count) (whole_call_permitted count)
  have permittedRest := concurrent_permitted_suffix concurrentAllocateCode
    (concurrentActiveCode count ++ concurrentReturnCode) permittedExpanded
  have permittedActive := concurrent_permitted_prefix (concurrentActiveCode count) concurrentReturnCode permittedRest
  have permittedReturn := concurrent_permitted_suffix (concurrentActiveCode count) concurrentReturnCode permittedRest
  have allocatedRunning := runWords_running_before (concurrentActiveCode count ++ concurrentReturnCode)
    allocated serialOut permittedRest restExec running
  have sourceRunning := permitted_running_before allocate allocateAllowed serialStart allocatedRunning
  have allocatedSP : allocated.sp = entryStack original := by
    rw [stack_allocate_sp, entrySP]
    rfl
  have pathExpanded := @StaticPath.of_code_eq base serialStart
    (concurrentAllocateCode ++ (concurrentActiveCode count ++ concurrentReturnCode)) (wholeCallCode count)
    (concurrent_code_shape count).symm path
  have allocationPath := StaticPath.prefix concurrentAllocateCode
    (concurrentActiveCode count ++ concurrentReturnCode) serialStart pathExpanded
  have sourceFetch : (program base).fetch serialStart.pc = some allocate := by
    simpa only [concurrentAllocateCode, StaticPath, stack_allocate_decode, and_true] using allocationPath
  have sourceMemoryFetch := loaded_fetch_of_fetch loaded sourceFetch
  have allocationRun : ScheduledWords environment.static base 0 concurrentAllocateCode view allocated
      [instructionObservation allocate serialStart] := by
    have atAdvanced : environment.static.advance 0 view = serialStart := advanced.symm
    have native : ScheduledWords environment.static base 0 [imageWords[0]!] view
        (Arm64.execInstWithSvc Arm64.noSyscalls allocate (environment.static.advance 0 view))
        [instructionObservation allocate (environment.static.advance 0 view)] :=
      ScheduledWords.step (environment := environment.static) (base := base) (tick := 0)
        (word := imageWords[0]!) (rest := []) (before := view)
        (out := Arm64.execInstWithSvc Arm64.noSyscalls allocate (environment.static.advance 0 view))
        (observations := []) (instruction := allocate) stack_allocate_decode allocateAllowed
        (by simpa only [atAdvanced] using sourceRunning) (by simpa only [atAdvanced] using sourceMemoryFetch)
        (by simpa only [atAdvanced] using allocatedRunning)
        (permitted_global_tail allocate allocateAllowed _)
        (ScheduledWords.done 1 _)
    simpa only [atAdvanced] using native
  have allocationSafe : EnvironmentSafePath environment.static 0 concurrentAllocateCode view := by
    simp only [EnvironmentSafePath, concurrentAllocateCode, stack_allocate_decode]
    exact ⟨True.intro, environment.staticAccesses 0 view, True.intro⟩
  have allocatedLoaded := permitted_codeLoaded allocate allocateAllowed serialStart loaded
  have restPath := StaticPath.suffix concurrentAllocateCode (concurrentActiveCode count ++ concurrentReturnCode)
    serialStart allocated allocateExec pathExpanded
  have activePath := StaticPath.prefix (concurrentActiveCode count) concurrentReturnCode allocated restPath
  have returnPath := StaticPath.suffix (concurrentActiveCode count) concurrentReturnCode
    allocated serialRestored activeExec restPath
  have protectedExpanded := concurrent_protected_cast _ _ _ serialStart (concurrent_code_shape count) protectedPath
  have protectedRest := ProtectedPath.suffix _ concurrentAllocateCode
    (concurrentActiveCode count ++ concurrentReturnCode) serialStart allocated allocateExec protectedExpanded
  have protectedActive := ProtectedPath.prefix _ (concurrentActiveCode count) concurrentReturnCode allocated protectedRest
  have expandedActive := runWords_code_cast (concurrentActiveCode count)
    (stackMiddleCode count ++ [imageWords[149]!]) allocated serialRestored rfl activeExec
  have enabledActive := concurrent_enabled_cast (stackActive original)
    (stackMiddleCode count ++ [imageWords[149]!]) (concurrentActiveCode count) allocated rfl
    (enabled_preserving_then_last original allocated serialRestored (stackMiddleCode count) imageWords[149]!
      (stack_middle_preserving count) allocatedSP expandedActive)
  have codeProtectedFull (i : Nat) (hi : i < (program base).code.length) :
      (shaBorrowScope base original extent).protected (base + BitVec.ofNat 64 i) :=
    concurrent_static_full base original extent _ (codeProtectedStatic i hi)
  have serialRestoredRunning := runWords_running_before concurrentReturnCode serialRestored serialOut permittedReturn returnExec running
  obtain ⟨actualRestored, activeObservations, activeRun, activeObserved, restoredCPU, restoredCells, actualRestoredRunning, activeSafe⟩ :=
    schedule_serial_words_safe environment.active (stackActive_cpu_invariant original) base codeProtectedFull
      (concurrentActiveCode count) 1 allocated serialRestored allocated rfl (by intro p hp; rfl)
      allocatedLoaded permittedActive activePath activeExec serialRestoredRunning enabledActive protectedActive
  have restoredSP := concurrent_active_restores count original allocated serialRestored allocatedSP activeExec
  have actualRestoredSP : actualRestored.sp = original.sp := by
    have equal := congrArg Arm64.State.sp restoredCPU
    simpa only [projection_sp, restoredSP] using equal.symm
  have activeCanonical := ScheduledWords.rebind environment.active environment.static rfl activeRun
  have staticCells : SameCellsOn (staticBorrowScope base original extent).protected serialRestored.mem actualRestored.mem := by
    intro p hp
    exact restoredCells p (concurrent_static_full base original extent p hp)
  have restoredLoaded := runWords_codeLoaded (concurrentActiveCode count) allocated serialRestored
    permittedActive allocatedLoaded activeExec
  obtain ⟨actualOut, returnObservations, returnRun, returnObserved, paired, finalCells, actualRunning, returnSafe⟩ :=
    schedule_serial_words_safe environment.static always_enabled_cpu_invariant base codeProtectedStatic
      concurrentReturnCode (1 + (concurrentActiveCode count).length) serialRestored serialOut actualRestored
      restoredCPU staticCells restoredLoaded permittedReturn returnPath returnExec running
      (enabled_true_path concurrentReturnCode serialRestored serialOut returnExec)
      (concurrent_return_protected _ serialRestored)
  have suffixRun := ScheduledWords.append activeCanonical returnRun
  have combined := ScheduledWords.append allocationRun suffixRun
  have combinedShape : ScheduledWords environment.static base 0 (wholeCallCode count) view actualOut
      ([instructionObservation allocate serialStart] ++ (activeObservations ++ returnObservations)) :=
    concurrent_scheduled_cast environment.static base 0
      (concurrentAllocateCode ++ (concurrentActiveCode count ++ concurrentReturnCode)) (wholeCallCode count)
      view actualOut _ (concurrent_code_shape count).symm combined
  have observedSuffix := runWordsObserved_append_success (concurrentActiveCode count) concurrentReturnCode
    allocated serialRestored serialOut activeObservations returnObservations activeObserved returnObserved
  have observedCombined := runWordsObserved_append_success concurrentAllocateCode
    (concurrentActiveCode count ++ concurrentReturnCode) serialStart allocated serialOut
    [instructionObservation allocate serialStart] (activeObservations ++ returnObservations) allocateObserved observedSuffix
  have originalObserved := runWordsObserved_code_cast
    (concurrentAllocateCode ++ (concurrentActiveCode count ++ concurrentReturnCode)) (wholeCallCode count)
    serialStart serialOut _ (concurrent_code_shape count).symm observedCombined
  have sameTrace : [instructionObservation allocate serialStart] ++ (activeObservations ++ returnObservations) = observations :=
    (Prod.mk.inj (Option.some.inj (originalObserved.symm.trans observed))).2
  have wholeRun : ScheduledWords environment.static base 0 (wholeCallCode count) view actualOut observations := by
    rw [sameTrace] at combinedShape
    exact combinedShape
  exact ⟨⟨allocated, serialRestored, actualRestored, actualOut, activeObservations,
    [instructionObservation allocate serialStart], returnObservations, allocatedSP, restoredSP, actualRestoredSP,
    allocationRun, allocationSafe, activeRun, activeSafe, returnRun, returnSafe, sameTrace.symm, wholeRun,
    paired, finalCells, actualRunning, wholeRun.length, (whole_call_without_return count).2⟩⟩

def concurrentSerialStart {base : BitVec 64} {s : Arm64.State} {extent : Nat}
    (environment : DynamicEnvironment base s extent) (message : Crypto.Reference.ByteList) : Arm64.State :=
  environment.advance 0 (logicalState base s message)

structure ConcurrentCallCore (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (environment : DynamicEnvironment base s extent) where
  safeOut : Arm64.State
  observations : List InstructionObservation
  safe : LogicalCallResult base s message authority safeOut observations
  serialOut : Arm64.State
  serialExecuted : runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
    (concurrentSerialStart environment message) = some serialOut
  serialObserved : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
    (concurrentSerialStart environment message) = some (serialOut, observations)
  serialPath : StaticPath base (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (concurrentSerialStart environment message)
  serialProtected : ProtectedPath (shaBorrowScope base s extent).protected
    (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (concurrentSerialStart environment message)
  serialRunning : serialOut.status = .Running
  serialState : returnStable serialOut = returnStable (concurrentSerialStart environment message)
  serialNV : nonvolatile serialOut = nonvolatile (concurrentSerialStart environment message)
  serialSP : serialOut.sp = (concurrentSerialStart environment message).sp
  serialPC : serialOut.pc = (concurrentSerialStart environment message).readReg64 .x30
  serialStatus : serialOut.readReg64 .x0 = 0#64
  serialDigest : memoryBytes32 serialOut.mem ((concurrentSerialStart environment message).readReg64 .x1) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  rebasedCPU : CPUProjection (concurrentSerialStart environment message) = CPUProjection (logicalState base s message)
  schedule : ConcurrentScheduleWitness base s extent environment (BitVec.ofNat 64 message.bytes.size)
    (logicalState base s message) (concurrentSerialStart environment message) serialOut observations
  budget : observations.length ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1)

theorem concurrent_call_core_of_safe (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (environment : DynamicEnvironment base s extent)
    (safeOut : Arm64.State) (observations : List InstructionObservation)
    (safe : LogicalCallResult base s message authority safeOut observations) :
    Nonempty (ConcurrentCallCore base s message extent authority environment) := by
  let view := logicalState base s message
  let start := concurrentSerialStart environment message
  have cpu : CPUProjection start = CPUProjection view := environment.cpu 0 view
  have cells : SameCellsOn (entryProtected base s extent) start.mem view.mem := by
    intro p hp
    exact (environment.staticCells 0 view p hp).symm
  have stack := environment.reservation 0 view (permission_view_entry_stack_grants base s message extent authority entry)
  obtain ⟨serialOut, executed, observed, path, protectedPath, running, state, nv, sp, pc, zero, digest⟩ :=
    rebased_native_call base s start message extent authority entry cpu cells stack safeOut observations safe
  have inputs := permission_view_entry_interference_projected base s start message extent authority entry cpu cells stack
  have startSP : start.sp = s.sp := by
    have equal := congrArg Arm64.State.sp cpu
    exact equal
  have protectedCode (i : Nat) (hi : i < (program base).code.length) :
      (staticBorrowScope base s extent).protected (base + BitVec.ofNat 64 i) := by
    have small : i < 896 := by rwa [program_code_length] at hi
    exact Or.inl (Or.inr (caller_region_contains_offset (callerImage base) entry.imageValid i small))
  obtain ⟨schedule⟩ := concurrent_schedule_from_serial base s extent environment (BitVec.ofNat 64 message.bytes.size)
    view start serialOut observations rfl startSP inputs.loaded protectedCode executed observed path protectedPath running
  have size64 : message.bytes.size < 2 ^ 64 := by have := entry.length; omega
  have wordBound := whole_call_code_bound (BitVec.ofNat 64 message.bytes.size)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt size64] at wordBound
  have budget : observations.length ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by
    rw [schedule.countExact]
    exact wordBound
  exact ⟨{
    safeOut := safeOut
    observations := observations
    safe := safe
    serialOut := serialOut
    serialExecuted := executed
    serialObserved := observed
    serialPath := path
    serialProtected := protectedPath
    serialRunning := running
    serialState := state
    serialNV := nv
    serialSP := sp
    serialPC := pc
    serialStatus := zero
    serialDigest := digest
    rebasedCPU := cpu
    schedule := schedule
    budget := budget }⟩

/-- All serial and scheduled witnesses are derived from the original typed
caller facts and the phase-sensitive environment laws. -/
theorem sha256_concurrent_call_core (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent) :
    Nonempty (ConcurrentCallCore base s message extent authority environment) := by
  obtain ⟨safeOut, observations, safe⟩ := sha256_logical_safe base s message extent authority entry
  exact concurrent_call_core_of_safe base s message extent authority entry environment safeOut observations safe

end Crypto.ARM64.Imported
