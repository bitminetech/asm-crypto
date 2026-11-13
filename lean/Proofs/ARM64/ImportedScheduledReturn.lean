import Proofs.ARM64.ImportedConcurrentCall

/-!
Actual bounded scheduled execution for the SHA-256 call. The evaluator fetches
from current memory, evaluates the fetched instruction, and stops at the first
RET; it receives no instruction tape. Scheduling takes place before every
instruction, including the initial allocation and final return. Its SHA-256
correctness follows from the caller-derived concurrent schedule and the proved
absence of an earlier RET. Observation completeness is used only for the
permitted SHA-256 forms, through `scheduledObservation_permitted`.
-/

namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def scheduledObservation (prog : Arm64.Program) (instruction : Arm64.Instr) (s : Arm64.State) : InstructionObservation :=
  let after := prog.evalInst instruction s
  ⟨s.pc, after.pc, s.sp, after.sp, dataAccesses instruction s⟩

/-- Execute through actual memory fetch/evaluation, with one finite scheduling
boundary before each instruction. Exhaustion/fault fails; the first RET stops. -/
def runScheduledToReturn (prog : Arm64.Program) (advance : Nat → Arm64.State → Arm64.State) :
    Nat → Nat → Arm64.State → Option (Arm64.State × List InstructionObservation)
  | 0, _, _ => none
  | fuel + 1, tick, s =>
    let before := advance tick s
    if before.status ≠ .Running then none else do
      let instruction ← prog.fetchMem before.mem before.pc
      let after := prog.evalInst instruction before
      if after.status ≠ .Running then none else
        let observation := scheduledObservation prog instruction before
        match instruction with
        | .ret _ => some (after, [observation])
        | _ => do
          let (out, observations) ← runScheduledToReturn prog advance fuel (tick + 1) after
          pure (out, observation :: observations)

def runScheduledStateToReturn (prog : Arm64.Program) (advance : Nat → Arm64.State → Arm64.State)
    (fuel tick : Nat) (s : Arm64.State) : Option Arm64.State :=
  (runScheduledToReturn prog advance fuel tick s).map Prod.fst

theorem scheduledObservation_permitted (base : BitVec 64) (instruction : Arm64.Instr)
    (allowed : permittedInstruction instruction = true) (s : Arm64.State) :
    scheduledObservation (program base) instruction s = instructionObservation instruction s := by
  unfold scheduledObservation instructionObservation
  rw [evalInst_permitted base instruction allowed s]

theorem runScheduledToReturn_nonret (prog : Arm64.Program) (advance : Nat → Arm64.State → Arm64.State)
    (fuel tick : Nat) (s : Arm64.State) (instruction : Arm64.Instr)
    (running : (advance tick s).status = .Running)
    (fetched : prog.fetchMem (advance tick s).mem (advance tick s).pc = some instruction)
    (afterRunning : (prog.evalInst instruction (advance tick s)).status = .Running)
    (notReturn : ∀ r, instruction ≠ .ret r) :
    runScheduledToReturn prog advance (fuel + 1) tick s =
      (runScheduledToReturn prog advance fuel (tick + 1) (prog.evalInst instruction (advance tick s))).map
        (fun result => (result.1, scheduledObservation prog instruction (advance tick s) :: result.2)) := by
  cases instruction <;> simp_all [runScheduledToReturn, Option.map_eq_bind]

theorem runScheduledToReturn_ret (prog : Arm64.Program) (advance : Nat → Arm64.State → Arm64.State)
    (fuel tick : Nat) (s : Arm64.State) (r : Arm64.Reg)
    (running : (advance tick s).status = .Running)
    (fetched : prog.fetchMem (advance tick s).mem (advance tick s).pc = some (.ret r))
    (afterRunning : (prog.evalInst (.ret r) (advance tick s)).status = .Running) :
    runScheduledToReturn prog advance (fuel + 1) tick s =
      some (prog.evalInst (.ret r) (advance tick s), [scheduledObservation prog (.ret r) (advance tick s)]) := by
  simp [runScheduledToReturn, running, fetched, afterRunning]

theorem runScheduledToReturn_of_schedule {scope : Crypto.Baseline.BorrowScope} {enabled : Arm64.State → Prop}
    (environment : BorrowEnvironment scope enabled) (base : BitVec 64) (before : List (BitVec 32))
    (returnWord : BitVec 32) (returnReg : Arm64.Reg) (extra tick : Nat) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (decodedReturn : Arm64.decode returnWord = some (.ret returnReg)) (noReturns : NoReturns before)
    (scheduled : ScheduledWords environment base tick (before ++ [returnWord]) s out observations) :
    runScheduledToReturn (program base) environment.advance (before.length + 1 + extra) tick s = some (out, observations) := by
  induction before generalizing tick s observations with
  | nil =>
    cases scheduled with
    | step decoded allowed beforeRunning fetched afterRunning globals tail =>
      have instructionEq := Option.some.inj (decoded.symm.trans decodedReturn)
      subst instructionEq
      cases tail
      have result := runScheduledToReturn_ret (program base) environment.advance extra tick s returnReg
        beforeRunning fetched (by rw [evalInst_permitted base (.ret returnReg) allowed]; exact afterRunning)
      simpa only [List.length_nil, Nat.zero_add, Nat.add_comm 1 extra,
        evalInst_permitted base (.ret returnReg) allowed,
        scheduledObservation_permitted base (.ret returnReg) allowed] using result
  | cons word rest ih =>
    cases scheduled with
    | @step tick word restAndReturn s out observations instruction decoded allowed beforeRunning fetched afterRunning globals tail =>
      have notReturn : ∀ r, instruction ≠ .ret r := by
        intro r equal
        exact noReturns word (by simp) r (by rw [decoded, equal])
      have result := ih (tick + 1) (Arm64.execInstWithSvc Arm64.noSyscalls instruction (environment.advance tick s))
        observations noReturns.tail tail
      have step := runScheduledToReturn_nonret (program base) environment.advance (rest.length + 1 + extra) tick s instruction
        beforeRunning fetched (by rw [evalInst_permitted base instruction allowed]; exact afterRunning) notReturn
      rw [evalInst_permitted base instruction allowed, scheduledObservation_permitted base instruction allowed] at step
      have fuel : (word :: rest).length + 1 + extra = (rest.length + 1 + extra) + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuel, step, result]
      rfl

theorem concurrent_call_evaluated (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) :
    runScheduledToReturn (program base) environment.advance
      (512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) 0 (logicalState base s message) =
      some (call.schedule.actualOut, call.observations) := by
  let count := BitVec.ofNat 64 message.bytes.size
  have scheduled := concurrent_scheduled_cast environment.static base 0 (wholeCallCode count)
    (wholeCallBeforeReturnCode count ++ [imageWords[150]!]) (logicalState base s message)
    call.schedule.actualOut call.observations (whole_call_final_return count) call.schedule.scheduled
  have bound : (wholeCallCode count).length ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by
    rw [← call.schedule.countExact]
    exact call.budget
  have length : (wholeCallBeforeReturnCode count).length + 1 = (wholeCallCode count).length := by
    rw [whole_call_final_return, List.length_append, List.length_singleton]
  have result := runScheduledToReturn_of_schedule environment.static base (wholeCallBeforeReturnCode count)
    imageWords[150]! .x30 ((512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) - (wholeCallCode count).length)
    0 (logicalState base s message) call.schedule.actualOut call.observations
    final_return_decode call.schedule.noEarlyReturn scheduled
  have fuel : (wholeCallBeforeReturnCode count).length + 1 +
      ((512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) - (wholeCallCode count).length) =
      512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by omega
  rw [fuel] at result
  exact result

theorem concurrent_call_state_evaluated (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) :
    runScheduledStateToReturn (program base) environment.advance
      (512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) 0 (logicalState base s message) = some call.schedule.actualOut := by
  unfold runScheduledStateToReturn
  rw [concurrent_call_evaluated base s message extent authority environment call]
  rfl

end Crypto.ARM64.Imported
