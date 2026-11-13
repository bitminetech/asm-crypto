import Proofs.ARM64.ImportedConcurrentCall
import Proofs.ARM64.ImportedTiming
import Proofs.ARM64.ImportedDisclosure

/-!
Modeled local-instruction costs for actual scheduled SHA execution. Costs are
sampled at each actual environment-advanced native pre-state. The instruction
update is exactly execInstWithSvc noSyscalls; ScheduledWords supplies actual
fetch/running evidence and fixes the accumulator's endpoint. Environment work,
waiting time and scheduling delay are excluded, as in the instruction budget.
There is no physical-cycle or all-side-channel claim.

The generic correspondence lemma takes actual equal observation witnesses.
The call corollaries obtain them from constructed ConcurrentCallCore witnesses,
so no trace equality or strict/serial result becomes an external caller premise.
-/
namespace Crypto.ARM64.Imported

/-- Annotate the same environment advances and actual imported CPU updates. -/
def runScheduledWordsCosted (profile : TimingProfile)
    (advance : Nat → Arm64.State → Arm64.State) :
    Nat → List (BitVec 32) → Arm64.State → Option (Arm64.State × Nat)
  | _, [], s => some (s, 0)
  | tick, word :: rest, s => do
      let current := advance tick s
      let instruction ← Arm64.decode word
      let after := Arm64.execInstWithSvc Arm64.noSyscalls instruction current
      let (out, tailCost) ← runScheduledWordsCosted profile advance (tick + 1) rest after
      pure (out, profile.cost instruction current + tailCost)

/-- Internal composition over actual fetched scheduled steps and actual serial
observations. Every cost is at its respective real native pre-state. -/
theorem scheduled_cost_matches_observed_serial (profile : TimingProfile)
    {scope : Crypto.Baseline.BorrowScope} {enabled : Arm64.State → Prop}
    {environment : BorrowEnvironment scope enabled} {base : BitVec 64} {tick : Nat}
    {words : List (BitVec 32)} {before after : Arm64.State} {observations : List InstructionObservation}
    (execution : ScheduledWords environment base tick words before after observations) :
    ∀ serial serialOut, profile.WordsCovered words →
      runWordsObserved words serial = some (serialOut, observations) →
      ∃ cost,
        runScheduledWordsCosted profile environment.advance tick words before = some (after, cost) ∧
        runWordsCosted profile words serial = some (serialOut, cost) := by
  induction execution with
  | done tick s =>
    intro serial serialOut covered observed
    have same : serial = serialOut ∧ [] = ([] : List InstructionObservation) := by
      simpa only [runWordsObserved, Option.some.injEq, Prod.mk.injEq] using observed
    rw [← same.1]
    exact ⟨0, rfl, rfl⟩
  | @step tick word rest before out observations instruction decoded allowed beforeRunning fetched afterRunning globals tail ih =>
    intro serial serialOut covered observed
    obtain ⟨serialTail, serialObserved, shape⟩ :=
      labeled_observed_cons word rest serial serialOut _ instruction decoded observed
    have same : instructionObservation instruction (environment.advance tick before) =
        instructionObservation instruction serial ∧ observations = serialTail := List.cons.inj shape
    have headCost := profile.observationLaw instruction (environment.advance tick before) serial
      (covered word (by simp) instruction decoded) same.1
    rw [← same.2] at serialObserved
    obtain ⟨tailCost, scheduledCost, serialCost⟩ := ih
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) serialOut covered.tail serialObserved
    refine ⟨profile.cost instruction (environment.advance tick before) + tailCost, ?_, ?_⟩
    · simp only [runScheduledWordsCosted, decoded, Bind.bind, Option.bind, scheduledCost, pure, Pure.pure]
    · simp only [runWordsCosted, decoded, Bind.bind, Option.bind, serialCost, pure, Pure.pure, headCost]

theorem ConcurrentCallCore.modeled_cost_matches_serial (profile : TimingProfile) (covered : profile.ImageCovered)
    {base : BitVec 64} {s : Arm64.State} {message : Crypto.Reference.ByteList} {extent : Nat}
    {authority : Crypto.Baseline.Authority} {environment : DynamicEnvironment base s extent}
    (call : ConcurrentCallCore base s message extent authority environment) :
    ∃ cost,
      runScheduledWordsCosted profile environment.advance 0 (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
        (logicalState base s message) = some (call.schedule.actualOut, cost) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
        (logicalState base s message) = some (call.safeOut, cost) := by
  exact scheduled_cost_matches_observed_serial profile call.schedule.scheduled
    (logicalState base s message) call.safeOut (profile.whole_call_covered covered _) call.safe.observed

theorem ConcurrentCallCore.architectural_units (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) :
    ∃ units,
      runScheduledWordsCosted architecturalUnitProfile environment.advance 0
        (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (logicalState base s message) =
          some (call.schedule.actualOut, units) ∧
      units = call.observations.length ∧
      units ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by
  obtain ⟨units, scheduled, serial⟩ := call.modeled_cost_matches_serial architecturalUnitProfile architectural_unit_image_covered
  have length := architectural_units_eq_length _ _ _ units serial
  have observations := call.schedule.countExact
  have same : units = call.observations.length := length.trans observations.symm
  exact ⟨units, scheduled, same, same ▸ call.budget⟩

/-- Caller-only construction, covering every permitted scheduling function. -/
theorem sha256_scheduled_modeled_cost (profile : TimingProfile) (covered : profile.ImageCovered)
    (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority) (environment : DynamicEnvironment base s extent) :
    ∃ call : ConcurrentCallCore base s message extent authority environment, ∃ cost,
      runScheduledWordsCosted profile environment.advance 0 (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
        (logicalState base s message) = some (call.schedule.actualOut, cost) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
        (logicalState base s message) = some (call.safeOut, cost) := by
  obtain ⟨call⟩ := sha256_concurrent_call_core base s message extent authority entry environment
  obtain ⟨cost, scheduled, serial⟩ := call.modeled_cost_matches_serial profile covered
  exact ⟨call, cost, scheduled, serial⟩

theorem sha256_scheduled_architectural_units (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority) (environment : DynamicEnvironment base s extent) :
    ∃ call : ConcurrentCallCore base s message extent authority environment, ∃ units,
      runScheduledWordsCosted architecturalUnitProfile environment.advance 0
        (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (logicalState base s message) =
          some (call.schedule.actualOut, units) ∧
      units = call.observations.length ∧
      units ≤ 512 + 4000 * ((message.bytes.size + 8) / 64 + 1) := by
  obtain ⟨call⟩ := sha256_concurrent_call_core base s message extent authority entry environment
  obtain ⟨units, costed, length, bound⟩ := call.architectural_units base s message extent authority environment
  exact ⟨call, units, costed, length, bound⟩

/-- Paired actual schedules have equal local-instruction cost for equal public
caller context, even with different secret payload/prior stack/output bytes and
different allowed external progress. Waiting/environment duration is excluded. -/
theorem paired_scheduled_modeled_cost_equal (profile : TimingProfile) (covered : profile.ImageCovered)
    (base : BitVec 64) (left right : Arm64.State)
    (leftMessage rightMessage : Crypto.Reference.ByteList) (leftExtent rightExtent : Nat)
    (leftAuthority rightAuthority : Crypto.Baseline.Authority)
    (leftEntry : PermissionViewInputs base left leftMessage leftExtent leftAuthority)
    (rightEntry : PermissionViewInputs base right rightMessage rightExtent rightAuthority)
    (context : SameDisclosureContext left right leftMessage rightMessage)
    (leftEnvironment : DynamicEnvironment base left leftExtent)
    (rightEnvironment : DynamicEnvironment base right rightExtent)
    (leftCall : ConcurrentCallCore base left leftMessage leftExtent leftAuthority leftEnvironment)
    (rightCall : ConcurrentCallCore base right rightMessage rightExtent rightAuthority rightEnvironment) :
    ∃ cost,
      runScheduledWordsCosted profile leftEnvironment.advance 0
        (wholeCallCode (BitVec.ofNat 64 leftMessage.bytes.size)) (logicalState base left leftMessage) =
          some (leftCall.schedule.actualOut, cost) ∧
      runScheduledWordsCosted profile rightEnvironment.advance 0
        (wholeCallCode (BitVec.ofNat 64 rightMessage.bytes.size)) (logicalState base right rightMessage) =
          some (rightCall.schedule.actualOut, cost) := by
  have publicInputs : SamePublicCall (logicalState base left leftMessage) (logicalState base right rightMessage) := by
    refine ⟨context.input, context.output, context.stack, context.link, ?_⟩
    change (logicalMemory base left leftMessage).read64 (left.readReg64 .x0 + 8#64) =
      (logicalMemory base right rightMessage).read64 (right.readReg64 .x0 + 8#64)
    rw [logicalMemory_read64, logicalMemory_read64, leftEntry.offsetValue, rightEntry.offsetValue, context.offset]
  have same := (sha256_observations_equal base (logicalState base left leftMessage)
    (logicalState base right rightMessage) leftMessage.bytes rightMessage.bytes
    (permission_view_inputs base left leftMessage leftExtent leftAuthority leftEntry)
    (permission_view_inputs base right rightMessage rightExtent rightAuthority rightEntry)
    publicInputs context.count leftCall.safeOut rightCall.safeOut leftCall.observations rightCall.observations
    leftCall.safe.observed rightCall.safe.observed).1
  have codeEq : wholeCallCode (BitVec.ofNat 64 rightMessage.bytes.size) =
      wholeCallCode (BitVec.ofNat 64 leftMessage.bytes.size) := by rw [context.count]
  have rightObserved : runWordsObserved (wholeCallCode (BitVec.ofNat 64 leftMessage.bytes.size))
      (logicalState base right rightMessage) = some (rightCall.safeOut, leftCall.observations) := by
    simpa only [codeEq, same] using rightCall.safe.observed
  obtain ⟨commonCost, commonLeft, commonRight⟩ := equal_observations_costed profile _
    (logicalState base left leftMessage) (logicalState base right rightMessage)
    leftCall.safeOut rightCall.safeOut leftCall.observations
    (profile.whole_call_covered covered _) leftCall.safe.observed rightObserved
  obtain ⟨leftCost, leftScheduled, leftSerial⟩ := leftCall.modeled_cost_matches_serial profile covered
  obtain ⟨rightCost, rightScheduled, rightSerial⟩ := rightCall.modeled_cost_matches_serial profile covered
  have leftEq : leftCost = commonCost :=
    (Prod.mk.inj (Option.some.inj (leftSerial.symm.trans commonLeft))).2
  have rightSerialCommon : runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 leftMessage.bytes.size))
      (logicalState base right rightMessage) = some (rightCall.safeOut, rightCost) := by
    simpa only [codeEq] using rightSerial
  have rightEq : rightCost = commonCost :=
    (Prod.mk.inj (Option.some.inj (rightSerialCommon.symm.trans commonRight))).2
  exact ⟨commonCost, by simpa only [leftEq] using leftScheduled,
    by simpa only [rightEq] using rightScheduled⟩

end Crypto.ARM64.Imported
