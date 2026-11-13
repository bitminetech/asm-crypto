import Proofs.ARM64.ImportedConfidentialCall
import Proofs.ARM64.ImportedABI

/-!
Explicit architectural timing models for the complete native SHA-256 call.
An externally reviewed profile chooses admitted instructions and a cost on
actual imported pre-states, with a checked per-instruction observation law.
Complete paired cost equality follows from the proved native trace theorem;
it is never an assumption of caller entry. The costed runner has exactly the
original imported CPU updates, with a proved state-erasure theorem.

The concrete architectural-unit profile counts instructions. Its one unit per
instruction measures architectural work. HardwareTimingConforms specifies the
hardware/profile correspondence required for a physical duration claim.
The current architectural observer has no cache, predictor, power, speculative
execution or scheduler model. Physical claims need their own explicit model
and conformance evidence under the chosen profile.

The consuming caller must keep preparation, sizing/allocation, invocation
scheduling and result use within the declared public-data/disclosure policy.
Message contents may be secret while pointers, offsets and lengths are public.
The digest/status are permitted releases. Private stack contents and secret-
valued caller-clobbered registers must remain protected, or be cleared before
exposure. This callee theorem does not prove those application-level duties.
-/

namespace Crypto.ARM64.Imported

structure TimingProfile where
  admits : Arm64.Instr → Prop
  cost : Arm64.Instr → Arm64.State → Nat
  observationLaw : ∀ instruction left right, admits instruction →
    instructionObservation instruction left = instructionObservation instruction right →
    cost instruction left = cost instruction right

def TimingProfile.ImageCovered (profile : TimingProfile) : Prop :=
  ∀ index : Fin 151, ∀ instruction, Arm64.decode imageWords[index.val]! = some instruction → profile.admits instruction

def TimingProfile.WordsCovered (profile : TimingProfile) (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ instruction, Arm64.decode word = some instruction → profile.admits instruction

theorem TimingProfile.WordsCovered.tail {profile : TimingProfile} {word : BitVec 32} {rest : List (BitVec 32)}
    (covered : profile.WordsCovered (word :: rest)) : profile.WordsCovered rest := by
  intro w member instruction decoded
  exact covered w (by simp [member]) instruction decoded

theorem TimingProfile.whole_call_covered (profile : TimingProfile) (covered : profile.ImageCovered)
    (count : BitVec 64) : profile.WordsCovered (wholeCallCode count) := by
  intro word member instruction decoded
  rw [← wholeCallIndices_words count] at member
  obtain ⟨index, present, same⟩ := List.mem_map.mp member
  subst word
  exact covered ⟨index, wholeCallIndices_bounded count index present⟩ instruction decoded

/-- Costs annotate exactly the existing imported decode/execute state updates. -/
def runWordsCosted (profile : TimingProfile) : List (BitVec 32) → Arm64.State → Option (Arm64.State × Nat)
  | [], s => some (s, 0)
  | word :: rest, s => do
      let instruction ← Arm64.decode word
      let after := Arm64.execInstWithSvc Arm64.noSyscalls instruction s
      let (out, tailCost) ← runWordsCosted profile rest after
      pure (out, profile.cost instruction s + tailCost)

theorem runWordsCosted_erases (profile : TimingProfile) (words : List (BitVec 32)) (s : Arm64.State) :
    (runWordsCosted profile words s).map Prod.fst = runWords words s := by
  induction words generalizing s with
  | nil => rfl
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsCosted, runWords, decoded]
    | some instruction =>
      simp only [runWordsCosted, runWords, decoded, Bind.bind, Option.bind]
      specialize ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)
      cases costed : runWordsCosted profile rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) with
      | none => simpa only [costed, Option.map_none, Option.bind_none, Bind.bind, Option.bind] using ih
      | some result =>
        rcases result with ⟨out, cost⟩
        simpa only [costed, Option.map_some, Option.bind_some, Bind.bind, Option.bind, pure, Pure.pure] using ih

/-- Internal composition lemma. Complete call theorems below derive equal
observations from the native noninterference proof rather than caller entry. -/
theorem equal_observations_costed (profile : TimingProfile) (words : List (BitVec 32))
    (left right leftOut rightOut : Arm64.State) (observations : List InstructionObservation)
    (covered : profile.WordsCovered words)
    (leftObserved : runWordsObserved words left = some (leftOut, observations))
    (rightObserved : runWordsObserved words right = some (rightOut, observations)) :
    ∃ cost, runWordsCosted profile words left = some (leftOut, cost) ∧
      runWordsCosted profile words right = some (rightOut, cost) := by
  induction words generalizing left right leftOut rightOut observations with
  | nil =>
    simp only [runWordsObserved, Option.some.injEq, Prod.mk.injEq] at leftObserved rightObserved
    obtain ⟨rfl, rfl⟩ := leftObserved
    obtain ⟨rfl, _⟩ := rightObserved
    exact ⟨0, rfl, rfl⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at leftObserved
    | some instruction =>
      obtain ⟨leftTail, leftTailObserved, leftList⟩ := labeled_observed_cons word rest left leftOut observations instruction decoded leftObserved
      obtain ⟨rightTail, rightTailObserved, rightList⟩ := labeled_observed_cons word rest right rightOut observations instruction decoded rightObserved
      have same : instructionObservation instruction left = instructionObservation instruction right ∧ leftTail = rightTail :=
        List.cons.inj (leftList.symm.trans rightList)
      have headCost := profile.observationLaw instruction left right (covered word (by simp) instruction decoded) same.1
      rw [same.2] at leftTailObserved
      obtain ⟨tailCost, leftCosted, rightCosted⟩ := ih
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction left)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) leftOut rightOut rightTail
        covered.tail leftTailObserved rightTailObserved
      refine ⟨profile.cost instruction left + tailCost, ?_, ?_⟩
      · simp only [runWordsCosted, decoded, Bind.bind, Option.bind, leftCosted, pure, Pure.pure]
      · simp only [runWordsCosted, decoded, Bind.bind, Option.bind, rightCosted, pure, Pure.pure, headCost]

/-- One abstract architectural instruction unit per admitted concrete form.
This profile makes no statement that physical instruction latency is one cycle. -/
def architecturalUnitProfile : TimingProfile where
  admits := CallFrame.Admissible
  cost := fun _ _ => 1
  observationLaw := fun _ _ _ _ _ => rfl

theorem architectural_unit_image_covered : architecturalUnitProfile.ImageCovered := by
  intro index instruction decoded
  exact scalar_admissible_image index instruction decoded

/-- Hardware/profile conformance law. The hardware-state type and
projection must describe any platform/microarchitectural context relevant to a
physical duration claim. The unit-cost profile measures architectural work. -/
def HardwareTimingConforms {Hardware : Type} (profile : TimingProfile)
    (project : Hardware → Arm64.State) (duration : Arm64.Instr → Hardware → Nat) : Prop :=
  ∀ instruction hardware, profile.admits instruction → duration instruction hardware = profile.cost instruction (project hardware)

theorem hardware_step_cost_equal {Hardware : Type} (profile : TimingProfile)
    (project : Hardware → Arm64.State) (duration : Arm64.Instr → Hardware → Nat)
    (conforms : HardwareTimingConforms profile project duration)
    (instruction : Arm64.Instr) (left right : Hardware) (admitted : profile.admits instruction)
    (observed : instructionObservation instruction (project left) = instructionObservation instruction (project right)) :
    duration instruction left = duration instruction right := by
  exact (conforms instruction left admitted).trans
    ((profile.observationLaw instruction (project left) (project right) admitted observed).trans
      (conforms instruction right admitted).symm)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- Complete paired native calls have equal cost in every covered observation-
determined timing profile. No trace equality is an entry assumption. -/
theorem sha256_modeled_cost_equal (profile : TimingProfile) (covered : profile.ImageCovered)
    (base : BitVec 64) (left right : Arm64.State) (leftData rightData : ByteArray)
    (leftEntry : CallInputs base left leftData) (rightEntry : CallInputs base right rightData)
    (publicInputs : SamePublicCall left right) (countEqual : leftData.size = rightData.size) :
    ∃ leftOut rightOut observations cost,
      runToReturn (program base) (512 + 4000 * ((leftData.size + 8) / 64 + 1)) left = some leftOut ∧
      runToReturn (program base) (512 + 4000 * ((rightData.size + 8) / 64 + 1)) right = some rightOut ∧
      runWordsObserved (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, observations) ∧
      runWordsObserved (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, observations) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, cost) ∧
      runWordsCosted profile (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, cost) := by
  obtain ⟨leftOut, leftReturned, _, _, _, _, _, _, _, _, _, _, leftObs, leftObserved⟩ :=
    sha256_fetched base left leftData leftEntry
  obtain ⟨rightOut, rightReturned, _, _, _, _, _, _, _, _, _, _, rightObs, rightObserved⟩ :=
    sha256_fetched base right rightData rightEntry
  have same := (sha256_observations_equal base left right leftData rightData leftEntry rightEntry
    publicInputs countEqual leftOut rightOut leftObs rightObs leftObserved rightObserved).1
  have rightWords : wholeCallCode (BitVec.ofNat 64 rightData.size) = wholeCallCode (BitVec.ofNat 64 leftData.size) := by rw [countEqual]
  have rightCommon : runWordsObserved (wholeCallCode (BitVec.ofNat 64 leftData.size)) right = some (rightOut, leftObs) := by
    simpa only [rightWords, same] using rightObserved
  obtain ⟨cost, leftCosted, rightCosted⟩ := equal_observations_costed profile
    (wholeCallCode (BitVec.ofNat 64 leftData.size)) left right leftOut rightOut leftObs
    (profile.whole_call_covered covered _) leftObserved rightCommon
  exact ⟨leftOut, rightOut, leftObs, cost, leftReturned, rightReturned, leftObserved,
    by simpa only [same] using rightObserved, leftCosted, by simpa only [rightWords] using rightCosted⟩


theorem architectural_units_eq_length (words : List (BitVec 32)) (s out : Arm64.State) (units : Nat)
    (costed : runWordsCosted architecturalUnitProfile words s = some (out, units)) : units = words.length := by
  induction words generalizing s out units with
  | nil => simpa [runWordsCosted] using (congrArg (fun result => result.map (fun pair => pair.2)) costed).symm
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsCosted, decoded] at costed
    | some instruction =>
      cases tail : runWordsCosted architecturalUnitProfile rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) with
      | none => simp [runWordsCosted, decoded, tail] at costed
      | some result =>
        rcases result with ⟨actualOut, tailUnits⟩
        have values : actualOut = out ∧ 1 + tailUnits = units := by
          rw [runWordsCosted, decoded] at costed
          change (runWordsCosted architecturalUnitProfile rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)).bind
            (fun pair => some (pair.1, 1 + pair.2)) = some (out, units) at costed
          rw [tail] at costed
          simpa only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] using costed
        have length := ih _ actualOut tailUnits tail
        simp only [List.length_cons]
        omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The concrete architectural profile counts native instructions; the bound
is the already proved instruction budget, with no physical-cycle claim. -/
theorem sha256_architectural_units_equal
    (base : BitVec 64) (left right : Arm64.State) (leftData rightData : ByteArray)
    (leftEntry : CallInputs base left leftData) (rightEntry : CallInputs base right rightData)
    (publicInputs : SamePublicCall left right) (countEqual : leftData.size = rightData.size) :
    ∃ leftOut rightOut units,
      runToReturn (program base) (512 + 4000 * ((leftData.size + 8) / 64 + 1)) left = some leftOut ∧
      runToReturn (program base) (512 + 4000 * ((rightData.size + 8) / 64 + 1)) right = some rightOut ∧
      runWordsCosted architecturalUnitProfile (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, units) ∧
      runWordsCosted architecturalUnitProfile (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, units) ∧
      units = (wholeCallCode (BitVec.ofNat 64 leftData.size)).length ∧
      units ≤ 512 + 4000 * ((leftData.size + 8) / 64 + 1) := by
  obtain ⟨leftOut, rightOut, observations, units, leftReturned, rightReturned, _, _, leftCosted, rightCosted⟩ :=
    sha256_modeled_cost_equal architecturalUnitProfile architectural_unit_image_covered base left right leftData rightData
      leftEntry rightEntry publicInputs countEqual
  have length := architectural_units_eq_length _ left leftOut units leftCosted
  have sizeBound : leftData.size < 2 ^ 64 := by have := leftEntry.bound; omega
  have bound := whole_call_code_bound (BitVec.ofNat 64 leftData.size)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeBound] at bound
  exact ⟨leftOut, rightOut, units, leftReturned, rightReturned, leftCosted, rightCosted, length, length ▸ bound⟩

end Crypto.ARM64.Imported
