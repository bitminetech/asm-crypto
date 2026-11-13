import Proofs.ARM64.ImportedLabeledExecution
import Proofs.ARM64.ImportedTraceRelation

/-!
Paired actual SHA-256 observation traces. The generic fold uses an internal
instruction-transfer callback, decoded execution, actual successful observed
runs and independently established labeled PC paths. The public suffix rule
instantiates that callback from the proved post-header mask semantics; it adds
no trace-equality or transfer premise to external caller entry.
Pure header/drop4 facts and PC-path stripping connect the paired four-word
header to the remainder. Returned remains an explicit terminal point. This
proves architectural instruction/data-access observations, not an undeclared
physical timing or concurrency model.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local irreducible] runWords runWordsObserved StaticPath

def PairedStepTransfer (base : BitVec 64)
    (Rel : IndexPoint → Arm64.State → Arm64.State → Prop) (indices : List Nat) : Prop :=
  ∀ i : Fin 151, i.val ∈ indices → ∀ (next : IndexPoint) (instruction : Arm64.Instr)
    (left right : Arm64.State),
    labeledSuccessor i.val next = true → Arm64.decode imageWords[i.val]! = some instruction →
    left.pc = base + BitVec.ofNat 64 (4 * i.val) →
    right.pc = base + BitVec.ofNat 64 (4 * i.val) →
    LabelPCStart base next (Arm64.execInstWithSvc Arm64.noSyscalls instruction left) →
    LabelPCStart base next (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) →
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running →
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running →
    Rel (.instruction i.val) left right →
    instructionObservation instruction left = instructionObservation instruction right ∧
      Rel next (Arm64.execInstWithSvc Arm64.noSyscalls instruction left)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction right)

theorem PairedStepTransfer.tail {base : BitVec 64}
    {Rel : IndexPoint → Arm64.State → Arm64.State → Prop} {i : Nat} {rest : List Nat}
    (transfer : PairedStepTransfer base Rel (i :: rest)) : PairedStepTransfer base Rel rest := by
  intro index member
  exact transfer index (List.mem_cons_of_mem i member)

theorem paired_observed_raw (words : List (BitVec 32)) (s out : Arm64.State)
    (observations : List InstructionObservation)
    (observed : runWordsObserved words s = some (out, observations)) : runWords words s = some out := by
  have actual := congrArg (Option.map Prod.fst) observed
  simpa only [runWordsObserved_erases, Option.map_some] using actual

theorem labelPCPath_start (base : BitVec 64) (indices : List Nat) (s : Arm64.State)
    (path : LabelPCPath base indices s) : LabelPCStart base (indexNext indices .returned) s := by
  cases indices with
  | nil => exact True.intro
  | cons i rest => exact path.1

theorem paired_labeled_observations (base : BitVec 64)
    (Rel : IndexPoint → Arm64.State → Arm64.State → Prop) (start : IndexPoint) (indices : List Nat)
    (left right leftOut rightOut : Arm64.State) (leftObs rightObs : List InstructionObservation)
    (labels : labeledRun start indices .returned = true)
    (leftPCPath : LabelPCPath base indices left) (rightPCPath : LabelPCPath base indices right)
    (leftObserved : runWordsObserved (indices.map fun i => imageWords[i]!) left = some (leftOut, leftObs))
    (rightObserved : runWordsObserved (indices.map fun i => imageWords[i]!) right = some (rightOut, rightObs))
    (leftRunning : leftOut.status = .Running) (rightRunning : rightOut.status = .Running)
    (related : Rel start left right) (transfer : PairedStepTransfer base Rel indices) :
    leftObs = rightObs ∧ Rel .returned leftOut rightOut := by
  induction indices generalizing start left right leftOut rightOut leftObs rightObs with
  | nil =>
    have terminal : start = .returned := by simpa only [labeledRun, decide_eq_true_eq] using labels
    subst start
    simp only [List.map_nil, runWordsObserved, Option.some.injEq, Prod.mk.injEq] at leftObserved rightObserved
    obtain ⟨rfl, rfl⟩ := leftObserved
    obtain ⟨rfl, rfl⟩ := rightObserved
    exact ⟨rfl, related⟩
  | cons i rest ih =>
    obtain ⟨startEq, bound, edge, tailLabels⟩ := (labeledRun_cons_iff start .returned i rest).mp labels
    cases decoded : Arm64.decode imageWords[i]! with
    | none => simp [LabelPCPath, decoded] at leftPCPath
    | some instruction =>
      have leftParts : left.pc = base + BitVec.ofNat 64 (4 * i) ∧
          LabelPCPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction left) := by
        simpa only [LabelPCPath, decoded] using leftPCPath
      have rightParts : right.pc = base + BitVec.ofNat 64 (4 * i) ∧
          LabelPCPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) := by
        simpa only [LabelPCPath, decoded] using rightPCPath
      obtain ⟨leftTailObs, leftTailObserved, leftObsEq⟩ := labeled_observed_cons imageWords[i]!
        (rest.map fun j => imageWords[j]!) left leftOut leftObs instruction decoded leftObserved
      obtain ⟨rightTailObs, rightTailObserved, rightObsEq⟩ := labeled_observed_cons imageWords[i]!
        (rest.map fun j => imageWords[j]!) right rightOut rightObs instruction decoded rightObserved
      have permitted := indexed_words_permitted rest (labeledRun_bounded _ _ _ tailLabels)
      have afterLeftRunning := runWords_running_before (rest.map fun j => imageWords[j]!)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction left) leftOut permitted
        (paired_observed_raw _ _ _ _ leftTailObserved) leftRunning
      have afterRightRunning := runWords_running_before (rest.map fun j => imageWords[j]!)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) rightOut permitted
        (paired_observed_raw _ _ _ _ rightTailObserved) rightRunning
      have currentRelation : Rel (.instruction i) left right := by rw [← startEq]; exact related
      obtain ⟨headEq, nextRelation⟩ := transfer ⟨i, bound⟩ (by simp) (indexNext rest .returned)
        instruction left right edge decoded leftParts.1 rightParts.1
        (labelPCPath_start base rest _ leftParts.2) (labelPCPath_start base rest _ rightParts.2)
        afterLeftRunning afterRightRunning currentRelation
      obtain ⟨tailEq, terminalRelation⟩ := ih (indexNext rest .returned)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction left)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) leftOut rightOut leftTailObs rightTailObs
        tailLabels leftParts.2 rightParts.2 leftTailObserved rightTailObserved leftRunning rightRunning
        nextRelation transfer.tail
      refine ⟨?_, terminalRelation⟩
      rw [leftObsEq, rightObsEq, headEq, tailEq]

def IndexedPublicRelation : IndexPoint → Arm64.State → Arm64.State → Prop
  | .instruction n, left, right => if h : n < 151 then PublicRelation (.instruction ⟨n, h⟩) left right else False
  | .returned, left, right => PublicRelation .returned left right

theorem indexedPublicRelation_instruction (i : Fin 151) (left right : Arm64.State) :
    IndexedPublicRelation (.instruction i.val) left right ↔ PublicRelation (.instruction i) left right := by
  simp only [IndexedPublicRelation, dif_pos i.isLt]

theorem indexedPublicRelation_returned (left right : Arm64.State) :
    IndexedPublicRelation .returned left right ↔ PublicRelation .returned left right := Iff.rfl

theorem indexed_public_step_transfer (base : BitVec 64) (indices : List Nat)
    (afterHeader : ∀ i ∈ indices, 4 ≤ i) : PairedStepTransfer base IndexedPublicRelation indices := by
  intro i member next instruction left right edge decoded _leftPC _rightPC _nextLeftPC _nextRightPC
    leftRunning rightRunning related
  have before := (indexedPublicRelation_instruction i left right).mp related
  refine ⟨image_public_observation_eq i instruction left right decoded before leftRunning rightRunning, ?_⟩
  cases next with
  | returned =>
    exact image_public_relation_transfer i .returned instruction left right (afterHeader i.val member)
      edge decoded before leftRunning rightRunning
  | instruction j =>
    have nextBound : j < 151 := successorIndices_bounded i.val j i.isLt (labeledSuccessor_mem i.val j edge)
    have after := image_public_relation_transfer i (.instruction ⟨j, nextBound⟩) instruction left right
      (afterHeader i.val member) edge decoded before leftRunning rightRunning
    exact (indexedPublicRelation_instruction ⟨j, nextBound⟩ _ _).mpr after


theorem LabelPCPath_code_cast (base : BitVec 64) (left right : List Nat) (s : Arm64.State)
    (equal : left = right) (path : LabelPCPath base left s) : LabelPCPath base right s := by
  cases equal
  exact path

theorem LabelPCPath_suffix (base : BitVec 64) (xs ys : List Nat) (s mid : Arm64.State)
    (prefixExec : runWords (xs.map fun i => imageWords[i]!) s = some mid)
    (wholePath : LabelPCPath base (xs ++ ys) s) : LabelPCPath base ys mid := by
  induction xs generalizing s with
  | nil =>
    simp only [List.map_nil, runWords, Option.some.injEq] at prefixExec
    subst mid
    exact wholePath
  | cons i rest ih =>
    cases decoded : Arm64.decode imageWords[i]! with
    | none => simp [List.map_cons, runWords, decoded] at prefixExec
    | some instruction =>
      rw [List.map_cons, runWords, decoded] at prefixExec
      change runWords (rest.map fun j => imageWords[j]!)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some mid at prefixExec
      have parts : s.pc = base + BitVec.ofNat 64 (4 * i) ∧
          LabelPCPath base (rest ++ ys) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [List.cons_append, LabelPCPath, decoded] using wholePath
      exact ih _ prefixExec parts.2

theorem labeledRun_drop (start finish : IndexPoint) (indices : List Nat) (n : Nat)
    (labels : labeledRun start indices finish = true) :
    labeledRun (indexNext (indices.drop n) finish) (indices.drop n) finish = true := by
  induction n generalizing start indices with
  | zero =>
    simp only [List.drop_zero]
    rw [← labeledRun_start start finish indices labels]
    exact labels
  | succ n ih =>
    cases indices with
    | nil => simp [indexNext, labeledRun]
    | cons i rest =>
      have fields := (labeledRun_cons_iff start finish i rest).mp labels
      simpa only [List.drop_succ_cons] using ih (indexNext rest finish) rest fields.2.2.2

theorem wholeCallIndices_header_split (count : BitVec 64) :
    wholeCallIndices count = indexSpan 0 4 ++ (wholeCallIndices count).drop 4 := by rfl

theorem wholeCallIndices_header_words : (indexSpan 0 4).map (fun i => imageWords[i]!) = headerCode := by
  decide +kernel

theorem wholeCallIndices_drop4_first (count : BitVec 64) :
    ((wholeCallIndices count).drop 4).head? = some 4 := by rfl

theorem wholeCallIndices_drop4_run (count : BitVec 64) :
    labeledRun (.instruction 4) ((wholeCallIndices count).drop 4) .returned = true := by
  exact labeledRun_drop (.instruction 0) .returned (wholeCallIndices count) 4 (wholeCallIndices_path count).valid

def IndexAfterHeader : IndexPoint → Prop
  | .instruction i => 4 ≤ i
  | .returned => True

theorem labeledSuccessor_afterHeader (i j : Nat) (lower : 4 ≤ i)
    (edge : labeledSuccessor i (.instruction j) = true) : 4 ≤ j := by
  have member := labeledSuccessor_mem i j edge
  unfold successorIndices at member
  split at member <;> simp_all <;> omega

theorem labeledRun_afterHeader (start : IndexPoint) (indices : List Nat)
    (labels : labeledRun start indices .returned = true) (lower : IndexAfterHeader start) :
    ∀ i ∈ indices, 4 ≤ i := by
  induction indices generalizing start with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨startEq, _, edge, tailLabels⟩ := (labeledRun_cons_iff start .returned i rest).mp labels
    have currentLower : 4 ≤ i := by rw [startEq] at lower; exact lower
    have nextLower : IndexAfterHeader (indexNext rest .returned) := by
      cases rest with
      | nil => exact True.intro
      | cons j tail => exact labeledSuccessor_afterHeader i j currentLower edge
    intro j member
    rcases List.mem_cons.mp member with head | tail
    · subst j; exact currentLower
    · exact ih _ tailLabels nextLower j tail

theorem wholeCallIndices_drop4_afterHeader (count : BitVec 64) :
    ∀ i ∈ (wholeCallIndices count).drop 4, 4 ≤ i :=
  labeledRun_afterHeader (.instruction 4) ((wholeCallIndices count).drop 4)
    (wholeCallIndices_drop4_run count) (by change 4 ≤ 4; omega)

theorem wholeCallCode_header_suffix (count : BitVec 64) :
    wholeCallCode count = headerCode ++ ((wholeCallIndices count).drop 4).map (fun i => imageWords[i]!) := by
  have mapped := congrArg (fun indices : List Nat => indices.map fun i => imageWords[i]!)
    (wholeCallIndices_header_split count)
  dsimp only at mapped
  rw [List.map_append, wholeCallIndices_header_words] at mapped
  exact (wholeCallIndices_words count).symm.trans mapped

theorem wholeCallIndices_suffix_labelPCPath (base : BitVec 64) (count : BitVec 64) (s mid : Arm64.State)
    (prefixExec : runWords headerCode s = some mid)
    (wholePath : LabelPCPath base (wholeCallIndices count) s) :
    LabelPCPath base ((wholeCallIndices count).drop 4) mid := by
  have prefixMapped := runWords_code_cast headerCode ((indexSpan 0 4).map fun i => imageWords[i]!) s mid
    wholeCallIndices_header_words.symm prefixExec
  have mappedPath := LabelPCPath_code_cast base (wholeCallIndices count)
    (indexSpan 0 4 ++ (wholeCallIndices count).drop 4) s (wholeCallIndices_header_split count) wholePath
  exact LabelPCPath_suffix base (indexSpan 0 4) ((wholeCallIndices count).drop 4) s mid prefixMapped mappedPath

theorem paired_public_suffix (count : BitVec 64) (base : BitVec 64)
    (left right leftOut rightOut : Arm64.State) (leftObs rightObs : List InstructionObservation)
    (leftPCPath : LabelPCPath base ((wholeCallIndices count).drop 4) left)
    (rightPCPath : LabelPCPath base ((wholeCallIndices count).drop 4) right)
    (leftObserved : runWordsObserved (((wholeCallIndices count).drop 4).map fun i => imageWords[i]!) left = some (leftOut, leftObs))
    (rightObserved : runWordsObserved (((wholeCallIndices count).drop 4).map fun i => imageWords[i]!) right = some (rightOut, rightObs))
    (leftRunning : leftOut.status = .Running) (rightRunning : rightOut.status = .Running)
    (initial : PublicRelation (.instruction ⟨4, by decide⟩) left right) :
    leftObs = rightObs ∧ PublicRelation .returned leftOut rightOut := by
  have related : IndexedPublicRelation (.instruction 4) left right :=
    (indexedPublicRelation_instruction ⟨4, by decide⟩ left right).mpr initial
  have result := paired_labeled_observations base IndexedPublicRelation (.instruction 4)
    ((wholeCallIndices count).drop 4) left right leftOut rightOut leftObs rightObs
    (wholeCallIndices_drop4_run count) leftPCPath rightPCPath leftObserved rightObserved leftRunning rightRunning
    related (indexed_public_step_transfer base _ (wholeCallIndices_drop4_afterHeader count))
  exact ⟨result.1, result.2⟩

end Crypto.ARM64.Imported
