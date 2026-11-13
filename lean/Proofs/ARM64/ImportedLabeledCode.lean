import Proofs.ARM64.ImportedCallBounds
import Proofs.ARM64.ImportedLinearFetch

/-!
Pure instruction-index tape for the exact SHA-256 recorded-word program.
Mapping the labels through the pinned image reproduces wholeCallCode. The
compositional path certificate checks every label's range and each CFG edge,
starts at 0 and terminates at 150/Returned, with no earlier return label. The
tape depends only on the public byte count and includes every repeated word,
schedule, compression, full-block and padding-block iteration.
These are list/CFG results. Alignment with actual fetched PCs and public data
access traces must be established separately; no trace equality is assumed.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

inductive IndexPoint where
  | instruction (index : Nat)
  | returned
  deriving DecidableEq, Repr

def labeledSuccessor (index : Nat) (next : IndexPoint) : Bool :=
  match next with
  | .returned => decide (index = 150)
  | .instruction j => match index with
    | 18 => decide (j = 19 ∨ j = 23)
    | 22 => decide (j = 17)
    | 27 => decide (j = 28 ∨ j = 29)
    | 41 => decide (j = 42 ∨ j = 126)
    | 48 => decide (j = 43 ∨ j = 49)
    | 66 => decide (j = 49 ∨ j = 67)
    | 105 => decide (j = 73 ∨ j = 106)
    | 125 => decide (j = 41)
    | 126 => decide (j = 127 ∨ j = 131)
    | 130 => decide (j = 41)
    | 150 => false
    | i => decide (j = i + 1)

def indexNext (indices : List Nat) (finish : IndexPoint) : IndexPoint :=
  match indices with
  | [] => finish
  | i :: _ => .instruction i

def labeledRun (start : IndexPoint) : List Nat → IndexPoint → Bool
  | [], finish => decide (start = finish)
  | i :: rest, finish => decide (start = .instruction i) &&
      (decide (i < 151) && (labeledSuccessor i (indexNext rest finish) &&
        labeledRun (indexNext rest finish) rest finish))


theorem labeledRun_cons_iff (start finish : IndexPoint) (i : Nat) (rest : List Nat) :
    labeledRun start (i :: rest) finish = true ↔
      start = .instruction i ∧ i < 151 ∧ labeledSuccessor i (indexNext rest finish) = true ∧
        labeledRun (indexNext rest finish) rest finish = true := by
  simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq]

theorem labeledRun_start (start finish : IndexPoint) (indices : List Nat)
    (h : labeledRun start indices finish = true) : start = indexNext indices finish := by
  cases indices with
  | nil => simpa [labeledRun, indexNext] using h
  | cons i rest =>
    simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem indexNext_append (xs ys : List Nat) (middle finish : IndexPoint)
    (hy : labeledRun middle ys finish = true) :
    indexNext (xs ++ ys) finish = indexNext xs middle := by
  cases xs with
  | nil => exact (labeledRun_start middle finish ys hy).symm
  | cons i rest => rfl

theorem labeledRun_append (start middle finish : IndexPoint) (xs ys : List Nat)
    (hx : labeledRun start xs middle = true) (hy : labeledRun middle ys finish = true) :
    labeledRun start (xs ++ ys) finish = true := by
  induction xs generalizing start with
  | nil =>
    have same : start = middle := by simpa [labeledRun] using hx
    subst start
    exact hy
  | cons i rest ih =>
    simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq] at hx
    simp only [List.cons_append, labeledRun, Bool.and_eq_true, decide_eq_true_eq]
    rw [indexNext_append rest ys middle finish hy]
    exact ⟨hx.1, hx.2.1, hx.2.2.1, ih _ hx.2.2.2⟩

theorem labeledRun_repeated (point : IndexPoint) (code : List Nat) (n : Nat)
    (cycle : labeledRun point code point = true) :
    labeledRun point (List.replicate n code).flatten point = true := by
  induction n with
  | zero => simp [labeledRun]
  | succ n ih =>
    simpa only [List.replicate_succ, List.flatten_cons] using
      labeledRun_append point point point code (List.replicate n code).flatten cycle ih

theorem labeledRun_repeat_exit (start finish : IndexPoint) (code : List Nat) (n : Nat)
    (cycle : labeledRun start code start = true) (exitPath : labeledRun start code finish = true) :
    labeledRun start (List.replicate (n + 1) code).flatten finish = true := by
  have combined := labeledRun_append start start finish (List.replicate n code).flatten code
    (labeledRun_repeated start code n cycle) exitPath
  simpa only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil] using combined

def indexSpan (offset count : Nat) : List Nat := (List.range count).map (offset + ·)

theorem map_repeated_indices (f : Nat → BitVec 32) (code : List Nat) (n : Nat) :
    (List.replicate n code).flatten.map f = (List.replicate n (code.map f)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.flatten_cons, List.map_append] using congrArg (code.map f ++ ·) ih


structure LabeledPath (start : IndexPoint) (indices : List Nat) (finish : IndexPoint) : Prop where
  valid : labeledRun start indices finish = true

theorem LabeledPath.append {start middle finish : IndexPoint} {xs ys : List Nat}
    (left : LabeledPath start xs middle) (right : LabeledPath middle ys finish) :
    LabeledPath start (xs ++ ys) finish :=
  ⟨labeledRun_append start middle finish xs ys left.valid right.valid⟩

theorem LabeledPath.repeated {point : IndexPoint} {code : List Nat}
    (cycle : LabeledPath point code point) (n : Nat) :
    LabeledPath point (List.replicate n code).flatten point :=
  ⟨labeledRun_repeated point code n cycle.valid⟩

theorem LabeledPath.repeat_exit {start finish : IndexPoint} {code : List Nat}
    (cycle : LabeledPath start code start) (exitPath : LabeledPath start code finish) (n : Nat) :
    LabeledPath start (List.replicate (n + 1) code).flatten finish :=
  ⟨labeledRun_repeat_exit start finish code n cycle.valid exitPath.valid⟩

def tailCopyIndices (rem : Nat) :=
  (List.replicate rem (indexSpan 17 6)).flatten ++ indexSpan 17 2

def paddingCountIndices (small : Bool) := if small then indexSpan 25 3 else indexSpan 25 4

def preparePaddingIndices (count : BitVec 64) :=
  (indexSpan 4 9 ++ (indexSpan 13 4 ++ tailCopyIndices (count.toNat % 64))) ++
    (indexSpan 23 2 ++ (paddingCountIndices (decide (count.toNat % 64 < 56)) ++ indexSpan 29 4))

def compressionIndices := indexSpan 67 6 ++
  ((List.replicate 64 (indexSpan 73 33)).flatten ++ indexSpan 106 17)

def blockIndices := (List.replicate 16 (indexSpan 43 6)).flatten ++
  ((List.replicate 48 (indexSpan 49 18)).flatten ++ compressionIndices)

def blockIterationIndices := indexSpan 41 2 ++ (blockIndices ++ indexSpan 123 3)

def outerLoopIndices (n : Nat) := (List.replicate n blockIterationIndices).flatten ++ indexSpan 41 1

def hashPhasesIndices (full padding : Nat) :=
  outerLoopIndices full ++ (indexSpan 126 5 ++ (outerLoopIndices padding ++ indexSpan 126 1))

def wholeCallIndices (count : BitVec 64) := indexSpan 0 4 ++ (preparePaddingIndices count ++
  (indexSpan 33 8 ++ (hashPhasesIndices (count.toNat / 64)
    (if count.toNat % 64 < 56 then 1 else 2) ++ indexSpan 131 20)))

theorem wholeCallIndices_words (count : BitVec 64) :
    (wholeCallIndices count).map (fun i => imageWords[i]!) = wholeCallCode count := by
  have header : (indexSpan 0 4).map (fun i => imageWords[i]!) = headerCode := by decide +kernel
  have zero : (indexSpan 4 9).map (fun i => imageWords[i]!) = zeroPadCode := by decide +kernel
  have setup : (indexSpan 13 4).map (fun i => imageWords[i]!) = paddingSetupCode := by decide +kernel
  have tailCycle : (indexSpan 17 6).map (fun i => imageWords[i]!) = tailCopyCycleCode := by decide +kernel
  have tailEnd : (indexSpan 17 2).map (fun i => imageWords[i]!) = tailCopyEndCode := by decide +kernel
  have marker : (indexSpan 23 2).map (fun i => imageWords[i]!) = markerCode := by decide +kernel
  have length : (indexSpan 29 4).map (fun i => imageWords[i]!) = lengthCode := by decide +kernel
  have init : (indexSpan 33 8).map (fun i => imageWords[i]!) = hashInitCode := by decide +kernel
  have word : (indexSpan 43 6).map (fun i => imageWords[i]!) = wordCycleCode := by decide +kernel
  have schedule : (indexSpan 49 18).map (fun i => imageWords[i]!) = scheduleCycleCode := by decide +kernel
  have initial : (indexSpan 67 6).map (fun i => imageWords[i]!) = initialLoadCode := by decide +kernel
  have round : (indexSpan 73 33).map (fun i => imageWords[i]!) = roundCycleCode := by decide +kernel
  have feed : (indexSpan 106 17).map (fun i => imageWords[i]!) = feedForwardCode := by decide +kernel
  have blockGate : (indexSpan 41 2).map (fun i => imageWords[i]!) = blockGateCode := by decide +kernel
  have advance : (indexSpan 123 3).map (fun i => imageWords[i]!) = blockAdvanceCode := by decide +kernel
  have skip : (indexSpan 41 1).map (fun i => imageWords[i]!) = blockSkipCode := by decide +kernel
  have phase : (indexSpan 126 5).map (fun i => imageWords[i]!) = paddingPhaseCode := by decide +kernel
  have digestGate : (indexSpan 126 1).map (fun i => imageWords[i]!) = digestGateCode := by decide +kernel
  have exitPath : (indexSpan 131 20).map (fun i => imageWords[i]!) = exitCode := by decide +kernel
  have padCount (small : Bool) : (paddingCountIndices small).map (fun i => imageWords[i]!) = paddingCountCode small := by
    cases small <;> decide +kernel
  simp only [wholeCallIndices, preparePaddingIndices, tailCopyIndices, compressionIndices, blockIndices,
    blockIterationIndices, outerLoopIndices, hashPhasesIndices, List.map_append, map_repeated_indices,
    header, zero, setup, tailCycle, tailEnd, marker, length, init, word, schedule, initial, round, feed,
    blockGate, advance, skip, phase, digestGate, exitPath, padCount]
  rfl

theorem wholeCallIndices_path (count : BitVec 64) :
    LabeledPath (.instruction 0) (wholeCallIndices count) .returned := by
  have header : LabeledPath (.instruction 0) (indexSpan 0 4) (.instruction 4) := ⟨by decide +kernel⟩
  have zero : LabeledPath (.instruction 4) (indexSpan 4 9) (.instruction 13) := ⟨by decide +kernel⟩
  have setup : LabeledPath (.instruction 13) (indexSpan 13 4) (.instruction 17) := ⟨by decide +kernel⟩
  have tailCycle : LabeledPath (.instruction 17) (indexSpan 17 6) (.instruction 17) := ⟨by decide +kernel⟩
  have tailEnd : LabeledPath (.instruction 17) (indexSpan 17 2) (.instruction 23) := ⟨by decide +kernel⟩
  have marker : LabeledPath (.instruction 23) (indexSpan 23 2) (.instruction 25) := ⟨by decide +kernel⟩
  have length : LabeledPath (.instruction 29) (indexSpan 29 4) (.instruction 33) := ⟨by decide +kernel⟩
  have init : LabeledPath (.instruction 33) (indexSpan 33 8) (.instruction 41) := ⟨by decide +kernel⟩
  have wordCycle : LabeledPath (.instruction 43) (indexSpan 43 6) (.instruction 43) := ⟨by decide +kernel⟩
  have wordExit : LabeledPath (.instruction 43) (indexSpan 43 6) (.instruction 49) := ⟨by decide +kernel⟩
  have scheduleCycle : LabeledPath (.instruction 49) (indexSpan 49 18) (.instruction 49) := ⟨by decide +kernel⟩
  have scheduleExit : LabeledPath (.instruction 49) (indexSpan 49 18) (.instruction 67) := ⟨by decide +kernel⟩
  have initial : LabeledPath (.instruction 67) (indexSpan 67 6) (.instruction 73) := ⟨by decide +kernel⟩
  have roundCycle : LabeledPath (.instruction 73) (indexSpan 73 33) (.instruction 73) := ⟨by decide +kernel⟩
  have roundExit : LabeledPath (.instruction 73) (indexSpan 73 33) (.instruction 106) := ⟨by decide +kernel⟩
  have feed : LabeledPath (.instruction 106) (indexSpan 106 17) (.instruction 123) := ⟨by decide +kernel⟩
  have gate : LabeledPath (.instruction 41) (indexSpan 41 2) (.instruction 43) := ⟨by decide +kernel⟩
  have advance : LabeledPath (.instruction 123) (indexSpan 123 3) (.instruction 41) := ⟨by decide +kernel⟩
  have skip : LabeledPath (.instruction 41) (indexSpan 41 1) (.instruction 126) := ⟨by decide +kernel⟩
  have phase : LabeledPath (.instruction 126) (indexSpan 126 5) (.instruction 41) := ⟨by decide +kernel⟩
  have digestGate : LabeledPath (.instruction 126) (indexSpan 126 1) (.instruction 131) := ⟨by decide +kernel⟩
  have exitPath : LabeledPath (.instruction 131) (indexSpan 131 20) .returned := ⟨by decide +kernel⟩
  have padCount (small : Bool) : LabeledPath (.instruction 25) (paddingCountIndices small) (.instruction 29) := by
    cases small <;> exact ⟨by decide +kernel⟩
  have tail (rem : Nat) : LabeledPath (.instruction 17) (tailCopyIndices rem) (.instruction 23) :=
    (tailCycle.repeated rem).append tailEnd
  have padding : LabeledPath (.instruction 4) (preparePaddingIndices count) (.instruction 33) :=
    (zero.append (setup.append (tail _))).append (marker.append ((padCount _).append length))
  have compression : LabeledPath (.instruction 67) compressionIndices (.instruction 123) :=
    initial.append ((roundCycle.repeat_exit roundExit 63).append feed)
  have block : LabeledPath (.instruction 43) blockIndices (.instruction 123) :=
    (wordCycle.repeat_exit wordExit 15).append ((scheduleCycle.repeat_exit scheduleExit 47).append compression)
  have iteration : LabeledPath (.instruction 41) blockIterationIndices (.instruction 41) :=
    gate.append (block.append advance)
  have outer (n : Nat) : LabeledPath (.instruction 41) (outerLoopIndices n) (.instruction 126) :=
    (iteration.repeated n).append skip
  have phases (full pad : Nat) : LabeledPath (.instruction 41) (hashPhasesIndices full pad) (.instruction 131) :=
    (outer full).append (phase.append ((outer pad).append digestGate))
  exact header.append (padding.append (init.append ((phases _ _).append exitPath)))


def successorIndices (index : Nat) : List Nat := match index with
  | 18 => [19, 23]
  | 22 => [17]
  | 27 => [28, 29]
  | 41 => [42, 126]
  | 48 => [43, 49]
  | 66 => [49, 67]
  | 105 => [73, 106]
  | 125 => [41]
  | 126 => [127, 131]
  | 130 => [41]
  | 150 => []
  | i => [i + 1]

theorem labeledSuccessor_iff_mem (i j : Nat) :
    labeledSuccessor i (.instruction j) = true ↔ j ∈ successorIndices i := by
  simp only [labeledSuccessor, successorIndices]
  split <;> simp_all

theorem labeledSuccessor_mem (i j : Nat) (h : labeledSuccessor i (.instruction j) = true) :
    j ∈ successorIndices i := (labeledSuccessor_iff_mem i j).mp h

theorem successorIndices_bounded (i j : Nat) (hi : i < 151) (member : j ∈ successorIndices i) :
    j < 151 := by
  unfold successorIndices at member
  split at member <;> simp_all <;> omega

theorem labeledRun_bounded (start finish : IndexPoint) (indices : List Nat)
    (h : labeledRun start indices finish = true) : ∀ i ∈ indices, i < 151 := by
  induction indices generalizing start with
  | nil => simp
  | cons i rest ih =>
    simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j member
    rcases List.mem_cons.mp member with head | tail
    · subst j; exact h.2.1
    · exact ih _ h.2.2.2 j tail

theorem labeledRun_adjacent (start finish : IndexPoint) (indices : List Nat)
    (h : labeledRun start indices finish = true) (front : List Nat) (i j : Nat) (rest : List Nat)
    (shape : indices = front ++ (i :: j :: rest)) : labeledSuccessor i (.instruction j) = true := by
  induction front generalizing start indices with
  | nil =>
    simp only [List.nil_append] at shape
    subst indices
    simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.2.1
  | cons first front ih =>
    cases indices with
    | nil => simp at shape
    | cons head tail =>
      have shapeTail : tail = front ++ (i :: j :: rest) := (List.cons.inj shape).2
      simp only [labeledRun, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ih _ tail h.2.2.2 shapeTail

theorem labeledRun_no_early_return (start finish : IndexPoint) (indices : List Nat)
    (h : labeledRun start indices finish = true) : 150 ∉ indices.dropLast := by
  induction indices generalizing start with
  | nil => simp
  | cons i rest ih =>
    cases rest with
    | nil => simp
    | cons j rest =>
      have fields := (labeledRun_cons_iff start finish i (j :: rest)).mp h
      have notReturn : i ≠ 150 := by
        intro same
        subst i
        have edge := fields.2.2.1
        simp [indexNext, labeledSuccessor] at edge
      have later := ih _ fields.2.2.2
      simp only [List.dropLast_cons₂]
      intro member
      rcases List.mem_cons.mp member with head | tail
      · exact notReturn head.symm
      · exact later tail

theorem wholeCallIndices_first (count : BitVec 64) : (wholeCallIndices count).head? = some 0 := by
  rfl

theorem wholeCallIndices_last (count : BitVec 64) : (wholeCallIndices count).getLast? = some 150 := by
  have last : (indexSpan 131 20).getLast? = some 150 := by decide +kernel
  simp [wholeCallIndices, List.getLast?_append, last]

theorem wholeCallIndices_return_only_final (count : BitVec 64) : 150 ∉ (wholeCallIndices count).dropLast :=
  labeledRun_no_early_return _ _ _ (wholeCallIndices_path count).valid

theorem wholeCallIndices_bounded (count : BitVec 64) : ∀ i ∈ wholeCallIndices count, i < 151 :=
  labeledRun_bounded _ _ _ (wholeCallIndices_path count).valid

theorem wholeCallIndices_adjacent (count : BitVec 64) (front : List Nat) (i j : Nat) (rest : List Nat)
    (shape : wholeCallIndices count = front ++ (i :: j :: rest)) :
    labeledSuccessor i (.instruction j) = true :=
  labeledRun_adjacent _ _ _ (wholeCallIndices_path count).valid front i j rest shape

theorem wholeCallIndices_terminal : labeledSuccessor 150 .returned = true := rfl

end Crypto.ARM64.Imported
