import Proofs.ARM64.ImportedLabelAlignment
import Proofs.ARM64.ImportedWholeCallFetch
import Proofs.ARM64.ImportedStackBound

/-!
Align the public SHA-256 instruction-index tape with actual imported execution
PCs. At every nonterminal edge, native PC alternatives and distinct decoded
successor instructions identify the next label from StaticPath. The Returned
endpoint imposes no artificial PC constraint. Whole-call premises are derived
from unchanged CallInputs and the complete native SHA-256 execution proof.
The observation theorem gives the exact PC list from public code base/length;
data-access traces and the complete architecture confidentiality policy remain
separate obligations.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local irreducible] runWords StaticPath runWordsObserved

def LabelPCStart (base : BitVec 64) (point : IndexPoint) (s : Arm64.State) : Prop :=
  match point with
  | .instruction i => s.pc = base + BitVec.ofNat 64 (4 * i)
  | .returned => True

def LabelPCPath (base : BitVec 64) : List Nat → Arm64.State → Prop
  | [], _ => True
  | i :: rest, s => s.pc = base + BitVec.ofNat 64 (4 * i) ∧
      match Arm64.decode imageWords[i]! with
      | none => False
      | some instruction => LabelPCPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

theorem indexed_words_permitted (indices : List Nat) (bound : ∀ i ∈ indices, i < 151) :
    PermittedWords (indices.map fun i => imageWords[i]!) := by
  intro word member instruction decoded
  obtain ⟨i, present, same⟩ := List.mem_map.mp member
  subst word
  exact image_permitted ⟨i, bound i present⟩ instruction decoded

theorem staticPath_head_fetch (base : BitVec 64) (word : BitVec 32) (rest : List (BitVec 32))
    (s : Arm64.State) (path : StaticPath base (word :: rest) s) :
    (program base).fetch s.pc = Arm64.decode word := by
  cases decoded : Arm64.decode word with
  | none => simp [StaticPath, decoded] at path
  | some instruction =>
    have parts : (program base).fetch s.pc = some instruction ∧
        StaticPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
      simpa only [StaticPath, decoded] using path
    simpa only [decoded] using parts.1

theorem labeledRun_labelPCPath (base : BitVec 64) (start : IndexPoint) (indices : List Nat)
    (s out : Arm64.State) (labels : labeledRun start indices .returned = true)
    (pc : LabelPCStart base start s)
    (executed : runWords (indices.map fun i => imageWords[i]!) s = some out)
    (path : StaticPath base (indices.map fun i => imageWords[i]!) s)
    (running : out.status = .Running) : LabelPCPath base indices s := by
  induction indices generalizing start s with
  | nil => exact True.intro
  | cons i rest ih =>
    obtain ⟨startEq, bound, edge, tailLabels⟩ := (labeledRun_cons_iff start .returned i rest).mp labels
    have currentPC : s.pc = base + BitVec.ofNat 64 (4 * i) := by
      rw [startEq] at pc
      exact pc
    have decoding := image_permitted_all ⟨i, bound⟩
    cases decoded : Arm64.decode imageWords[i]! with
    | none => simp only [decoded, Option.map_none, Option.getD_none, Bool.false_eq_true] at decoding
    | some instruction =>
      rw [List.map_cons, runWords, decoded] at executed
      change runWords (rest.map fun j => imageWords[j]!)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have parts : (program base).fetch s.pc = some instruction ∧
          StaticPath base (rest.map fun j => imageWords[j]!)
            (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [List.map_cons, StaticPath, decoded] using path
      have nextRunning := runWords_running_before (rest.map fun j => imageWords[j]!)
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) out
        (indexed_words_permitted rest (labeledRun_bounded _ _ _ tailLabels)) executed running
      simp only [LabelPCPath, decoded]
      refine ⟨currentPC, ?_⟩
      cases rest with
      | nil => exact True.intro
      | cons j tail =>
        have tailFields := (labeledRun_cons_iff (indexNext (j :: tail) .returned) .returned j tail).mp tailLabels
        have nextBound : j < 151 := tailFields.2.1
        have nextFetched := staticPath_head_fetch base imageWords[j]! (tail.map fun k => imageWords[k]!)
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) parts.2
        have nextPC := native_next_label base ⟨i, bound⟩ ⟨j, nextBound⟩ s instruction edge decoded currentPC nextRunning nextFetched
        exact ih (.instruction j) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) tailLabels nextPC executed parts.2

theorem whole_call_labelPCPath (base : BitVec 64) (s out : Arm64.State) (count : BitVec 64)
    (pc : s.pc = base) (executed : runWords (wholeCallCode count) s = some out)
    (path : StaticPath base (wholeCallCode count) s) (running : out.status = .Running) :
    LabelPCPath base (wholeCallIndices count) s := by
  have mappedExec := runWords_code_cast (wholeCallCode count)
    ((wholeCallIndices count).map fun i => imageWords[i]!) s out (wholeCallIndices_words count).symm executed
  have mappedPath := @StaticPath.of_code_eq base s ((wholeCallIndices count).map fun i => imageWords[i]!)
    (wholeCallCode count) (wholeCallIndices_words count) path
  exact labeledRun_labelPCPath base (.instruction 0) (wholeCallIndices count) s out
    (wholeCallIndices_path count).valid (by simpa [LabelPCStart] using pc) mappedExec mappedPath running

theorem whole_call_sha256_labelPCPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) :
    ∃ out, runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out ∧
      StaticPath base (wholeCallCode (BitVec.ofNat 64 data.size)) s ∧
      LabelPCPath base (wholeCallIndices (BitVec.ofNat 64 data.size)) s ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧ memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
  obtain ⟨out, executed, path, state, nv, sp, pc, zero, running, digest⟩ := whole_call_sha256_staticPath base s data entry
  exact ⟨out, executed, path, whole_call_labelPCPath base s out (BitVec.ofNat 64 data.size) entry.pc executed path running,
    state, nv, sp, pc, zero, running, digest⟩


theorem labeled_observed_cons (word : BitVec 32) (rest : List (BitVec 32))
    (s out : Arm64.State) (observations : List InstructionObservation) (instruction : Arm64.Instr)
    (decoded : Arm64.decode word = some instruction)
    (observed : runWordsObserved (word :: rest) s = some (out, observations)) :
    ∃ tailObs, runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some (out, tailObs) ∧
      observations = instructionObservation instruction s :: tailObs := by
  cases tail : runWordsObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) with
  | none => simp [runWordsObserved, decoded, tail] at observed
  | some result =>
    rcases result with ⟨actualOut, tailObs⟩
    have same : actualOut = out ∧ instructionObservation instruction s :: tailObs = observations := by
      simpa only [runWordsObserved, decoded, Bind.bind, Option.bind, tail, pure, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] using observed
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨tailObs, rfl, rfl⟩

theorem labelPCPath_observed_pcs (base : BitVec 64) (indices : List Nat) (s out : Arm64.State)
    (observations : List InstructionObservation) (pcPath : LabelPCPath base indices s)
    (observed : runWordsObserved (indices.map fun i => imageWords[i]!) s = some (out, observations)) :
    observations.map InstructionObservation.pc = indices.map (fun i => base + BitVec.ofNat 64 (4 * i)) := by
  induction indices generalizing s observations with
  | nil =>
    simp only [List.map_nil, runWordsObserved, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨rfl, rfl⟩ := observed
    rfl
  | cons i rest ih =>
    cases decoded : Arm64.decode imageWords[i]! with
    | none => simp [LabelPCPath, decoded] at pcPath
    | some instruction =>
      have parts : s.pc = base + BitVec.ofNat 64 (4 * i) ∧
          LabelPCPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [LabelPCPath, decoded] using pcPath
      obtain ⟨tailObs, tailObserved, obsEq⟩ := labeled_observed_cons imageWords[i]!
        (rest.map fun j => imageWords[j]!) s out observations instruction decoded observed
      have tailPCs := ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) tailObs parts.2 tailObserved
      rw [obsEq, List.map_cons, List.map_cons]
      change s.pc :: tailObs.map InstructionObservation.pc =
        (base + BitVec.ofNat 64 (4 * i)) :: rest.map (fun j => base + BitVec.ofNat 64 (4 * j))
      rw [parts.1, tailPCs]

theorem callInputs_labelPCPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) : LabelPCPath base (wholeCallIndices (BitVec.ofNat 64 data.size)) s := by
  obtain ⟨out, executed, path, _, _, _, _, _, running, _⟩ := whole_call_sha256_staticPath base s data entry
  exact whole_call_labelPCPath base s out (BitVec.ofNat 64 data.size) entry.pc executed path running

theorem whole_call_observed_pc_tape (base : BitVec 64) (s out : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 data.size)) s = some (out, observations)) :
    observations.map InstructionObservation.pc =
      (wholeCallIndices (BitVec.ofNat 64 data.size)).map (fun i => base + BitVec.ofNat 64 (4 * i)) := by
  have mappedObserved := runWordsObserved_code_cast (wholeCallCode (BitVec.ofNat 64 data.size))
    ((wholeCallIndices (BitVec.ofNat 64 data.size)).map fun i => imageWords[i]!) s out observations
    (wholeCallIndices_words (BitVec.ofNat 64 data.size)).symm observed
  exact labelPCPath_observed_pcs base (wholeCallIndices (BitVec.ofNat 64 data.size)) s out observations
    (callInputs_labelPCPath base s data entry) mappedObserved

end Crypto.ARM64.Imported
