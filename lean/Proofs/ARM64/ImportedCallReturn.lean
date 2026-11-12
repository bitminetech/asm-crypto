import Proofs.ARM64.ImportedReturnFetch
import Proofs.ARM64.ImportedCycleFetch

/-! The complete recorded call has no RET before its final image instruction. -/
namespace Crypto.ARM64.Imported

def WordsWithoutReturn (words : List (BitVec 32)) : Prop := PermittedWords words ∧ NoReturns words

def nonReturnInstruction : Arm64.Instr → Bool
  | .ret _ => false
  | _ => true

theorem wordsWithoutReturn_of_all (words : List (BitVec 32))
    (all : (words.all fun word => ((Arm64.decode word).map fun i =>
      permittedInstruction i && nonReturnInstruction i).getD false) = true) : WordsWithoutReturn words := by
  constructor
  · intro word member instruction decoded
    have good := List.all_eq_true.mp all word member
    have both : permittedInstruction instruction = true ∧ nonReturnInstruction instruction = true := by
      simpa only [decoded, Option.map_some, Option.getD_some, Bool.and_eq_true] using good
    exact both.1
  · intro word member r decoded
    have good := List.all_eq_true.mp all word member
    simp [decoded, nonReturnInstruction] at good

theorem WordsWithoutReturn.append {xs ys : List (BitVec 32)}
    (left : WordsWithoutReturn xs) (right : WordsWithoutReturn ys) : WordsWithoutReturn (xs ++ ys) :=
  ⟨left.1.append right.1, left.2.append right.2⟩

theorem WordsWithoutReturn.repeated {code : List (BitVec 32)}
    (safe : WordsWithoutReturn code) (n : Nat) : WordsWithoutReturn (List.replicate n code).flatten :=
  ⟨safe.1.repeated n, safe.2.repeated n⟩

def exitBeforeReturnCode := (imageWords.toList.drop 131).take 19

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem header_without_return : WordsWithoutReturn headerCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem zero_pad_without_return : WordsWithoutReturn zeroPadCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem padding_setup_without_return : WordsWithoutReturn paddingSetupCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem tail_copy_cycle_without_return : WordsWithoutReturn tailCopyCycleCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem tail_copy_end_without_return : WordsWithoutReturn tailCopyEndCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem marker_without_return : WordsWithoutReturn markerCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem length_without_return : WordsWithoutReturn lengthCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem hash_init_without_return : WordsWithoutReturn hashInitCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_gate_without_return : WordsWithoutReturn blockGateCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem word_cycle_without_return : WordsWithoutReturn wordCycleCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem schedule_cycle_without_return : WordsWithoutReturn scheduleCycleCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem initial_load_without_return : WordsWithoutReturn initialLoadCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem round_cycle_without_return : WordsWithoutReturn roundCycleCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem feed_forward_without_return : WordsWithoutReturn feedForwardCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_advance_without_return : WordsWithoutReturn blockAdvanceCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_skip_without_return : WordsWithoutReturn blockSkipCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem padding_phase_without_return : WordsWithoutReturn paddingPhaseCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem digest_gate_without_return : WordsWithoutReturn digestGateCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem exit_before_return_without_return : WordsWithoutReturn exitBeforeReturnCode := by
  apply wordsWithoutReturn_of_all
  decide +kernel

theorem padding_count_without_return (small : Bool) : WordsWithoutReturn (paddingCountCode small) := by
  cases small <;> apply wordsWithoutReturn_of_all <;> decide +kernel

theorem tail_copy_without_return (rem : Nat) : WordsWithoutReturn (tailCopyCode rem) :=
  (tail_copy_cycle_without_return.repeated rem).append tail_copy_end_without_return

theorem prepare_padding_without_return (count : BitVec 64) : WordsWithoutReturn (preparePaddingCode count) :=
  (zero_pad_without_return.append (padding_setup_without_return.append (tail_copy_without_return _))).append
    (marker_without_return.append ((padding_count_without_return _).append length_without_return))

theorem compression_without_return : WordsWithoutReturn compressionCode :=
  initial_load_without_return.append ((round_cycle_without_return.repeated 64).append feed_forward_without_return)

theorem block_without_return : WordsWithoutReturn blockCode :=
  (word_cycle_without_return.repeated 16).append
    ((schedule_cycle_without_return.repeated 48).append compression_without_return)

theorem block_iteration_without_return : WordsWithoutReturn blockIterationCode :=
  block_gate_without_return.append (block_without_return.append block_advance_without_return)

theorem outer_loop_without_return (n : Nat) : WordsWithoutReturn (outerLoopCode n) :=
  (block_iteration_without_return.repeated n).append block_skip_without_return

theorem hash_phases_without_return (full padding : Nat) : WordsWithoutReturn (hashPhasesCode full padding) :=
  (outer_loop_without_return full).append (padding_phase_without_return.append
    ((outer_loop_without_return padding).append digest_gate_without_return))

def wholeCallBeforeReturnCode (count : BitVec 64) :=
  headerCode ++ (preparePaddingCode count ++ (hashInitCode ++
    (hashPhasesCode (count.toNat / 64) (if count.toNat % 64 < 56 then 1 else 2) ++ exitBeforeReturnCode)))

theorem whole_call_without_return (count : BitVec 64) : WordsWithoutReturn (wholeCallBeforeReturnCode count) :=
  header_without_return.append ((prepare_padding_without_return count).append
    (hash_init_without_return.append ((hash_phases_without_return _ _).append exit_before_return_without_return)))

theorem exit_code_return : exitCode = exitBeforeReturnCode ++ [imageWords[150]!] := by decide +kernel

theorem whole_call_final_return (count : BitVec 64) :
    wholeCallCode count = wholeCallBeforeReturnCode count ++ [imageWords[150]!] := by
  simp only [wholeCallCode, wholeCallBeforeReturnCode, hashBodyCode, exit_code_return, List.append_assoc]

theorem final_return_decode : Arm64.decode imageWords[150]! = some (.ret .x30) := by decide +kernel

theorem whole_call_permitted (count : BitVec 64) : PermittedWords (wholeCallCode count) := by
  rw [whole_call_final_return]
  exact (whole_call_without_return count).1.append (image_single_permitted ⟨150, by decide⟩)

theorem whole_call_return_from_path (base : BitVec 64) (s out : Arm64.State) (count : BitVec 64)
    (loaded : (program base).CodeLoaded s.mem)
    (executed : runWords (wholeCallCode count) s = some out)
    (path : StaticPath base (wholeCallCode count) s) (running : out.status = .Running) :
    runToReturn (program base) (512 + 4000 * ((count.toNat + 8) / 64 + 1)) s = some out := by
  have bound := whole_call_code_bound count
  have length : (wholeCallBeforeReturnCode count).length + 1 = (wholeCallCode count).length := by
    rw [whole_call_final_return, List.length_append, List.length_singleton]
  have result := runToReturn_of_staticPath base (wholeCallBeforeReturnCode count) imageWords[150]! .x30
    ((512 + 4000 * ((count.toNat + 8) / 64 + 1)) - (wholeCallCode count).length) s out
    final_return_decode (whole_call_without_return count).2
    (by rw [← whole_call_final_return]; exact whole_call_permitted count) loaded
    (by rw [← whole_call_final_return]; exact executed)
    (by rw [← whole_call_final_return]; exact path) running
  have fuel : (wholeCallBeforeReturnCode count).length + 1 +
      ((512 + 4000 * ((count.toNat + 8) / 64 + 1)) - (wholeCallCode count).length) =
      512 + 4000 * ((count.toNat + 8) / 64 + 1) := by omega
  rw [fuel] at result
  exact result

end Crypto.ARM64.Imported

