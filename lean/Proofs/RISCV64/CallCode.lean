import Proofs.RISCV64.SerialCall

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (paddingBlockCount)

private def ReturnFree (code : List Instruction) : Prop :=
  code.all (fun i => i.op != .ret) = true

private instance (code : List Instruction) : Decidable (ReturnFree code) :=
  inferInstanceAs (Decidable (_ = true))

private theorem ReturnFree.append {a b : List Instruction} (ha : ReturnFree a) (hb : ReturnFree b) :
    ReturnFree (a ++ b) := by
  simpa only [ReturnFree, List.all_append, Bool.and_eq_true] using And.intro ha hb

private theorem ImageExecution.follow {base : Addr} {s t out : CPU} {a b : List Instruction}
    (left : ImageExecution base s a t) (right : ImageExecution base t b out)
    (free : ReturnFree a) : ImageExecution base s (a ++ b) out :=
  left.append right (fun i hi => by
    have h := List.all_eq_true.mp (show a.all (fun i => i.op != .ret) = true from free) i hi
    simpa using h)

def blockCode : List Instruction :=
  [blockGuard, startWords] ++ loadCode 16 ++ expansionCode 48 ++ loadHashBody ++
    roundCode 64 ++ feedForward ++ advanceBlock

private theorem load_free (n : Nat) : ReturnFree (loadCode n) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.append (show ReturnFree loadCycle by decide)

private theorem expansion_free (n : Nat) : ReturnFree (expansionCode n) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.append (show ReturnFree expansionCycle by decide)

private theorem round_free (n : Nat) : ReturnFree (roundCode n) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.append (show ReturnFree roundCycle by decide)

attribute [local irreducible] loadCode expansionCode roundCode

private theorem block_free : ReturnFree blockCode := by
  simp only [blockCode, List.append_assoc]
  exact (show ReturnFree [blockGuard, startWords] by decide).append
    ((load_free 16).append ((expansion_free 48).append
      ((show ReturnFree loadHashBody by decide).append
        ((round_free 64).append ((show ReturnFree feedForward by decide).append
          (show ReturnFree advanceBlock by decide))))))

private theorem block_execution {base : Addr} {s out : CPU} (path : BlockPath base s out) :
    ImageExecution base s blockCode out := by
  obtain ⟨enter, loaded, expanded, start, finish, compressed, e, l, x, h, r, f, a⟩ := path
  simp only [blockCode, List.append_assoc]
  exact e.follow
    (l.follow (x.follow (h.follow (r.follow (f.follow a (by decide)) (round_free _)) (by decide))
      (expansion_free _)) (load_free _)) (by decide)

def blockLoop : Nat → List Instruction
  | 0 => []
  | n+1 => blockLoop n ++ blockCode

private theorem block_loop_free (n : Nat) : ReturnFree (blockLoop n) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.append block_free

private theorem loop_execution {base : Addr} {s out : CPU} {n : Nat}
    (path : BlockPathPrefix base s n out) : ImageExecution base s (blockLoop n) out := by
  induction path with
  | nil => exact .nil _
  | step _ next ih => exact ih.follow (block_execution next) (block_loop_free _)

private theorem tail_prefix_free (n : Nat) : ReturnFree (tailPrefix n) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.append (show ReturnFree tailCycle by decide)

private theorem tail_free (n : Nat) : ReturnFree (tailCode n) :=
  (tail_prefix_free n).append (show ReturnFree (tailCode 0) by decide)

private theorem marker_free (n : Nat) : ReturnFree (markerCode n) := by
  by_cases small : n < 56
  · simpa [markerCode, small] using (show ReturnFree (markerCode 0) by decide)
  · simpa [markerCode, small] using (show ReturnFree (markerCode 56) by decide)

def callBeforeReturn (size : Nat) : List Instruction :=
  saveFrame ++ headerBody ++ zeroPadding ++ lengthBody ++ tailCode (size % 64) ++
    markerCode (size % 64) ++ lengthSuffix ++ initialHashCode ++ blockLoop (size / 64) ++
    [blockGuard] ++ [phaseGuard] ++ paddingPhase ++
    blockLoop (if size % 64 < 56 then 1 else 2) ++ [blockGuard] ++ [phaseGuard] ++ digestCode

def callCode (size : Nat) : List Instruction := callBeforeReturn size ++ returnCode

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CallPath.decoded {base : Addr} {s out : CPU} {data : ByteArray}
    (path : CallPath base s out data) : ImageExecution base s (callCode data.size) out := by
  obtain ⟨frame, head, clear, start, copied, marked, padded, body, msgMid, msgExit, switch,
    padInit, padMid, padExit, digest, written,
    save, header, zero, length, copy, marker, suffix, iv, msg, msgEnd, choosePad, beginPad, pad, padEnd,
    chooseDigest, bytes, ret⟩ := path
  have digestExit := bytes.follow ret (by decide +kernel)
  have phaseExit := chooseDigest.follow digestExit (by decide)
  have padExit := padEnd.follow phaseExit (by decide)
  have padRuns := (loop_execution pad).follow padExit (block_loop_free _)
  have switched := beginPad.follow padRuns (by decide)
  have chosen := choosePad.follow switched (by decide)
  have msgExit := msgEnd.follow chosen (by decide)
  have hashing := (loop_execution msg).follow msgExit (block_loop_free _)
  have initialized := iv.follow hashing (by decide)
  have suffixed := suffix.follow initialized (by decide)
  have marked := marker.follow suffixed (marker_free _)
  have copied := copy.follow marked (tail_free _)
  have lengths := length.follow copied (by decide)
  have cleared := zero.follow lengths (by decide)
  have header := header.follow cleared (by decide)
  have full := save.follow header (by decide)
  simpa only [callCode, callBeforeReturn, paddingBlockCount, List.append_assoc] using full

theorem call_has_return (size : Nat) : ∃ i ∈ callCode size, i.op = .ret := by
  refine ⟨returnInst, ?_, rfl⟩
  simp [callCode, returnCode]

private theorem load_length (n : Nat) : (loadCode n).length = 17*n := by
  induction n with
  | zero => simp [loadCode]
  | succ n ih =>
    have step : loadCycle.length = 17 := by decide
    simp only [loadCode, List.length_append, ih, step, Nat.mul_succ]

private theorem expansion_length (n : Nat) : (expansionCode n).length = 31*n := by
  induction n with
  | zero => simp [expansionCode]
  | succ n ih =>
    have step : expansionCycle.length = 31 := by decide
    simp only [expansionCode, List.length_append, ih, step, Nat.mul_succ]

private theorem round_length (n : Nat) : (roundCode n).length = 52*n := by
  induction n with
  | zero => simp [roundCode]
  | succ n ih =>
    have step : roundCycle.length = 52 := by decide
    simp only [roundCode, List.length_append, ih, step, Nat.mul_succ]

private theorem block_length : blockCode.length = 5126 := by
  simp only [blockCode, List.length_append, load_length, expansion_length, round_length]
  decide

private theorem block_loop_length (n : Nat) : (blockLoop n).length = 5126*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [blockLoop, List.length_append, ih, block_length, Nat.mul_succ]

private theorem tail_prefix_length (n : Nat) : (tailPrefix n).length = 7*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : tailCycle.length = 7 := by decide
    simp only [tailPrefix, List.length_append, ih, step, Nat.mul_succ]

/-- Exact instruction count, including the return and both loop exit tests. -/
theorem call_instruction_count (size : Nat) : (callCode size).length =
    155 + 7*(size % 64) + 5126*(size / 64 + (if size % 64 < 56 then 1 else 2)) +
      (if size % 64 < 56 then 0 else 1) := by
  have tail : (tailCode (size % 64)).length = 7*(size % 64) + 1 := by
    simp only [tailCode, List.length_append, tail_prefix_length, List.length_cons, List.length_nil]
  have lengths : saveFrame.length = 9 ∧ headerBody.length = 3 ∧ zeroPadding.length = 16 ∧
      lengthBody.length = 6 ∧ lengthSuffix.length = 18 ∧ initialHashCode.length = 13 ∧
      paddingPhase.length = 4 ∧ digestCode.length = 64 ∧ returnCode.length = 11 := by decide
  rcases lengths with ⟨a, b, c, d, e, f, g, h, j⟩
  simp only [callCode, callBeforeReturn, List.length_append, a, b, c, d, e, f, g, h, j,
    tail, block_loop_length, List.length_cons, List.length_nil]
  by_cases short : size % 64 < 56
  · have marker : (markerCode (size % 64)).length = 6 := by
      simpa only [markerCode, if_pos short, if_pos (show 0 < 56 by decide)] using
        (show (markerCode 0).length = 6 by decide)
    simp only [marker, short, if_true]
    omega
  · have marker : (markerCode (size % 64)).length = 7 := by
      simpa only [markerCode, if_neg short, if_neg (show ¬56 < 56 by decide)] using
        (show (markerCode 56).length = 7 by decide)
    simp only [marker, short, if_false]
    omega

end Crypto.RISCV64
