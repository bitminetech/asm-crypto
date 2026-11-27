import Proofs.HMACSHA256.RISCV64Program
import Proofs.RISCV64.ModeledBaseline

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference

def shaInstructionEvents : List Instruction → CPU → List (List Access)
  | [], _ => []
  | i :: code, s => i.observations s :: shaInstructionEvents code (i.step s)

private theorem sha_events_flatten (code : List Instruction) (s : CPU) :
    (shaInstructionEvents code s).flatten = accessTrace code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i tail ih => simp only [shaInstructionEvents, List.flatten_cons, accessTrace, ih]

private theorem sha_events_count (code : List Instruction) (s : CPU) :
    (shaInstructionEvents code s).length = code.length := by
  induction code generalizing s with
  | nil => rfl
  | cons i tail ih => simp only [shaInstructionEvents, List.length_cons, ih]

private theorem observation_count_fixed (i : Instruction) (s t : CPU) :
    (i.observations s).length = (i.observations t).length := by
  rcases i with ⟨op, bytes⟩
  cases op <;> rfl

private theorem same_sha_events (code : List Instruction) (s t : CPU)
    (same : accessTrace code s = accessTrace code t) :
    shaInstructionEvents code s = shaInstructionEvents code t := by
  induction code generalizing s t with
  | nil => rfl
  | cons i tail ih =>
    have flat : i.observations s ++ accessTrace tail (i.step s) =
        i.observations t ++ accessTrace tail (i.step t) := same
    obtain ⟨head, rest⟩ := List.append_inj flat (observation_count_fixed i s t)
    simp only [shaInstructionEvents, head, ih _ _ rest]

private theorem sha_path_executed {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution (shaAddress base) s code out)
    (allowed : PermittedPath (shaAddress base) s code) :
    ProgramExecution base s (shaInstructionEvents code s) out := by
  induction path with
  | nil => exact .nil _
  | @cons s out i tail decoded last remaining ih =>
    cases allowed with
    | cons loaded readable rest =>
      exact .cons (.sha (checked_step_loaded _ _ _ loaded decoded readable)) (ih rest)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
/-- The SHA-256 instructions reached by the HMAC link use precisely the
checked SHA-256 path and its existing observation function. -/
theorem sha_execution_observations (base : Addr) (s : CPU) (message : ByteList) (extent : Nat)
    (caller : CallerEntry (shaAddress base) s message extent) :
    ∃ out, runUntilReturn (shaAddress base) s (callSteps message.bytes.size) = some out ∧
      ProgramExecution base s (shaInstructionEvents (callCode message.bytes.size) s) out ∧
      (shaInstructionEvents (callCode message.bytes.size) s).length = callSteps message.bytes.size := by
  obtain ⟨inputs, grants⟩ := caller.decoded_layout
  obtain ⟨out, constructed, _⟩ := serial_sha256 (shaAddress base) s message.bytes inputs caller.output_outside
  have path := constructed.decoded
  have data := call_initial_data_permitted (shaAddress base) s message.bytes inputs grants
  have safe := path.initial_permitted s.mem (by have := caller.imageAligned; omega) caller.textExecute data
  have allowed := permittedPath_of_accesses (shaAddress base) s _ caller.loaded caller.imageReadOnly safe
  have returned := path.to_first_return allowed (call_has_return message.bytes.size)
  rw [call_instruction_count] at returned
  exact ⟨out, returned, sha_path_executed path allowed,
    (sha_events_count _ _).trans (call_instruction_count _)⟩

theorem sha_instruction_events_public (base : Addr) (s t : CPU) (a b : ByteList) (n m : Nat)
    (left : CallerEntry base s a n) (right : CallerEntry base t b m)
    (publicCall : SamePublicCall s t a b) :
    shaInstructionEvents (callCode a.bytes.size) s = shaInstructionEvents (callCode b.bytes.size) t := by
  have trace := caller_public_trace base s t a b n m left right publicCall
  rw [← publicCall.count] at trace ⊢
  exact same_sha_events _ s t trace

/-- Equal public SHA-256 call data gives the same per-instruction trace in
the linked HMAC execution, including the return to the HMAC call site. -/
theorem sha_segment_public (base : Addr) (s t : CPU) (a b : ByteList) (n m : Nat)
    (left : CallerEntry (shaAddress base) s a n) (right : CallerEntry (shaAddress base) t b m)
    (publicCall : SamePublicCall s t a b) :
    ∃ out other events,
      runUntilReturn (shaAddress base) s (callSteps a.bytes.size) = some out ∧
      runUntilReturn (shaAddress base) t (callSteps b.bytes.size) = some other ∧
      ProgramExecution base s events out ∧ ProgramExecution base t events other := by
  obtain ⟨out, ret, first, _⟩ := sha_execution_observations base s a n left
  obtain ⟨other, ret', second, _⟩ := sha_execution_observations base t b m right
  have trace := caller_public_trace (shaAddress base) s t a b n m left right publicCall
  rw [← publicCall.count] at trace second
  have same := same_sha_events _ s t trace
  exact ⟨out, other, _, ret, ret', first, same.symm ▸ second⟩

end Crypto.HMACSHA256.RISCV64
