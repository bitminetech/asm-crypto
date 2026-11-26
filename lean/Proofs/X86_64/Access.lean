import Proofs.X86_64.WordTrace
import Proofs.X86_64.PlatformFrame
import Proofs.X86_64.Observations

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

def WordAccess.dword (a : WordAccess) : DataAccess := ⟨a.write,a.address,4⟩

/-- The word-loop proof computes exactly the effective addresses from the
upstream ISA memory operand, including its index scale and displacement. -/
theorem word_accesses (i : WordInst) (len : Nat) (s : Cpu) :
    dataAccesses ⟨i.op,len⟩ s = some ((i.access (project s)).toList.map WordAccess.dword) := by
  cases i with
  | rr op dst src | rm op dst src =>
    cases op <;> simp [dataAccesses, WordInst.op, WordOp.opcode, operandAccess, WordInst.access,
      WordAccess.dword, Indexed.ea, Indexed.addr, Ea.addr, Ea.offset, Scale.toVal, project, Size.bytes]
  | _ =>
    simp [dataAccesses, WordInst.op, operandAccess, WordInst.access,
      WordAccess.dword, Indexed.ea, Indexed.addr, Ea.addr, Ea.offset, Scale.toVal, project, Size.bytes]

/-- Observe the data operands of an instruction list at successive ISA states.
An unsupported operation produces no trace. -/
def operandTrace : List Instr → Cpu → Option (List (Val × List DataAccess))
  | [], _ => some []
  | i :: rest, s => do
    let accesses ← dataAccesses i s
    return (s.rip, accesses) :: (← operandTrace rest (X86.step i s))

theorem word_operand_trace (block : WordBlock) (s : Cpu) :
    operandTrace (instructions block) s = some ((wordTrace block s).map
      (fun e => (e.1, e.2.toList.map WordAccess.dword))) := by
  induction block generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,len⟩ := p
    rw [show instructions ((i,len)::rest) = ⟨i.op,len⟩ :: instructions rest from rfl]
    simp [operandTrace,word_accesses,wordTrace,ih]

/-- Whole-call fetched instructions admit a data-operand trace, ending in the
implicit stack read of RET. -/
theorem Execution.operand_trace {base s trace out} (run : Execution base s trace out) :
    ∃ observations, operandTrace (trace.map Prod.snd) s = some observations ∧
      observations.map Prod.fst = trace.map Prod.fst := by
  induction run with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons s next out i trace fetched executed _ ih =>
    have one : X86.step i s = next := by
      cases h : s.stopped with
      | true => simp [stepLoaded, h, guard] at executed
      | false => simpa [stepLoaded, h, guard, fetched] using executed
    obtain ⟨accesses, known⟩ := scalar_accesses_defined i s (fetched_scalar fetched)
    obtain ⟨later, tail, clocks⟩ := ih
    exact ⟨(s.rip,accesses)::later,by simp [operandTrace,known,one,tail],by simp [clocks]⟩

theorem sha256_operand_trace {base s message extent} (entry : CallerEntry base s message extent) :
    ∃ out trace observations, Execution base s trace out ∧ CallResult s out message ∧
      operandTrace (trace.map Prod.snd) s = some observations ∧
      observations.map Prod.fst = trace.map Prod.fst ∧ observations.length = callSteps message.bytes.size := by
  obtain ⟨out,trace,actual,result,count,_⟩ := sha256_execution _ _ _ _ entry
  obtain ⟨observations,accesses,pcs⟩ := actual.operand_trace
  have len : observations.length = trace.length := by simpa only [List.length_map] using congrArg List.length pcs
  exact ⟨out,trace,observations,actual,result,accesses,pcs,len.trans count⟩

theorem Execution.observe {base s trace out} (run : Execution base s trace out) :
    ∃ events, ObservedExecution base s events out ∧
      events.map (fun e => (e.1,e.2.1)) = trace ∧
      operandTrace (trace.map Prod.snd) s = some (events.map (fun e => (e.1,e.2.2))) := by
  induction run with
  | nil => exact ⟨[], .nil _, rfl, rfl⟩
  | @cons s next out i trace fetched executed rest ih =>
    have eq : X86.step i s = next := by
      cases stopped : s.stopped with
      | true => simp [stepLoaded, stopped, guard] at executed
      | false => simpa [stepLoaded, stopped, guard, fetched] using executed
    obtain ⟨accesses, known⟩ := scalar_accesses_defined i s (fetched_scalar fetched)
    obtain ⟨events, steps, code, observation⟩ := ih
    exact ⟨(_,i,accesses)::events, .cons fetched executed known steps, by simp [code],
      by simp [operandTrace, known, eq, observation]⟩

end Crypto.X86_64
