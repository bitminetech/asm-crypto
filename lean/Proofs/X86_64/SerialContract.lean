import Proofs.X86_64.Access
import Proofs.X86_64.StackTrace

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

private theorem trace_unique {base s a b x y} (left : Execution base s x a)
    (right : Execution base s y b) (size : x.length = y.length) : x = y ∧ a = b := by
  induction left generalizing y b with
  | nil =>
    cases right with
    | nil => exact ⟨rfl,rfl⟩
    | cons => simp at size
  | @cons s mid out i trace fetched executed _ ih =>
    cases right with
    | nil => simp at size
    | cons other next tail =>
      obtain rfl := Option.some.inj (fetched.symm.trans other)
      obtain rfl := Option.some.inj (executed.symm.trans next)
      obtain ⟨rfl,rfl⟩ := ih tail (by simpa using size)
      exact ⟨rfl,rfl⟩

/-- Serial reference, ABI, stack and instruction guarantees about one and the
same run. The data operand observations use the upstream effective addresses. -/
structure SerialContract (base : Val) (s out : Cpu) (message : Crypto.Reference.ByteList)
    (trace : List (Val × Instr)) (observations : List (Val × List DataAccess)) : Prop
    extends CallResult s out message where
  returned : returnAt base (callSteps message.bytes.size) s = some out
  executed : Execution base s trace out
  count : trace.length = callSteps message.bytes.size
  last : trace.getLast?.map (fun e => isReturn e.2) = some true
  beforeReturn : ∀ e ∈ trace.dropLast, isReturn e.2 = false
  scalar : ∀ e ∈ trace, ScalarLeaf e.2
  layout : ∀ e ∈ trace, ((e.1-base).toNat,e.2) ∈ codeLayout
  operands : operandTrace (trace.map Prod.snd) s = some observations
  pcs : observations.map Prod.fst = trace.map Prod.fst
  exactStack : stackTrace (trace.map Prod.snd) s =
    trace.map (fun e => s.regs.get .rsp - BitVec.ofNat 64 (stackDepth (e.1-base).toNat))
  stackBound : ∀ p ∈ stackTrace (trace.map Prod.snd) s, ∃ used ≤ 504, p = s.regs.get .rsp - BitVec.ofNat 64 used
  platform : platformState out = platformState s

theorem sha256_serial_contract {base s message extent} (entry : CallerEntry base s message extent) :
    ∃ out trace observations, SerialContract base s out message trace observations := by
  obtain ⟨out,returned,result⟩ := sha256_serial _ _ _ _ entry
  obtain ⟨trace,actual,count,last,earlier⟩ := returnAt_execution returned
  obtain ⟨obs,accesses,pcs⟩ := actual.operand_trace
  obtain ⟨_,_,layoutRun,_,layoutCount,sites⟩ := sha256_instruction_boundaries entry
  obtain ⟨rfl,rfl⟩ := trace_unique actual layoutRun (count.trans layoutCount.symm)
  obtain ⟨_,_,stackRun,_,stackCount,depth,bound⟩ := sha256_stack_bound entry
  obtain ⟨rfl,rfl⟩ := trace_unique actual stackRun (count.trans stackCount.symm)
  exact ⟨_,_,_,⟨result,returned,actual,count,last,earlier,actual.scalar,sites,accesses,pcs,depth,bound,actual.platform⟩⟩

end Crypto.X86_64
