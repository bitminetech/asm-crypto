import Proofs.HMACSHA256.ARM64FinishTrace

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.ARM64.Imported

private theorem key_body_trace_equal {base sp input output : Addr} {a b : ByteList}
    {xs ys : List InstructionObservation} (left : KeyBodyTrace base sp input output a xs)
    (right : KeyBodyTrace base sp input output b ys) (offset : a.offset = b.offset)
    (count : a.bytes.size = b.bytes.size) : xs = ys := by
  cases left with
  | short small =>
    cases right with
    | short => simp only [keyShortEvents, offset, count]
    | long large => omega
  | long large run inputA outputA stackA linkA =>
    cases right with
    | short small => omega
    | long _ other inputB outputB stackB linkB =>
      have observed := run.same_observations other (inputA.trans inputB.symm) (outputA.trans outputB.symm)
        (stackA.trans stackB.symm) (linkA.trans linkB.symm) offset count
      rw [observed]

structure KeyPublic (s t : Arm64.State) (a b : ByteList) : Prop where
  pc : s.pc = t.pc
  sp : s.sp = t.sp
  input : s.readReg64 .x0 = t.readReg64 .x0
  output : s.readReg64 .x1 = t.readReg64 .x1
  link : s.readReg64 .lr = t.readReg64 .lr
  offset : a.offset = b.offset
  count : a.bytes.size = b.bytes.size

theorem key_whole_trace_equal {base : Addr} {s t : Arm64.State} {a b : ByteList}
    {xs ys : List InstructionObservation} (left : KeyWholeTrace base s a xs)
    (right : KeyWholeTrace base t b ys) (same : KeyPublic s t a b) : xs = ys := by
  obtain ⟨u, bodyA, hA⟩ := left
  obtain ⟨v, bodyB, hB⟩ := right
  have rhs : KeyBodyTrace base (s.sp - 96#64) (s.readReg64 .x0) (s.readReg64 .x1) b v := by
    rw [same.sp, same.input, same.output]
    exact bodyB
  rw [hA, hB, key_body_trace_equal bodyA rhs same.offset same.count, same.pc, same.sp, same.output, same.link]

theorem key_scheduled_public {base : Addr} {s t : Arm64.State} {a b : ByteList} {n m : Nat}
    (left : KeyCall base s a n) (right : KeyCall base t b m) (same : KeyPublic s t a b)
    (envS : NativeEnvironment (keyBorrow base s n) s)
    (envT : NativeEnvironment (keyBorrow base t m) t) :
    ∃ outS outT obs, ScheduledExecution base envS.schedule 0 s obs outS ∧
      ScheduledExecution base envT.schedule 0 t obs outT ∧ outS.pc = outT.pc ∧ outS.sp = outT.sp := by
  obtain ⟨outS, xs, runS, spS, pcS, _, _, _, _, _, traceS⟩ := key_execution_concurrent left envS
  obtain ⟨outT, ys, runT, spT, pcT, _, _, _, _, _, traceT⟩ := key_execution_concurrent right envT
  have observations := key_whole_trace_equal traceS traceT same
  exact ⟨outS, outT, xs, runS, observations.symm ▸ runT,
    pcS.trans (same.link.trans pcT.symm), spS.trans (same.sp.trans spT.symm)⟩

end Crypto.HMACSHA256.ARM64
