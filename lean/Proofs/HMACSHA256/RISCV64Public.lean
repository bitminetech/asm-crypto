import Proofs.HMACSHA256.RISCV64HelperConcurrency
import Proofs.HMACSHA256.RISCV64Timing

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference

structure EntryPublic (s t : CPU) (keyA keyB messageA messageB : ByteList) : Prop where
  pc : s.pc = t.pc
  sp : s.reg 2#5 = t.reg 2#5
  link : s.reg 1#5 = t.reg 1#5
  key : s.reg 10#5 = t.reg 10#5
  message : s.reg 11#5 = t.reg 11#5
  scratch : s.reg 12#5 = t.reg 12#5
  mac : s.reg 13#5 = t.reg 13#5
  keyOffset : keyA.offset = keyB.offset
  keyCount : keyA.bytes.size = keyB.bytes.size
  messageOffset : messageA.offset = messageB.offset
  messageCount : messageA.bytes.size = messageB.bytes.size

private theorem preparation_same_trace {base : Addr} {s t : CPU} {keyA keyB messageA messageB : ByteList}
    {xs ys : List (List Access)} {capacity : Nat}
    (one : EntryPreparationTrace base s keyA messageA capacity xs)
    (two : EntryPreparationTrace base t keyB messageB capacity ys)
    (agree : EntryPublic s t keyA keyB messageA messageB) : xs = ys := by
  obtain ⟨calledA, afterA, eventsA, pcA, spA, inA, outA, keyTraceA, stackA, srcA, dstA, traceA⟩ := one
  obtain ⟨calledB, afterB, eventsB, pcB, spB, inB, outB, keyTraceB, stackB, srcB, dstB, traceB⟩ := two
  have spOff := congrArg (· - 176#64) agree.sp
  have sameKey := key_same_trace keyTraceA keyTraceB (pcA.trans pcB.symm)
    (spA.trans (spOff.trans spB.symm)) (inA.trans (agree.key.trans inB.symm))
    (outA.trans (spOff.trans outB.symm)) agree.keyOffset agree.keyCount
  have sameEntry : entryBeforeKeyEvents base s (BitVec.ofNat 64 capacity) =
      entryBeforeKeyEvents base t (BitVec.ofNat 64 capacity) := by
    simp only [entryBeforeKeyEvents, entryFrontEvents, agree.pc, agree.sp, agree.scratch, agree.message]
  have sameInner : entryInnerEvents base afterA messageA = entryInnerEvents base afterB messageB := by
    simp only [entryInnerEvents, stackA, stackB, agree.sp, srcA, srcB, agree.message, dstA, dstB,
      agree.scratch, agree.messageOffset, agree.messageCount]
  rw [traceA, traceB, sameEntry, sameKey, sameInner]

theorem entry_same_trace {base : Addr} {s t : CPU} {keyA keyB messageA messageB : ByteList}
    {xs ys : List (List Access)} {capacity : Nat}
    (one : EntryTrace base s keyA messageA capacity xs)
    (two : EntryTrace base t keyB messageB capacity ys)
    (agree : EntryPublic s t keyA keyB messageA messageB) : xs = ys := by
  by_cases small : capacity < 96 + messageA.bytes.size
  · have other : capacity < 96 + messageB.bytes.size := agree.messageCount ▸ small
    simp only [EntryTrace, if_pos small] at one
    simp only [EntryTrace, if_pos other] at two
    rw [one, two]
    simp only [entrySmallEvents, entryFrontEvents, entryReturnEvents, agree.pc, agree.sp,
      agree.scratch, agree.message]
  · have other : ¬ capacity < 96 + messageB.bytes.size := agree.messageCount ▸ small
    simp only [EntryTrace, if_neg small] at one
    simp only [EntryTrace, if_neg other] at two
    obtain ⟨finishA, beforeA, eventsA, prepA, pcA, spA, inA, kA, outA, hashA, traceA⟩ := one
    obtain ⟨finishB, beforeB, eventsB, prepB, pcB, spB, inB, kB, outB, hashB, traceB⟩ := two
    have before := preparation_same_trace prepA prepB agree
    have spOff := congrArg (· - 176#64) agree.sp
    have hashes := finish_same_trace hashA hashB (pcA.trans pcB.symm)
      (spA.trans (spOff.trans spB.symm))
      (inA.trans ((congrArg (· + 8#64) agree.scratch).trans inB.symm))
      (kA.trans (spOff.trans kB.symm)) (outA.trans (agree.mac.trans outB.symm)) rfl
      (by simp only [hmacInner_length, agree.messageCount])
    rw [traceA, traceB, before, hashes]
    simp only [entrySuccessReturnEvents, entryReturnEvents, agree.sp]

/-- Identical public entry data yields the same retired instruction and
operand trace in any two permitted schedules, including an undersized
call and either key-length branch. The target timing law gives equal cost. -/
theorem entry_public_execution {base : Addr} {s t : CPU} {keyA keyB messageA messageB : ByteList}
    {nA mA nB mB capacity : Nat} (left : EntryCall base s keyA messageA nA mA capacity)
    (right : EntryCall base t keyB messageB nB mB capacity)
    (envA : EntryEnvironment base s nA mA capacity) (envB : EntryEnvironment base t nB mB capacity)
    (agree : EntryPublic s t keyA keyB messageA messageB) (profile : LinkedTimingProfile base) :
    ∃ a b events cost, CostedScheduledExecution profile envA.schedule 0 s events a cost ∧
      CostedScheduledExecution profile envB.schedule 0 t events b cost := by
  obtain ⟨a, xs, runA, _, traceA, resultA, _⟩ := entry_execution_concurrent left envA
  obtain ⟨b, ys, runB, _, traceB, resultB, _⟩ := entry_execution_concurrent right envB
  have trace := entry_same_trace traceA traceB agree
  have pc := resultA.2.2.1.trans (agree.link.trans resultB.2.2.1.symm)
  rw [← trace] at runB
  obtain ⟨cost, first, second⟩ := scheduled_equal_timing runA runB pc profile
  exact ⟨a, b, xs, cost, first, second⟩

theorem key_public_execution {base : Addr} {s t : CPU} {a b : ByteList} {n m : Nat}
    (left : KeyCall base s a n) (right : KeyCall base t b m)
    (envA : NativeEnvironment (keyBorrow base s n) s) (envB : NativeEnvironment (keyBorrow base t m) t)
    (sp : s.reg 2#5 = t.reg 2#5) (link : s.reg 1#5 = t.reg 1#5)
    (input : s.reg 10#5 = t.reg 10#5) (output : s.reg 11#5 = t.reg 11#5)
    (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size)
    (profile : LinkedTimingProfile base) :
    ∃ u v events cost, CostedScheduledExecution profile envA.schedule 0 s events u cost ∧
      CostedScheduledExecution profile envB.schedule 0 t events v cost := by
  obtain ⟨u, xs, runA, _, traceA, returnA, _⟩ := key_execution_concurrent left envA
  obtain ⟨v, ys, runB, _, traceB, returnB, _⟩ := key_execution_concurrent right envB
  have agreement := key_same_trace traceA traceB (left.pc.trans right.pc.symm) sp input output offset count
  rw [← agreement] at runB
  obtain ⟨cost, first, second⟩ := scheduled_equal_timing runA runB (returnA.trans (link.trans returnB.symm)) profile
  exact ⟨u, v, xs, cost, first, second⟩

theorem finish_public_execution {base : Addr} {s t : CPU} {a b : ByteList} {k0 k1 : HmacKeyBlock} {n m : Nat}
    (left : FinishCall base s a k0 n) (right : FinishCall base t b k1 m)
    (envA : NativeEnvironment (finishBorrow base s n) s) (envB : NativeEnvironment (finishBorrow base t m) t)
    (sp : s.reg 2#5 = t.reg 2#5) (link : s.reg 1#5 = t.reg 1#5)
    (input : s.reg 10#5 = t.reg 10#5) (keyPtr : s.reg 11#5 = t.reg 11#5) (output : s.reg 12#5 = t.reg 12#5)
    (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size)
    (profile : LinkedTimingProfile base) :
    ∃ u v events cost, CostedScheduledExecution profile envA.schedule 0 s events u cost ∧
      CostedScheduledExecution profile envB.schedule 0 t events v cost := by
  obtain ⟨u, xs, runA, _, traceA, returnA, _⟩ := finish_execution_concurrent left envA
  obtain ⟨v, ys, runB, _, traceB, returnB, _⟩ := finish_execution_concurrent right envB
  have agreement := finish_same_trace traceA traceB (left.pc.trans right.pc.symm) sp input keyPtr output offset count
  rw [← agreement] at runB
  obtain ⟨cost, first, second⟩ := scheduled_equal_timing runA runB (returnA.trans (link.trans returnB.symm)) profile
  exact ⟨u, v, xs, cost, first, second⟩

end Crypto.HMACSHA256.RISCV64
