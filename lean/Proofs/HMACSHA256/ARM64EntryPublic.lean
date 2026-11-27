import Proofs.HMACSHA256.ARM64InnerPublic
import Proofs.HMACSHA256.ARM64KeyPublic

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.ARM64.Imported

structure EntryPublic (s t : Arm64.State) (keyA keyB messageA messageB : ByteList) : Prop where
  pc : s.pc = t.pc
  sp : s.sp = t.sp
  link : s.readReg64 .lr = t.readReg64 .lr
  key : s.readReg64 .x0 = t.readReg64 .x0
  message : s.readReg64 .x1 = t.readReg64 .x1
  scratch : s.readReg64 .x2 = t.readReg64 .x2
  mac : s.readReg64 .x3 = t.readReg64 .x3
  keyOffset : keyA.offset = keyB.offset
  keyCount : keyA.bytes.size = keyB.bytes.size
  messageOffset : messageA.offset = messageB.offset
  messageCount : messageA.bytes.size = messageB.bytes.size

theorem EntrySuccessTrace.same_events {base : Addr} {s t : Arm64.State} {keyA keyB messageA messageB : ByteList}
    {capacity : Nat} (left : EntrySuccessTrace base s keyA messageA capacity)
    (right : EntrySuccessTrace base t keyB messageB capacity) (same : EntryPublic s t keyA keyB messageA messageB) :
    left.events = right.events := by
  have stack : s.sp - 160#64 = t.sp - 160#64 := congrArg (· - 160#64) same.sp
  have block : s.sp - 160#64 + 96#64 = t.sp - 160#64 + 96#64 := congrArg (· + 96#64) stack
  have key := key_whole_trace_equal left.keyTrace right.keyTrace
    ⟨left.keyPC.trans right.keyPC.symm, left.keySP.trans (stack.trans right.keySP.symm),
      left.keyInput.trans (same.key.trans right.keyInput.symm), left.keyOutput.trans (block.trans right.keyOutput.symm),
      left.keyLink.trans right.keyLink.symm, same.keyOffset, same.keyCount⟩
  have inner := left.innerTrace.same_trace right.innerTrace (left.innerPC.trans right.innerPC.symm)
    (left.innerSP.trans (stack.trans right.innerSP.symm))
    (left.messageInput.trans (same.message.trans right.messageInput.symm))
    (left.scratch.trans (same.scratch.trans right.scratch.symm)) same.messageOffset same.messageCount
  have finish := left.finishTrace.same_trace right.finishTrace
    ⟨left.finishPC.trans right.finishPC.symm, left.finishSP.trans (stack.trans right.finishSP.symm),
      left.finishInput.trans ((congrArg (· + 8#64) same.scratch).trans right.finishInput.symm),
      left.finishKey.trans (block.trans right.finishKey.symm), left.finishMac.trans (same.mac.trans right.finishMac.symm),
      left.finishLink.trans right.finishLink.symm, rfl, by simp only [hmacInner_length, same.messageCount]⟩
  simp only [EntrySuccessTrace.events, key, inner, finish, stack]

theorem EntryTrace.same_trace {base : Addr} {s t : Arm64.State} {keyA keyB messageA messageB : ByteList}
    {xs ys : List InstructionObservation} {capacity : Nat}
    (left : EntryTrace base s keyA messageA capacity xs) (right : EntryTrace base t keyB messageB capacity ys)
    (same : EntryPublic s t keyA keyB messageA messageB) : xs = ys := by
  have frontTrace : entryPrefixEvents base s capacity messageA.bytes.size =
      entryPrefixEvents base t capacity messageB.bytes.size := by
    simp only [entryPrefixEvents, same.pc, same.sp, same.scratch, same.message, same.messageCount]
  have returnTrace : entryReturnEvents base s = entryReturnEvents base t := by
    simp only [entryReturnEvents, same.sp, same.link]
  have required : hmacScratchRequired messageA = hmacScratchRequired messageB := by
    simp only [hmacScratchRequired, same.messageCount]
  cases left with
  | small small =>
    cases right with
    | small => rw [frontTrace, returnTrace]
    | full room _ => omega
  | full room leftBody =>
    cases right with
    | small small => omega
    | full _ rightBody => rw [frontTrace, returnTrace, leftBody.same_events rightBody same]

theorem entry_scheduled_public {base : Addr} {s t : Arm64.State} {keyA keyB msgA msgB : ByteList}
    {keyExtentA keyExtentB msgExtentA msgExtentB capacity : Nat}
    (left : EntryCall base s keyA msgA keyExtentA msgExtentA capacity)
    (right : EntryCall base t keyB msgB keyExtentB msgExtentB capacity) (same : EntryPublic s t keyA keyB msgA msgB)
    (envS : NativeEnvironment (entryBorrow base s keyExtentA msgExtentA capacity) s)
    (envT : NativeEnvironment (entryBorrow base t keyExtentB msgExtentB capacity) t) :
    ∃ outS outT obs, ScheduledExecution base envS.schedule 0 s obs outS ∧
      ScheduledExecution base envT.schedule 0 t obs outT ∧ outS.pc = outT.pc ∧ outS.sp = outT.sp := by
  obtain ⟨outS, xs, runS, resultS, _, traceS⟩ := entry_execution_concurrent left envS
  obtain ⟨outT, ys, runT, resultT, _, traceT⟩ := entry_execution_concurrent right envT
  have observations := traceS.same_trace traceT same
  exact ⟨outS, outT, xs, runS, observations.symm ▸ runT,
    resultS.link.trans (same.link.trans resultT.link.symm), resultS.sp.trans (same.sp.trans resultT.sp.symm)⟩

end Crypto.HMACSHA256.ARM64
