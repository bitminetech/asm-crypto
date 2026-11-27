import Proofs.HMACSHA256.ARM64Concurrency
import Proofs.HMACSHA256.ARM64StraightTrace
import Proofs.ARM64.ImportedConfidentialCall

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.ARM64.Imported

theorem ShaCallResult.same_observations {base : Addr} {s t outS outT : Arm64.State}
    {a b : ByteList} {xs ys : List InstructionObservation}
    (left : ShaCallResult base s outS a xs) (right : ShaCallResult base t outT b ys)
    (input : s.readReg64 .x0 = t.readReg64 .x0) (output : s.readReg64 .x1 = t.readReg64 .x1)
    (sp : s.sp = t.sp) (link : s.readReg64 .lr = t.readReg64 .lr)
    (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size) :
    xs = ys := by
  obtain ⟨extentS, entryS⟩ := left.caller
  obtain ⟨extentT, entryT⟩ := right.caller
  exact (sha256_observations_equal base s t a.bytes b.bytes
    (caller_entry_inputs base s a extentS entryS) (caller_entry_inputs base t b extentT entryT)
    ⟨input, output, sp, link, by rw [entryS.offsetValue, entryT.offsetValue, offset]⟩
    count outS outT xs ys left.trace right.trace).1

structure FinishPublic (s t : Arm64.State) (a b : ByteList) : Prop where
  pc : s.pc = t.pc
  sp : s.sp = t.sp
  input : s.readReg64 .x0 = t.readReg64 .x0
  key : s.readReg64 .x1 = t.readReg64 .x1
  output : s.readReg64 .x2 = t.readReg64 .x2
  link : s.readReg64 .lr = t.readReg64 .lr
  offset : a.offset = b.offset
  count : a.bytes.size = b.bytes.size

private theorem enter_arg (s : Arm64.State) (i : BitVec 5) (frame : Addr) (other : i ≠ 29#5) :
    (enteredState s frame).readReg64 (.gpr i) = s.readReg64 (.gpr i) := by
  by_cases zero : i = 31#5
  · subst i; rfl
  · simp only [enteredState, trace_read_reg_set_pc, Arm64.Reg.x29,
      trace_read_write_reg64 _ _ _ _ zero, if_neg (fun eq => other (Arm64.Reg.gpr.inj eq).symm),
      if_neg (show Arm64.Reg.sp ≠ .gpr i from by intro h; cases h), trace_read_reg_set_mem]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4800000 in
theorem FinishBody.same_trace {base : Addr} {s t outS outT : Arm64.State}
    {a b : ByteList} {k0 k1 : HmacKeyBlock}
    (left : FinishBody base (enteredState s 224#64) outS a k0)
    (right : FinishBody base (enteredState t 224#64) outT b k1)
    (same : FinishPublic s t a b) :
    left.nativeTrace = right.nativeTrace := by
  let u := enteredState s 224#64
  let v := enteredState t 224#64
  have pc : u.pc = v.pc := congrArg (· + 28#64) same.pc
  have sp : u.sp = v.sp := congrArg (· - 224#64) same.sp
  have innerPC := left.innerReturn.trans right.innerReturn.symm
  have innerSP := left.innerSP.trans (sp.trans right.innerSP.symm)
  have innerKey : left.afterInner.readReg64 .x19 = right.afterInner.readReg64 .x19 := by
    rw [left.innerKey, right.innerKey]
    change (enteredState s 224#64).readReg64 (.gpr 1) = (enteredState t 224#64).readReg64 (.gpr 1)
    rw [enter_arg s 1 _ (by decide), enter_arg t 1 _ (by decide)]
    exact same.key
  have innerSetup := range_agree_on (before := []) (after := [])
    (by decide +kernel) left.innerCall right.innerCall left.innerHash.started right.innerHash.started
    pc sp (by simp [RegistersAgree])
  obtain ⟨inL, dstL, _, _, linkL, spL, _⟩ := inner_call_registers u
  obtain ⟨inR, dstR, _, _, linkR, spR, _⟩ := inner_call_registers v
  have innerInputs : (innerCallState u).readReg64 .x0 = (innerCallState v).readReg64 .x0 := by
    rw [inL, inR]
    change (enteredState s 224#64).readReg64 (.gpr 0) = (enteredState t 224#64).readReg64 (.gpr 0)
    rw [enter_arg s 0 _ (by decide), enter_arg t 0 _ (by decide)]
    exact same.input
  have innerSHA := left.innerHash.same_observations right.innerHash innerInputs
    (dstL.trans ((congrArg (· + 184#64) sp).trans dstR.symm))
    (spL.trans (sp.trans spR.symm)) (linkL.trans ((congrArg (· + 16#64) pc).trans linkR.symm))
    same.offset same.count
  have readyL := run_range_running_before (by decide +kernel) left.outerCall left.outerHash.started
  have readyR := run_range_running_before (by decide +kernel) right.outerCall right.outerHash.started
  have padL := run_range_running_before (by decide +kernel) left.writePad readyL
  have padR := run_range_running_before (by decide +kernel) right.writePad readyR
  have headL := run_range_running_before (by decide +kernel) left.preparePad padL
  have headR := run_range_running_before (by decide +kernel) right.preparePad padR
  have headers := range_agree_on (before := [.sp, .x19]) (after := [.sp, .x19])
    (by decide +kernel) left.writeHeader right.writeHeader headL headR innerPC innerSP (by
      intro r present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · exact innerSP
      · exact innerKey)
  have headPC : left.header.pc = right.header.pc := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) left.writeHeader headL,
      run_range_end (by decide +kernel) (by decide +kernel) right.writeHeader headR, innerPC]
  have mask := range_agree_on (before := [.sp, .x19]) (after := [.sp, .x19, .x8])
    (by decide +kernel) left.preparePad right.preparePad padL padR headPC (headers.2 .sp (by simp)) headers.2
  have maskPC : left.mask.pc = right.mask.pc := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) left.preparePad padL,
      run_range_end (by decide +kernel) (by decide +kernel) right.preparePad padR, headPC]
  have pad := range_agree_on (before := [.sp, .x19, .x8]) (after := [])
    (by decide +kernel) left.writePad right.writePad readyL readyR maskPC (mask.2 .sp (by simp)) mask.2
  have outerPC : left.outerList.pc = right.outerList.pc := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) left.writePad readyL,
      run_range_end (by decide +kernel) (by decide +kernel) right.writePad readyR, maskPC]
  have outerSP := left.outerSP.trans (sp.trans right.outerSP.symm)
  have outerSetup := range_agree_on (before := []) (after := [])
    (by decide +kernel) left.outerCall right.outerCall left.outerHash.started right.outerHash.started
    outerPC outerSP (by simp [RegistersAgree])
  obtain ⟨srcL, macL, lrL, stackL, _⟩ := outer_call_registers left.outerList
  obtain ⟨srcR, macR, lrR, stackR, _⟩ := outer_call_registers right.outerList
  have mac : (outerCallState left.outerList).readReg64 .x1 =
      (outerCallState right.outerList).readReg64 .x1 := by
    rw [macL, macR, left.outerMac, right.outerMac]
    change (enteredState s 224#64).readReg64 (.gpr 2) = (enteredState t 224#64).readReg64 (.gpr 2)
    rw [enter_arg s 2 _ (by decide), enter_arg t 2 _ (by decide)]
    exact same.output
  have outerSHA := left.outerHash.same_observations right.outerHash
    (srcL.trans ((congrArg (· + 96#64) outerSP).trans srcR.symm)) mac
    (stackL.trans (outerSP.trans stackR.symm)) (lrL.trans ((congrArg (· + 12#64) outerPC).trans lrR.symm))
    (by rfl) (by rw [hmacOuter_length, hmacOuter_length])
  have enteredSP : (enteredState s 224#64).sp = (enteredState t 224#64).sp := sp
  simp only [FinishBody.nativeTrace, same.pc, same.sp, innerSetup.1, innerSHA, headers.1, mask.1, pad.1,
    outerSetup.1, outerSHA, left.outerReturn, right.outerReturn, left.sp, right.sp, enteredSP, same.link]

theorem finish_scheduled_public {base : Addr} {s t : Arm64.State} {a b : ByteList}
    {k0 k1 : HmacKeyBlock} {n m : Nat}
    (left : FinishCall base s a k0 n) (right : FinishCall base t b k1 m) (same : FinishPublic s t a b)
    (envS : NativeEnvironment (finishBorrow base s n) s)
    (envT : NativeEnvironment (finishBorrow base t m) t) :
    ∃ outS outT obs, ScheduledExecution base envS.schedule 0 s obs outS ∧
      ScheduledExecution base envT.schedule 0 t obs outT ∧ outS.pc = outT.pc ∧ outS.sp = outT.sp := by
  obtain ⟨outS, xs, runS, spS, pcS, _, _, _, _, _, _, leftBody, traceS⟩ := finish_execution_concurrent left envS
  obtain ⟨outT, ys, runT, spT, pcT, _, _, _, _, _, _, rightBody, traceT⟩ := finish_execution_concurrent right envT
  have observations := traceS.trans ((leftBody.same_trace rightBody same).trans traceT.symm)
  exact ⟨outS, outT, xs, runS, observations.symm ▸ runT,
    pcS.trans (same.link.trans pcT.symm), spS.trans (same.sp.trans spT.symm)⟩

end Crypto.HMACSHA256.ARM64
