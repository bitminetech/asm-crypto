import Proofs.HMACSHA256.ARM64Inner
import Proofs.HMACSHA256.ARM64StraightTrace

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference

set_option maxHeartbeats 3600000 in
theorem InnerTrace.same_trace {base : Addr} {s t : Arm64.State} {a b : ByteList}
    {xs ys : List InstructionObservation} (left : InnerTrace base s a xs) (right : InnerTrace base t b ys)
    (pc : s.pc = t.pc) (sp : s.sp = t.sp)
    (message : s.readReg64 .x20 = t.readReg64 .x20) (scratch : s.readReg64 .x21 = t.readReg64 .x21)
    (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size) :
    xs = ys := by
  have inputs : RegistersAgree [.sp, .x20, .x21] s t := by
    intro r present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact sp
    · exact message
    · exact scratch
  have header := range_agree_on (before := [.sp, .x20, .x21]) (after := [.sp, .x20, .x21])
    (by decide +kernel) left.writeHeader right.writeHeader left.headerLive right.headerLive pc sp inputs
  have mask := range_agree_on (before := [.sp, .x20, .x21]) (after := [.sp, .x20, .x8, .x12])
    (by decide +kernel) left.mask right.mask left.maskedLive right.maskedLive
    (left.headerPC.trans right.headerPC.symm) (header.2 .sp (by simp)) header.2
  have pad := range_agree_on (before := [.sp, .x20, .x8, .x12]) (after := [.sp, .x20])
    (by decide +kernel) left.pad right.pad left.paddedLive right.paddedLive
    (left.maskedPC.trans right.maskedPC.symm) (mask.2 .sp (by simp)) mask.2
  have copy := range_agree_on (before := [.sp, .x20]) (after := [])
    (by decide +kernel) left.prepareCopy right.prepareCopy left.copyLive right.copyLive
    (left.paddedPC.trans right.paddedPC.symm) (pad.2 .sp (by simp)) pad.2
  rw [left.trace, right.trace]
  simp only [innerEvents, header.1, mask.1, pad.1, copy.1, sp, message, scratch, offset, count]

end Crypto.HMACSHA256.ARM64
