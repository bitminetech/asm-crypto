import Proofs.HMACSHA256.RISCV64Finish
import Proofs.HMACSHA256.RISCV64FrameTrace
import Proofs.HMACSHA256.RISCV64PadTrace
import Proofs.HMACSHA256.RISCV64ShaTrace

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference

def finishInnerSetupEvents (pc : Addr) : List (List Access) :=
  [[.fetch pc 2], [.fetch (pc + 2#64) 2], [.fetch (pc + 4#64) 2], [.fetch (pc + 6#64) 4]]

def finishHeaderEvents (pc sp : Addr) : List (List Access) :=
  [[.fetch pc 4], [.fetch (pc + 4#64) 2, .write sp .double],
    [.fetch (pc + 6#64) 2], [.fetch (pc + 8#64) 2, .write (sp + 8#64) .double],
    [.fetch (pc + 10#64) 4], [.fetch (pc + 14#64) 2, .write (sp + 16#64) .double]]

def finishMaskEvents (pc : Addr) : List (List Access) :=
  [(0, 4), (4, 4), (8, 2), (10, 4), (14, 2), (16, 4), (20, 2), (22, 4), (26, 4)].map
    fun (offset, width) => [.fetch (pc + BitVec.ofNat 64 offset) width]

def finishOuterSetupEvents (pc : Addr) : List (List Access) :=
  [[.fetch pc 2], [.fetch (pc + 2#64) 2], [.fetch (pc + 4#64) 4]]

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem finish_inner_setup_events (s : CPU) :
    runOpsEvents ((decodeRange finish 0x1c 4).getD []) s = finishInnerSetupEvents s.pc := by
  rw [finish_first_decoded, Option.getD_some]
  simp (config := {decide := true}) [finishInnerSetupEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, BitVec.add_assoc]

theorem finish_header_events (s : CPU) :
    runOpsEvents ((decodeRange finish 0x26 6).getD []) s = finishHeaderEvents s.pc (s.reg 2#5) := by
  rw [finish_header_decoded, Option.getD_some]
  simp (config := {decide := true}) [finishHeaderEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, pc_advance, pc_put, pc_write,
    reg_advance, reg_put, reg_write, BitVec.add_assoc]

theorem finish_mask_events (s : CPU) :
    runOpsEvents ((decodeRange finish 0x36 9).getD []) s = finishMaskEvents s.pc := by
  rw [outer_mask_decoded, Option.getD_some]
  simp (config := {decide := true}) [finishMaskEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, pc_advance, pc_put, setPC,
    BitVec.add_assoc]

theorem finish_outer_setup_events (s : CPU) :
    runOpsEvents ((decodeRange finish 0xb4 3).getD []) s = finishOuterSetupEvents s.pc := by
  rw [outer_call_decoded, Option.getD_some]
  simp (config := {decide := true}) [finishOuterSetupEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, pc_advance, pc_put, BitVec.add_assoc]

theorem public_sha_registers {s t : CPU} (pc : s.pc = t.pc) (link : s.reg 1#5 = t.reg 1#5)
    (stack : s.reg 2#5 = t.reg 2#5) (input : s.reg 10#5 = t.reg 10#5)
    (output : s.reg 11#5 = t.reg 11#5) :
    PublicAgreement (publicRegs entryPublicRegs) s t := by
  refine ⟨pc, ?_⟩
  intro r included
  simp only [publicRegs, entryPublicRegs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with h | h | h | h | h <;> subst r
  · rw [reg_zero, reg_zero]
  · exact link
  · exact stack
  · exact input
  · exact output

theorem sha_same_public_data {base : Addr} {s t : CPU} {a b : ByteList} {n m : Nat}
    (one : CallerEntry base s a n) (two : CallerEntry base t b m)
    (regs : PublicAgreement (publicRegs entryPublicRegs) s t)
    (offset : a.offset = b.offset) (length : a.bytes.size = b.bytes.size) :
    SamePublicCall s t a b := by
  have pointer := regs.reg 10#5 (by decide)
  refine ⟨regs, length, ?_⟩
  unfold inputPayload
  rw [one.offsetValue, two.offsetValue]
  change s.reg 10#5 + BitVec.ofNat 64 a.offset = t.reg 10#5 + BitVec.ofNat 64 b.offset
  rw [pointer, offset]

theorem same_sha_instruction_events {base : Addr} {s t : CPU} {a b : ByteList} {n m : Nat}
    (one : CallerEntry base s a n) (two : CallerEntry base t b m)
    (same : SamePublicCall s t a b) :
    shaInstructionEvents (callCode a.bytes.size) s = shaInstructionEvents (callCode b.bytes.size) t := by
  exact sha_instruction_events_public base s t a b n m one two same


/-- The trace of the finishing helper contains public stack, key and code
addresses, and the two checked SHA-256 observations on the real call states. -/
def FinishTrace (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock)
    (events : List (List Access)) : Prop :=
  let text := routineAddress base finish
  let frame := s.reg 2#5 - 240#64
  let innerState := innerCallState (enteredFrame .finish s)
  let outer := hmacOuter k0 (sha256 inner).2
  ∃ (outerList : CPU) (extent : Nat),
    CallerEntry (shaAddress base) innerState inner extent ∧
    CallerEntry (shaAddress base) (outerCallState outerList) outer 120 ∧
    outerList.pc = text + 0xb4#64 ∧
    outerList.reg 2#5 = frame ∧ outerList.reg 18#5 = s.reg 12#5 ∧
    events =
      prologueEvents .finish s.pc (s.reg 2#5) ++
      finishInnerSetupEvents (text + 0x1c#64) ++
      shaInstructionEvents (callCode inner.bytes.size) innerState ++
      finishHeaderEvents (text + 0x26#64) frame ++
      finishMaskEvents (text + 0x36#64) ++
      padEvents 4 (text + 0x54#64) (s.reg 11#5) (frame + 24#64) 8 ++
      finishOuterSetupEvents (text + 0xb4#64) ++
      shaInstructionEvents (callCode outer.bytes.size) (outerCallState outerList) ++
      epilogueEvents .finish (text + 0xbc#64) frame

theorem finish_same_trace {base : Addr} {s t : CPU} {a b : ByteList} {k0 k1 : HmacKeyBlock}
    {xs ys : List (List Access)}
    (left : FinishTrace base s a k0 xs) (right : FinishTrace base t b k1 ys)
    (pc : s.pc = t.pc) (sp : s.reg 2#5 = t.reg 2#5)
    (input : s.reg 10#5 = t.reg 10#5) (keyPtr : s.reg 11#5 = t.reg 11#5)
    (output : s.reg 12#5 = t.reg 12#5)
    (offset : a.offset = b.offset) (count : a.bytes.size = b.bytes.size) :
    xs = ys := by
  obtain ⟨outerA, na, innerA, outerEntryA, pcA, spA, macA, traceA⟩ := left
  obtain ⟨outerB, nb, innerB, outerEntryB, pcB, spB, macB, traceB⟩ := right
  let startA := enteredFrame .finish s
  let startB := enteredFrame .finish t
  have startPC : startA.pc = startB.pc := by
    change (enteredFrame .finish s).pc = (enteredFrame .finish t).pc
    rw [enteredFrame_pc, enteredFrame_pc, pc]
  have startSP : startA.reg 2#5 = startB.reg 2#5 := by
    change (enteredFrame .finish s).reg 2#5 = (enteredFrame .finish t).reg 2#5
    rw [enteredFrame_sp, enteredFrame_sp, sp]
  have startInput : startA.reg 10#5 = startB.reg 10#5 := by
    change (enteredFrame .finish s).reg 10#5 = (enteredFrame .finish t).reg 10#5
    rw [enteredFrame_reg _ _ _ (by decide), enteredFrame_reg _ _ _ (by decide), input]
  obtain ⟨inA, outA, _, _, stackA, linkA, _⟩ := inner_call_registers startA
  obtain ⟨inB, outB, _, _, stackB, linkB, _⟩ := inner_call_registers startB
  have firstPublic : SamePublicCall (innerCallState startA) (innerCallState startB) a b :=
    sha_same_public_data innerA innerB
      (public_sha_registers (innerA.pc.trans innerB.pc.symm)
        (linkA.trans (congrArg (· + 10#64) startPC) |>.trans linkB.symm)
        (stackA.trans startSP |>.trans stackB.symm) (inA.trans startInput |>.trans inB.symm)
        (outA.trans (congrArg (· + 88#64) startSP) |>.trans outB.symm))
      offset count
  have outerSP : outerA.reg 2#5 = outerB.reg 2#5 := by rw [spA, spB, sp]
  have outerMac : outerA.reg 18#5 = outerB.reg 18#5 := by rw [macA, macB, output]
  have outerPC := pcA.trans pcB.symm
  obtain ⟨inA, outA, stackA, linkA, _⟩ := outer_call_registers outerA
  obtain ⟨inB, outB, stackB, linkB, _⟩ := outer_call_registers outerB
  have secondPublic : SamePublicCall (outerCallState outerA) (outerCallState outerB)
      (hmacOuter k0 (sha256 a).2) (hmacOuter k1 (sha256 b).2) :=
    sha_same_public_data outerEntryA outerEntryB
      (public_sha_registers (outerEntryA.pc.trans outerEntryB.pc.symm)
        (linkA.trans (congrArg (· + 8#64) outerPC) |>.trans linkB.symm)
        (stackA.trans outerSP |>.trans stackB.symm) (inA.trans outerSP |>.trans inB.symm)
        (outA.trans outerMac |>.trans outB.symm))
      rfl ((hmacOuter_length _ _).trans (hmacOuter_length _ _).symm)
  rw [traceA, traceB, same_sha_instruction_events innerA innerB firstPublic,
    same_sha_instruction_events outerEntryA outerEntryB secondPublic, pc, sp, keyPtr]

end Crypto.HMACSHA256.RISCV64
