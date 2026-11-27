import Proofs.HMACSHA256.X86Frame
import Proofs.HMACSHA256.X86Guard
import Proofs.HMACSHA256.X86Return
import Proofs.HMACSHA256.X86CallSites

namespace Crypto.HMACSHA256.X86_64

open X86

theorem entry_capacity_decoded : decodeRange entry 0xe 7 = some [
  ⟨.mov .q (.reg .rbx) (.reg .rdi), 3⟩,
  ⟨.mov .q (.reg .rbp) (.reg .rsi), 3⟩,
  ⟨.mov .q (.reg .r12) (.reg .rdx), 3⟩,
  ⟨.mov .q (.reg .r13) (.reg .rcx), 3⟩,
  ⟨.mov .d (.reg .rax) (.imm 1#64), 5⟩,
  ⟨.mov .q (.reg .rcx) (.mem { base := some .r12 }), 4⟩,
  ⟨.mov .q (.reg .rdx) (.mem { base := some .rbp, disp := 16#64 }), 4⟩] := by decide +kernel

def capacityState (s : Cpu) : Cpu :=
  let r := s.regs
  { s with
    regs := (((((r.set .rbx (r.get .rdi)).set .rbp (r.get .rsi)).set .r12 (r.get .rdx)).set
      .r13 (r.get .rcx)).set .rax 1#64).set
        .rcx (s.mem.readSize .q (r.get .rdx)) |>.set .rdx (s.mem.readSize .q (r.get .rsi + 16#64)),
    rip := s.rip + 25#64 }

theorem set_buffer_status (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.mov .d (.reg .rax) (.imm 1#64), 5⟩ s =
      { s with regs := s.regs.set .rax 1#64, rip := s.rip + 5#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Value.writeView, Value.trunc]
  rfl

theorem load_argument_word (s : Cpu) (dst : GPR) (address : Ea) (len : Nat)
    (live : s.ms = none) (unlocked : address.lock = false) :
    X86.step ⟨.mov .q (.reg dst) (.mem address), len⟩ s =
      { s with regs := s.regs.set dst (s.mem.readSize .q (address.addr s
          (s.rip + BitVec.ofNat 64 len))), rip := s.rip + BitVec.ofNat 64 len } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Value.writeView, Cpu.readMem, unlocked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
/-- Decode the actual argument moves and the two public capacity reads. -/
theorem entry_capacity_setup (s : Cpu) (live : s.ms = none) :
    runRange entry 0xe 7 s = some (capacityState s) := by
  unfold runRange
  rw [entry_capacity_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [move_reg _ .rbx .rdi _ live]
  rw [move_reg _ .rbp .rsi] <;> try exact live
  rw [move_reg _ .r12 .rdx] <;> try exact live
  rw [move_reg _ .r13 .rcx] <;> try exact live
  rw [set_buffer_status] <;> try exact live
  rw [load_argument_word _ .rcx]
  case live => exact live
  case unlocked => rfl
  rw [load_argument_word _ .rdx]
  case live => exact live
  case unlocked => rfl
  simp (config := {decide := true}) only [capacityState, Ea.addr, Ea.offset, Regs.get_set_ne,
    Regs.get_set_same, if_false, show (0 : Val) = 0#64 from rfl,
    BitVec.zero_add, BitVec.add_zero, BitVec.add_assoc] <;> rfl

theorem capacity_state_registers (s : Cpu) :
    (capacityState s).regs.get .rcx = s.mem.readSize .q (s.regs.get .rdx) ∧
    (capacityState s).regs.get .rdx = s.mem.readSize .q (s.regs.get .rsi + 16#64) ∧
    (capacityState s).regs.get .rax = 1#64 ∧
    (capacityState s).regs.get .rbx = s.regs.get .rdi ∧
    (capacityState s).regs.get .rbp = s.regs.get .rsi ∧
    (capacityState s).regs.get .r12 = s.regs.get .rdx ∧
    (capacityState s).regs.get .r13 = s.regs.get .rcx ∧
    (capacityState s).regs.get .rsp = s.regs.get .rsp := by
  simp (config := {decide := true}) only [capacityState, Regs.get_set_ne, Regs.get_set_same, and_true]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
/-- The undersized path runs the decoded return with no helper call and no
memory stores after the prologue. The prologue's stack write footprint is
handled separately. -/
theorem undersized_entry (base : Val) (s : Cpu) (capacity count : Val)
    (pc : s.rip = routineAddress base entry) (live : s.ms = none)
    (capacityAt : (enteredFrame .entry s).mem.readSize .q (s.regs.get .rdx) = capacity)
    (countAt : (enteredFrame .entry s).mem.readSize .q (s.regs.get .rsi + 16#64) = count)
    (short : capacity.toNat < 96 + count.toNat)
    (epilogueCanonical : canonical (routineAddress base entry + 0x100#64) = true)
    (link : (enteredFrame .entry s).mem.readSize .q (s.regs.get .rsp) =
      s.mem.readSize .q (s.regs.get .rsp))
    (linkCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true) :
    ∃ loaded checked out,
      runRange entry 0 7 s = some (enteredFrame .entry s) ∧
      runRange entry 0xe 7 (enteredFrame .entry s) = some loaded ∧
      runGuard loaded = some checked ∧ checked.rip = routineAddress base entry + 0x100#64 ∧
      runRange entry 0x100 8 checked = some out ∧
      out.regs.get .rax = 1#64 ∧ out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧
      out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧ out.mem = (enteredFrame .entry s).mem := by
  let saved := enteredFrame .entry s
  let loaded := capacityState saved
  have savedLive : saved.ms = none := (entered_frame_live .entry s).trans live
  have loadedLive : loaded.ms = none := savedLive
  have loadedPC : loaded.rip = routineAddress base entry + 0x27#64 := by
    change saved.rip + 25#64 = _
    rw [entered_frame_pc, pc, BitVec.add_assoc]
    rfl
  have target : canonical (loaded.rip + 0xd9#64) = true := by
    rw [loadedPC, BitVec.add_assoc]
    exact epilogueCanonical
  obtain ⟨checked, guard, mem, running, regs, branch, _⟩ := runGuard_result loaded loadedLive target
  obtain ⟨cap, len, status, _, _, _, _, stack⟩ := capacity_state_registers saved
  have testedCapacity : loaded.regs.get .rcx = capacity := by
    rw [cap, entered_frame_register .entry s .rdx (by decide)]
    exact capacityAt
  have testedCount : loaded.regs.get .rdx = count := by
    rw [len, entered_frame_register .entry s .rsi (by decide)]
    exact countAt
  have reached : checked.rip = routineAddress base entry + 0x100#64 := by
    rw [branch, testedCapacity, testedCount, if_pos short, loadedPC, BitVec.add_assoc]
    rfl
  have sp : checked.regs.get .rsp = s.regs.get .rsp - 120#64 := by
    rw [regs .rsp (by decide), stack, entered_frame_stack, BitVec.sub_sub]
    rfl
  have targetSlot : checked.mem.readSize .q (checked.regs.get .rsp + 120#64) =
      s.mem.readSize .q (s.regs.get .rsp) := by
    rw [sp, BitVec.sub_add_cancel, mem]
    exact link
  have returnOk := (returns checked running).1 (by rw [targetSlot]; exact linkCanonical)
  let out := restoredState checked 72#64 4
  obtain ⟨outStack, outPC, outMem⟩ := restored_stack_and_link checked 72#64 4
  have savedStatus : out.regs.get .rax = checked.regs.get .rax := restored_status _ _ _
  have status := (savedStatus.trans (regs .rax (by decide))).trans status
  refine ⟨loaded, checked, out, enter_frame .entry s live, entry_capacity_setup saved savedLive,
    guard, reached, returnOk, status, ?_, ?_, outMem.trans mem⟩
  · rw [outStack, sp, BitVec.add_assoc, show 72#64 + 56#64 = 120#64 + 8#64 from rfl,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  · rw [outPC, BitVec.add_assoc]
    exact targetSlot

end Crypto.HMACSHA256.X86_64
