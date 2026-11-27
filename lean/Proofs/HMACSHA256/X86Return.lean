import Proofs.HMACSHA256.X86Setup
import Proofs.X86_64.Entry

namespace Crypto.HMACSHA256.X86_64

open X86

def returnSlots : List (GPR × Nat) := [(.r15, 2), (.r14, 2), (.r13, 2), (.r12, 2), (.rbp, 1), (.rbx, 1)]

def popInstruction (item : GPR × Nat) : Instr := ⟨.pop .q (.reg item.1), item.2⟩

def returnCode (frame : Val) (len : Nat) : List Instr :=
  ⟨.bin .add .q (.reg .rsp) (.imm frame), len⟩ :: returnSlots.map popInstruction ++ [⟨.ret, 1⟩]

theorem entry_return_decoded :
    decodeRange entry 0x100 8 = some (returnCode 72#64 4) := by decide +kernel

theorem key_return_decoded :
    decodeRange key 0x44 8 = some (returnCode 8#64 4) := by decide +kernel

theorem finish_return_decoded :
    decodeRange finish 0xaf 8 = some (returnCode 136#64 7) := by decide +kernel

def releaseFrame (s : Cpu) (frame : Val) (len : Nat) : Cpu := { s with
  regs := s.regs.set .rsp (s.regs.get .rsp + frame)
  flags := Flags.add .q (s.regs.get .rsp) frame s.flags
  rip := s.rip + BitVec.ofNat 64 len }

theorem release_step (s : Cpu) (frame : Val) (len : Nat) (live : s.ms = none) :
    X86.step ⟨.bin .add .q (.reg .rsp) (.imm frame), len⟩ s = releaseFrame s frame len := by
  have q : Value.trunc .q frame = frame := by
    change frame &&& Size.q.mask = frame
    rw [show Size.q.mask = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.getReg, Cpu.writeOperand, Cpu.setFlags, Cpu.setReg, Cpu.setRip, Value.writeView,
    Flags.addResult, q, releaseFrame]

def restoreSlot (s : Cpu) (item : GPR × Nat) : Cpu := { s with
  regs := (s.regs.set .rsp (s.regs.get .rsp + 8#64)).set item.1 (s.mem.readSize .q (s.regs.get .rsp))
  rip := s.rip + BitVec.ofNat 64 item.2 }

theorem pop_step (s : Cpu) (item : GPR × Nat) (live : s.ms = none) :
    X86.step (popInstruction item) s = restoreSlot s item := by
  simp [popInstruction, X86.step, Cpu.stopped, live, Cpu.popValue, Cpu.writeOperand, Cpu.setReg,
    Cpu.readMem, Cpu.setRip, Size.bytes, Value.writeView, restoreSlot]

private theorem restored_slots (s : Cpu) (items : List (GPR × Nat)) (live : s.ms = none) :
    X86.run (items.map popInstruction) s = items.foldl restoreSlot s := by
  induction items generalizing s with
  | nil => rfl
  | cons item tail ih =>
    simp only [X86.run, List.map_cons, List.foldl_cons, pop_step _ _ live]
    exact ih _ live

def readyReturn (s : Cpu) (frame : Val) (len : Nat) : Cpu :=
  returnSlots.foldl restoreSlot (releaseFrame s frame len)

def restoredState (s : Cpu) (frame : Val) (len : Nat) : Cpu :=
  let before := readyReturn s frame len
  { before with
    regs := before.regs.set .rsp (before.regs.get .rsp + 8#64)
    rip := before.mem.readSize .q (before.regs.get .rsp) }

private theorem ret_step (s : Cpu) (live : s.ms = none)
    (canonicalTarget : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true) :
    X86.step ⟨.ret, 1⟩ s = { s with
      regs := s.regs.set .rsp (s.regs.get .rsp + 8#64)
      rip := s.mem.readSize .q (s.regs.get .rsp) } := by
  simp [X86.step, Cpu.stopped, live, Cpu.readMem, Cpu.setReg, Value.writeView, canonicalTarget]

private theorem return_run (s : Cpu) (frame : Val) (len : Nat) (live : s.ms = none)
    (target : canonical (s.mem.readSize .q (s.regs.get .rsp + frame + 48#64)) = true) :
    X86.run (returnCode frame len) s = restoredState s frame len := by
  have pops := restored_slots (releaseFrame s frame len) returnSlots live
  have split : X86.run (returnCode frame len) s =
      X86.step ⟨.ret, 1⟩ (X86.run (returnSlots.map popInstruction) (releaseFrame s frame len)) := by
    simp only [returnCode, List.cons_append, X86.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil, release_step _ _ _ live]
  rw [split, pops]
  have stack : (readyReturn s frame len).regs.get .rsp = s.regs.get .rsp + frame + 48#64 := by
    simp (config := { decide := true }) [readyReturn, returnSlots, restoreSlot, releaseFrame, BitVec.add_assoc]
  have memory : (readyReturn s frame len).mem = s.mem := by
    simp [readyReturn, returnSlots, restoreSlot, releaseFrame]
  have retLive : (readyReturn s frame len).ms = none := by
    simp [readyReturn, returnSlots, restoreSlot, releaseFrame, live]
  have retTarget : canonical ((readyReturn s frame len).mem.readSize .q
      ((readyReturn s frame len).regs.get .rsp)) = true := by
    rw [memory, stack]
    exact target
  change X86.step ⟨.ret, 1⟩ (readyReturn s frame len) = _
  rw [ret_step _ retLive retTarget]
  rfl

/-- All three linked epilogues release their own frame, load the saved
registers and return through the original stack slot. -/
theorem returns (s : Cpu) (live : s.ms = none) :
    (canonical (s.mem.readSize .q (s.regs.get .rsp + 120#64)) = true →
      runRange entry 0x100 8 s = some (restoredState s 72#64 4)) ∧
    (canonical (s.mem.readSize .q (s.regs.get .rsp + 56#64)) = true →
      runRange key 0x44 8 s = some (restoredState s 8#64 4)) ∧
    (canonical (s.mem.readSize .q (s.regs.get .rsp + 184#64)) = true →
      runRange finish 0xaf 8 s = some (restoredState s 136#64 7)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro target
    have actual := return_run s 72#64 4 live (by simpa [BitVec.add_assoc] using target)
    simp [runRange, entry_return_decoded, actual]
  · intro target
    have actual := return_run s 8#64 4 live (by simpa [BitVec.add_assoc] using target)
    simp [runRange, key_return_decoded, actual]
  · intro target
    have actual := return_run s 136#64 7 live (by simpa [BitVec.add_assoc] using target)
    simp [runRange, finish_return_decoded, actual]

theorem restored_stack_and_link (s : Cpu) (frame : Val) (len : Nat) :
    (restoredState s frame len).regs.get .rsp = s.regs.get .rsp + frame + 56#64 ∧
    (restoredState s frame len).rip = s.mem.readSize .q (s.regs.get .rsp + frame + 48#64) ∧
    (restoredState s frame len).mem = s.mem := by
  simp (config := { decide := true }) [restoredState, readyReturn, returnSlots, restoreSlot, releaseFrame,
    Regs.get_set_ne, Regs.get_set_same, BitVec.add_assoc]

set_option maxHeartbeats 1600000 in
theorem restored_register (s : Cpu) (frame : Val) (len : Nat) (i : Fin 6) :
    (restoredState s frame len).regs.get (Crypto.X86_64.savedReg i) =
      s.mem.readSize .q (s.regs.get .rsp + frame + BitVec.ofNat 64 (8 * (5 - i.val))) := by
  obtain ⟨i, hi⟩ := i
  interval_cases i <;>
    simp (config := { decide := true }) [restoredState, readyReturn, returnSlots, restoreSlot, releaseFrame,
      Crypto.X86_64.savedReg, Regs.get_set_ne, Regs.get_set_same, BitVec.add_assoc]

theorem restored_status (s : Cpu) (frame : Val) (len : Nat) :
    (restoredState s frame len).regs.get .rax = s.regs.get .rax := by
  simp (config := {decide := true}) [restoredState, readyReturn, returnSlots, restoreSlot,
    releaseFrame, Regs.get_set_ne]

theorem restored_direction (s : Cpu) (frame : Val) (len : Nat) :
    (restoredState s frame len).flags.df = s.flags.df := by
  simp only [restoredState, readyReturn, returnSlots, List.foldl_cons, List.foldl_nil,
    restoreSlot, releaseFrame, Flags.add, Flags.fromResult]

theorem restored_live (s : Cpu) (frame : Val) (len : Nat) :
    (restoredState s frame len).ms = s.ms := by
  simp only [restoredState, readyReturn, returnSlots, List.foldl_cons, List.foldl_nil, restoreSlot, releaseFrame]

end Crypto.HMACSHA256.X86_64
