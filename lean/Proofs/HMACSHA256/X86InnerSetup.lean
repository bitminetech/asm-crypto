import Proofs.HMACSHA256.X86Entry
import Proofs.HMACSHA256.X86Pad

namespace Crypto.HMACSHA256.X86_64

open X86

theorem inner_header_decoded : decodeRange entry 0x45 8 = some [
  ⟨.mov .q (.reg .rax) (.mem { base := some .r12 }), 4⟩,
  ⟨.bin .sub .q (.reg .rax) (.imm 8#64), 4⟩,
  ⟨.mov .q (.mem { base := some .r12, disp := 8#64 }) (.reg .rax), 5⟩,
  ⟨.mov .q (.mem { base := some .r12, disp := 16#64 }) (.imm 24#64), 9⟩,
  ⟨.mov .q (.reg .rax) (.mem { base := some .rbp, disp := 16#64 }), 4⟩,
  ⟨.bin .add .q (.reg .rax) (.imm 64#64), 4⟩,
  ⟨.mov .q (.mem { base := some .r12, disp := 24#64 }) (.reg .rax), 5⟩,
  ⟨.mov .q (.reg .r8) (.imm 0x3636363636363636#64), 10⟩] := by decide +kernel

theorem copy_setup_decoded : decodeRange entry 0xd9 4 = some [
  ⟨.mov .q (.reg .rsi) (.mem { base := some .rbp, disp := 8#64 }), 4⟩,
  ⟨.bin .add .q (.reg .rsi) (.reg .rbp), 3⟩,
  ⟨.lea .q .rdi { base := some .r12, disp := 96#64 }, 5⟩,
  ⟨.mov .q (.reg .rcx) (.mem { base := some .rbp, disp := 16#64 }), 4⟩] := by decide +kernel

theorem subtract_rax (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .sub .q (.reg .rax) (.imm 8#64), 4⟩ s =
      { s with
        regs := s.regs.set .rax (s.regs.get .rax - 8#64)
        flags := Flags.sub .q (s.regs.get .rax) 8#64 s.flags
        rip := s.rip + 4#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.subResult,
    Value.writeView]

theorem add_rax (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .add .q (.reg .rax) (.imm 64#64), 4⟩ s =
      { s with
        regs := s.regs.set .rax (s.regs.get .rax + 64#64)
        flags := Flags.add .q (s.regs.get .rax) 64#64 s.flags
        rip := s.rip + 4#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.addResult,
    Value.writeView]

theorem store_scratch (s : Cpu) (source : Operand) (disp : Val) (len : Nat)
    (live : s.ms = none) (notMemory : source.isMem = false) :
    X86.step ⟨.mov .q (.mem { base := some .r12, disp := disp }) source, len⟩ s =
      { s with
        mem := s.mem.writeSize .q (s.regs.get .r12 + disp) (s.readOperand .q (s.rip + BitVec.ofNat 64 len) source)
        rip := s.rip + BitVec.ofNat 64 len } := by
  cases source <;> simp [Operand.isMem] at notMemory
  all_goals simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Operand.locked,
    Cpu.writeOperand, Cpu.writeMem, Cpu.setRip, Ea.addr, Ea.offset]

theorem set_ipad (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.mov .q (.reg .r8) (.imm 0x3636363636363636#64), 10⟩ s =
      { s with regs := s.regs.set .r8 0x3636363636363636#64, rip := s.rip + 10#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Value.writeView, q_trunc]

def innerHeaderMemory (s : Cpu) : Mem :=
  let scratch := s.regs.get .r12
  let afterSize := s.mem.writeSize .q (scratch + 8#64) (s.mem.readSize .q scratch - 8#64)
  let afterOffset := afterSize.writeSize .q (scratch + 16#64) 24#64
  let count := afterOffset.readSize .q (s.regs.get .rbp + 16#64)
  afterOffset.writeSize .q (scratch + 24#64) (count + 64#64)

def innerHeaderState (s : Cpu) : Cpu :=
  let scratch := s.regs.get .r12
  let size := s.mem.readSize .q scratch
  let afterOffset := (s.mem.writeSize .q (scratch + 8#64) (size - 8#64)).writeSize .q (scratch + 16#64) 24#64
  let count := afterOffset.readSize .q (s.regs.get .rbp + 16#64)
  { s with
    regs := (s.regs.set .rax (count + 64#64)).set .r8 0x3636363636363636#64
    mem := innerHeaderMemory s
    flags := Flags.add .q count 64#64 (Flags.sub .q size 8#64 s.flags)
    rip := s.rip + 45#64 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem entry_inner_header (s : Cpu) (live : s.ms = none) :
    runRange entry 0x45 8 s = some (innerHeaderState s) := by
  unfold runRange
  rw [inner_header_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [load_argument_word _ .rax { base := some .r12 } 4]
  case live => exact live
  case unlocked => rfl
  rw [subtract_rax] <;> try exact live
  rw [store_scratch _ (.reg .rax) 8#64 5]
  case live => exact live
  case notMemory => rfl
  rw [store_scratch _ (.imm 24#64) 16#64 9]
  case live => exact live
  case notMemory => rfl
  rw [load_argument_word _ .rax]
  case live => exact live
  case unlocked => rfl
  rw [add_rax] <;> try exact live
  rw [store_scratch _ (.reg .rax) 24#64 5]
  case live => exact live
  case notMemory => rfl
  rw [set_ipad] <;> try exact live
  simp (config := {decide := true}) only [innerHeaderState, innerHeaderMemory, Ea.addr, Ea.offset,
    if_false, show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, BitVec.add_assoc,
    Regs.get_set_same, Regs.get_set_ne, Regs.set_set_same, Cpu.readOperand, Cpu.getReg,
    q_trunc] <;> rfl

theorem add_message_base (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .add .q (.reg .rsi) (.reg .rbp), 3⟩ s =
      { s with
        regs := s.regs.set .rsi (s.regs.get .rsi + s.regs.get .rbp)
        flags := Flags.add .q (s.regs.get .rsi) (s.regs.get .rbp) s.flags
        rip := s.rip + 3#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.addResult,
    Value.writeView]

theorem lea_message_dest (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.lea .q .rdi { base := some .r12, disp := 96#64 }, 5⟩ s =
      { s with regs := s.regs.set .rdi (s.regs.get .r12 + 96#64), rip := s.rip + 5#64 } := by
  simp [X86.step, Cpu.stopped, live, Ea.addr, Ea.offset, Cpu.setReg, Cpu.setRip, Value.writeView]

def messageCopyState (s : Cpu) : Cpu :=
  let msg := s.regs.get .rbp
  let offset := s.mem.readSize .q (msg + 8#64)
  { s with
    regs := ((s.regs.set .rsi (offset + msg)).set .rdi (s.regs.get .r12 + 96#64)).set .rcx
      (s.mem.readSize .q (msg + 16#64))
    flags := Flags.add .q offset msg s.flags
    rip := s.rip + 16#64 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3400000 in
theorem entry_copy_setup (s : Cpu) (live : s.ms = none) :
    runRange entry 0xd9 4 s = some (messageCopyState s) := by
  unfold runRange
  rw [copy_setup_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [load_argument_word _ .rsi]
  case live => exact live
  case unlocked => rfl
  rw [add_message_base] <;> try exact live
  rw [lea_message_dest] <;> try exact live
  rw [load_argument_word _ .rcx]
  case live => exact live
  case unlocked => rfl
  simp (config := {decide := true}) only [messageCopyState, Ea.addr, Ea.offset, if_false,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, BitVec.add_assoc,
    Regs.get_set_same, Regs.get_set_ne, Regs.set_set_same] <;> rfl

end Crypto.HMACSHA256.X86_64
