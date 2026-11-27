import Proofs.HMACSHA256.X86Setup
import Proofs.HMACSHA256.X86Entry
import Proofs.HMACSHA256.X86Zero

namespace Crypto.HMACSHA256.X86_64

open X86

theorem key_clear_setup_decoded :
    decodeRange key 0xe 5 = some [
      ⟨.mov .q (.reg .rbx) (.reg .rdi), 3⟩,
      ⟨.mov .q (.reg .rbp) (.reg .rsi), 3⟩,
      ⟨.bin .xor .d (.reg .rax) (.reg .rax), 2⟩,
      ⟨.mov .q (.reg .rdi) (.reg .rsi), 3⟩,
      ⟨.mov .d (.reg .rcx) (.imm 8#64), 5⟩] := by decide +kernel

/-- K0's incoming address is saved before advancing RDI through REP STOSQ. -/
def keyClearState (s : Cpu) : Cpu :=
  let (aux, afterOracle) := s.undefBit
  let r := s.regs
  let args := ((r.set .rbx (r.get .rdi)).set .rbp (r.get .rsi)).set .rax 0#64
  { afterOracle with
    regs := (args.set .rdi (r.get .rsi)).set .rcx 8#64
    flags := Flags.logic .d 0#64 aux s.flags
    rip := s.rip + 16#64 }

theorem xor_accumulator (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .xor .d (.reg .rax) (.reg .rax), 2⟩ s =
      let (aux, afterOracle) := s.undefBit
      { afterOracle with
        regs := s.regs.set .rax 0#64
        flags := Flags.logic .d 0#64 aux s.flags
        rip := s.rip + 2#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem,
    Cpu.readOperand, Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setFlags, Cpu.setRip,
    Value.writeView, Cpu.undefBit, show Value.trunc .d 0#64 = 0#64 from rfl]

theorem set_clear_count (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.mov .d (.reg .rcx) (.imm 8#64), 5⟩ s =
      { s with regs := s.regs.set .rcx 8#64, rip := s.rip + 5#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Value.writeView, Value.trunc]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem key_clear_setup (s : Cpu) (live : s.ms = none) :
    runRange key 0xe 5 s = some (keyClearState s) := by
  unfold runRange
  rw [key_clear_setup_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [move_reg _ .rbx .rdi _ live]
  rw [move_reg _ .rbp .rsi] <;> try exact live
  rw [xor_accumulator] <;> try exact live
  rw [move_reg _ .rdi .rsi] <;> try exact live
  rw [set_clear_count] <;> try exact live
  simp (config := {decide := true}) only [keyClearState, Cpu.undefBit, Regs.get_set_ne,
    Regs.get_set_same, BitVec.add_assoc] <;> rfl

theorem key_clear_arguments (s : Cpu) :
    (keyClearState s).regs.get .rdi = s.regs.get .rsi ∧
    (keyClearState s).regs.get .rbx = s.regs.get .rdi ∧
    (keyClearState s).regs.get .rbp = s.regs.get .rsi ∧
    (keyClearState s).regs.get .rcx = 8#64 ∧
    (keyClearState s).regs.get .rax = 0#64 ∧
    (keyClearState s).regs.get .rsp = s.regs.get .rsp ∧
    (keyClearState s).mem = s.mem ∧
    (keyClearState s).flags.df = s.flags.df ∧ (keyClearState s).ms = s.ms := by
  simp (config := {decide := true}) only [keyClearState, Cpu.undefBit, Regs.get_set_same,
    Regs.get_set_ne, Flags.logic, Flags.fromResult, and_true, true_and]

theorem key_length_decoded : decodeRange key 0x21 3 = some [
  ⟨.mov .q (.reg .rcx) (.mem { base := some .rbx, disp := 16#64 }), 4⟩,
  ⟨.bin .cmp .q (.reg .rcx) (.imm 64#64), 4⟩,
  ⟨.jcc .a 14#64, 2⟩] := by decide +kernel

def keyTestState (s : Cpu) : Cpu :=
  let count := s.mem.readSize .q (s.regs.get .rbx + 16#64)
  { s with
    regs := s.regs.set .rcx count
    flags := Flags.sub .q count 64#64 s.flags
    rip := if 64 < count.toNat then s.rip + 24#64 else s.rip + 10#64 }

theorem compare_key_length (s : Cpu) (live : s.ms = none) :
    step ⟨.bin .cmp .q (.reg .rcx) (.imm 64#64), 4⟩ s =
      { s with flags := Flags.sub .q (s.regs.get .rcx) 64#64 s.flags, rip := s.rip + 4#64 } := by
  simp [step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.getReg, Cpu.setFlags, Cpu.setRip]

private theorem key_ja (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 2#64 + 14#64) = true) :
    step ⟨.jcc .a 14#64, 2⟩ s =
      { s with rip := if !s.flags.cf && !s.flags.zf then s.rip + 2#64 + 14#64 else s.rip + 2#64 } := by
  simp [step, Cpu.stopped, live, Cc.eval, Cpu.setRipChecked, Cpu.setRip, target]
  split <;> rfl

private theorem above64 (v : Val) (flags : Flags) :
    (!(Flags.sub .q v 64#64 flags).cf && !(Flags.sub .q v 64#64 flags).zf) =
      decide (64 < v.toNat) := by
  have zero : (v - 64#64 == 0#64) = decide (v.toNat = 64) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have eq := BitVec.sub_add_cancel v 64#64
      rw [h, BitVec.zero_add] at eq
      exact congrArg BitVec.toNat eq.symm
    · intro h
      have eq : v = 64#64 := BitVec.eq_of_toNat_eq h
      simp [eq]
  simp only [Flags.sub, Flags.fromResult, Flags.subCF, Flags.subResult, Value.uval, Value.isZero, q_trunc]
  change (!decide (v.toNat < 64) && !(v - 64#64 == 0#64)) = _
  rw [zero]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2300000 in
theorem key_length_test (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 24#64) = true) :
    runRange key 0x21 3 s = some (keyTestState s) := by
  unfold runRange
  rw [key_length_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [load_argument_word _ .rcx]
  case live => exact live
  case unlocked => rfl
  rw [compare_key_length] <;> try exact live
  rw [key_ja]
  case live => exact live
  case target => simpa only [BitVec.add_assoc] using target
  simp (config := {decide := true}) only [keyTestState, Ea.addr, Ea.offset, if_false,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, BitVec.add_assoc,
    Regs.get_set_same, Regs.get_set_ne, above64, decide_eq_true_eq] <;> rfl

theorem short_setup_decoded : decodeRange key 0x2b 3 = some [
  ⟨.mov .q (.reg .rsi) (.mem { base := some .rbx, disp := 8#64 }), 4⟩,
  ⟨.bin .add .q (.reg .rsi) (.reg .rbx), 3⟩,
  ⟨.mov .q (.reg .rdi) (.reg .rbp), 3⟩] := by decide +kernel

theorem add_key_base (s : Cpu) (live : s.ms = none) :
    step ⟨.bin .add .q (.reg .rsi) (.reg .rbx), 3⟩ s =
      { s with
        regs := s.regs.set .rsi (s.regs.get .rsi + s.regs.get .rbx)
        flags := Flags.add .q (s.regs.get .rsi) (s.regs.get .rbx) s.flags
        rip := s.rip + 3#64 } := by
  simp [step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.addResult,
    Value.writeView]

def keyCopyState (s : Cpu) : Cpu :=
  let addr := s.regs.get .rbx
  let offset := s.mem.readSize .q (addr + 8#64)
  { s with
    regs := (s.regs.set .rsi (offset + addr)).set .rdi (s.regs.get .rbp)
    flags := Flags.add .q offset addr s.flags
    rip := s.rip + 10#64 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem key_copy_setup (s : Cpu) (live : s.ms = none) :
    runRange key 0x2b 3 s = some (keyCopyState s) := by
  unfold runRange
  rw [short_setup_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [load_argument_word _ .rsi]
  case live => exact live
  case unlocked => rfl
  rw [add_key_base] <;> try exact live
  rw [move_reg _ .rdi .rbp] <;> try exact live
  simp (config := {decide := true}) only [keyCopyState, Ea.addr, Ea.offset, if_false,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, BitVec.add_assoc,
    Regs.get_set_same, Regs.get_set_ne] <;> rfl

theorem key_copy_exit (s : Cpu) (live : s.ms = none) (target : canonical (s.rip + 13#64) = true) :
    runRange key 0x37 1 s = some { s with rip := s.rip + 13#64 } := by
  have decoded : decodeRange key 0x37 1 = some [⟨.jmp (.rel 11#64), 2⟩] := by decide +kernel
  rw [runRange, decoded]
  simp [X86.run, X86.step, Cpu.stopped, live, Cpu.setRipChecked, Cpu.setRip,
    BitVec.add_assoc, show (2#64 + 11#64) = 13#64 from rfl, target]

end Crypto.HMACSHA256.X86_64
