import Proofs.HMACSHA256.X86Repeat

namespace Crypto.HMACSHA256.X86_64

open X86

def decodeRange (routine : Routine) (offset : Nat) : Nat → Option (List Instr)
  | 0 => some []
  | count + 1 => do
    let ins ← decodeAt routine offset
    return ins :: (← decodeRange routine (offset + ins.len) count)

def runRange (routine : Routine) (offset count : Nat) (s : Cpu) : Option Cpu :=
  (decodeRange routine offset count).map fun ops => X86.run ops s

theorem finish_header_decoded :
    decodeRange finish 0x21 3 = some [
      ⟨.mov .q (.mem { base := some .rsp }) (.imm 120#64), 8⟩,
      ⟨.mov .q (.mem { base := some .rsp, disp := 8#64 }) (.imm 24#64), 9⟩,
      ⟨.mov .q (.mem { base := some .rsp, disp := 16#64 }) (.imm 96#64), 9⟩] := by decide +kernel

def finishHeader (s : Cpu) : Mem :=
  let stack := s.regs.get .rsp
  ((s.mem.writeSize .q stack 120#64).writeSize .q (stack + 8#64) 24#64).writeSize
    .q (stack + 16#64) 96#64

theorem q_trunc (v : Val) : Value.trunc .q v = v := by
  change v &&& Size.q.mask = v
  rw [show Size.q.mask = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

theorem store_header_word (s : Cpu) (disp value : Val) (length : Nat) (live : s.ms = none) :
    X86.step ⟨.mov .q (.mem { base := some .rsp, disp := disp }) (.imm value), length⟩ s =
      { s with
        mem := s.mem.writeSize .q (s.regs.get .rsp + disp) value
        rip := s.rip + BitVec.ofNat 64 length } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.writeMem, Cpu.setRip, Ea.addr, Ea.offset, q_trunc]

theorem finish_header (s : Cpu) (live : s.ms = none) :
    runRange finish 0x21 3 s = some { s with mem := finishHeader s, rip := s.rip + 26#64 } := by
  unfold runRange
  rw [finish_header_decoded]
  have h0 := store_header_word s 0#64 120#64 8 live
  have proceed (st : Cpu) (addr value : Val) (len : Nat) (ok : st.ms = none) :
      (X86.step ⟨.mov .q (.mem { base := some .rsp, disp := addr }) (.imm value), len⟩ st).ms = none := by
    rw [store_header_word st addr value len ok]
    exact ok
  have h1 := proceed s 0#64 120#64 8 live
  let st := X86.step ⟨.mov .q (.mem { base := some .rsp }) (.imm 120#64), 8⟩ s
  have h2 := proceed st 8#64 24#64 9 h1
  simp only [Option.map_some, X86.run, List.foldl]
  rw [store_header_word _ _ _ _ h2, store_header_word st 8#64 24#64 9 h1]
  change (some { st with mem := _, rip := _ }) = _
  rw [show st = _ from h0]
  simp [finishHeader, BitVec.add_assoc]

theorem finish_inner_call_decoded :
    decodeRange finish 0x11 4 = some [
      ⟨.mov .q (.reg .rbx) (.reg .rsi), 3⟩,
      ⟨.mov .q (.reg .rbp) (.reg .rdx), 3⟩,
      ⟨.lea .q .rsi { base := some .rsp, disp := 88#64 }, 5⟩,
      ⟨.call (.rel 0xfffffffffffff00f#64), 5⟩] := by decide +kernel

theorem move_reg (s : Cpu) (dst src : GPR) (length : Nat) (live : s.ms = none) :
    X86.step ⟨.mov .q (.reg dst) (.reg src), length⟩ s =
      { s with regs := s.regs.set dst (s.regs.get src), rip := s.rip + BitVec.ofNat 64 length } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.setRip, q_trunc, Value.writeView]

theorem lea_stack (s : Cpu) (dst : GPR) (disp : Val) (length : Nat) (live : s.ms = none) :
    X86.step ⟨.lea .q dst { base := some .rsp, disp := disp }, length⟩ s =
      { s with
        regs := s.regs.set dst (s.regs.get .rsp + disp)
        rip := s.rip + BitVec.ofNat 64 length } := by
  simp [X86.step, Cpu.stopped, live, Ea.addr, Ea.offset, Cpu.setReg, Cpu.setRip, Value.writeView]

theorem direct_call (s : Cpu) (disp : Val) (live : s.ms = none)
    (target : canonical (s.rip + 5#64 + disp) = true) :
    X86.step ⟨.call (.rel disp), 5⟩ s =
      (s.push .q (s.rip + 5#64)).setRip (s.rip + 5#64 + disp) := by
  simp [X86.step, Cpu.stopped, live, target]

/-- The first call saves K0 and the MAC pointer in nonvolatile registers and
passes a pointer to the last 32 bytes of the outer list for the inner digest. -/
theorem finish_inner_call (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 0xfffffffffffff01f#64) = true) :
    let regs := ((s.regs.set .rbx (s.regs.get .rsi)).set .rbp (s.regs.get .rdx)).set
      .rsi (s.regs.get .rsp + 88#64)
    runRange finish 0x11 4 s = some
      (({ s with regs := regs }.push .q (s.rip + 16#64)).setRip
        (s.rip + 0xfffffffffffff01f#64)) := by
  dsimp only
  unfold runRange
  rw [finish_inner_call_decoded]
  let a := X86.step ⟨.mov .q (.reg .rbx) (.reg .rsi), 3⟩ s
  have aEq := move_reg s .rbx .rsi 3 live
  have aLive : a.ms = none := by simp [a, aEq, live]
  let b := X86.step ⟨.mov .q (.reg .rbp) (.reg .rdx), 3⟩ a
  have bEq := move_reg a .rbp .rdx 3 aLive
  have bLive : b.ms = none := by simp [b, bEq, aLive]
  let c := X86.step ⟨.lea .q .rsi { base := some .rsp, disp := 88#64 }, 5⟩ b
  have cEq := lea_stack b .rsi 88#64 5 bLive
  have cLive : c.ms = none := by simp [c, cEq, bLive]
  have cTarget : canonical (c.rip + 5#64 + 0xfffffffffffff00f#64) = true := by
    simpa [c, cEq, b, bEq, a, aEq, BitVec.add_assoc] using target
  change some (X86.step ⟨.call (.rel 0xfffffffffffff00f#64), 5⟩ c) = _
  rw [direct_call _ _ cLive cTarget]
  simp [c, cEq, b, bEq, a, aEq, Cpu.setRip, Cpu.push, Cpu.writeMem, Cpu.setReg,
    Value.writeView, BitVec.add_assoc]

theorem finish_outer_call_decoded :
    decodeRange finish 0xa4 3 = some [
      ⟨.mov .q (.reg .rdi) (.reg .rsp), 3⟩,
      ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩,
      ⟨.call (.rel (-4223#64)), 5⟩] := by decide +kernel

def outerCallState (s : Cpu) : Cpu :=
  let args := (s.regs.set .rdi (s.regs.get .rsp)).set .rsi (s.regs.get .rbp)
  (({ s with regs := args }.push .q (s.rip + 11#64)).setRip (s.rip - 4212#64))

/-- The second call passes the serialized stack list and original MAC
pointer, and pushes the return address of the helper's epilogue. -/
theorem finish_outer_call (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip - 4212#64) = true) :
    runRange finish 0xa4 3 s = some (outerCallState s) := by
  unfold runRange
  rw [finish_outer_call_decoded]
  let a : Cpu := { s with regs := s.regs.set .rdi (s.regs.get .rsp), rip := s.rip + 3#64 }
  let b : Cpu := { a with regs := a.regs.set .rsi (a.regs.get .rbp), rip := a.rip + 3#64 }
  have aStep : X86.step ⟨.mov .q (.reg .rdi) (.reg .rsp), 3⟩ s = a :=
    move_reg _ _ _ _ live
  have bStep : X86.step ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩ a = b :=
    move_reg _ _ _ _ live
  have link : b.rip + 5#64 = s.rip + 11#64 := by
    simp only [b, a, BitVec.add_assoc]
    rfl
  have branch : b.rip + 5#64 + (-4223#64) = s.rip - 4212#64 := by
    rw [link, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  change some (X86.step ⟨.call (.rel (-4223#64)), 5⟩
    (X86.step ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩
      (X86.step ⟨.mov .q (.reg .rdi) (.reg .rsp), 3⟩ s))) = _
  rw [aStep, bStep, direct_call b (-4223#64) live (by rw [branch]; exact target), branch, link]
  simp (config := { decide := true }) [outerCallState, b, a, Regs.get_set_ne, Cpu.push, Cpu.setRip,
    Cpu.setReg, Cpu.writeMem]


end Crypto.HMACSHA256.X86_64
