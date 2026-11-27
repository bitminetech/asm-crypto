import Proofs.HMACSHA256.X86Setup
import Proofs.HMACSHA256.EncodedByteList
import Proofs.HMACSHA256.ARM64Memory
import Proofs.X86_64.Memory64

namespace Crypto.HMACSHA256.X86_64

open X86
open Crypto.X86_64 (byteView byteView_read64 byteView_write64 read64_write64)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

def routineAddress (base : Val) (routine : Routine) : Val := base + BitVec.ofInt 64 routine.offset
def shaAddress (base : Val) : Val := base + BitVec.ofInt 64 sha256Offset

def innerCallState (s : Cpu) : Cpu :=
  let args := ((s.regs.set .rbx (s.regs.get .rsi)).set .rbp (s.regs.get .rdx)).set
    .rsi (s.regs.get .rsp + 88#64)
  (({ s with regs := args }.push .q (s.rip + 16#64)).setRip (s.rip - 4065#64))

theorem inner_call (s : Cpu) (live : s.ms = none)
    (canonical : X86.canonical (s.rip - 4065#64) = true) :
    runRange finish 0x11 4 s = some (innerCallState s) := by
  have address : s.rip - 4065#64 = s.rip + 0xfffffffffffff01f#64 := by
    rw [BitVec.sub_eq_add_neg]
    rfl
  have checked := finish_inner_call s live (by rw [← address]; exact canonical)
  simpa only [innerCallState, address] using checked

private theorem inner_relocation :
    BitVec.ofInt 64 finish.offset + (0x11#64 + (-4065#64)) = BitVec.ofInt 64 sha256Offset := by decide +kernel

private theorem outer_relocation :
    BitVec.ofInt 64 finish.offset + (0xa4#64 + (-4212#64)) = BitVec.ofInt 64 sha256Offset := by decide +kernel

theorem inner_target (base : Val) (s : Cpu) (pc : s.rip = routineAddress base finish + 0x11#64) :
    (innerCallState s).rip = shaAddress base := by
  change s.rip - 4065#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc,
    inner_relocation]

theorem outer_target (base : Val) (s : Cpu) (pc : s.rip = routineAddress base finish + 0xa4#64) :
    (outerCallState s).rip = shaAddress base := by
  change s.rip - 4212#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc,
    outer_relocation]

private theorem push_register (s : Cpu) (v : Val) (r : GPR) (other : r ≠ .rsp) :
    (s.push .q v).regs.get r = s.regs.get r := by
  simp only [Cpu.push, Size.bytes, Cpu.setReg, Value.writeView_q, Cpu.writeMem]
  exact Regs.get_set_ne _ _ _ _ (Ne.symm other)

private theorem push_stack (s : Cpu) (v : Val) :
    (s.push .q v).regs.get .rsp = s.regs.get .rsp - 8#64 := by
  simp only [Cpu.push, Size.bytes, Cpu.setReg, Cpu.writeMem, Value.writeView_q, Regs.get_set_same]
  rfl

private theorem push_memory (s : Cpu) (v : Val) :
    (s.push .q v).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) v := rfl

theorem inner_call_registers (s : Cpu) :
    (innerCallState s).regs.get .rdi = s.regs.get .rdi ∧
    (innerCallState s).regs.get .rsi = s.regs.get .rsp + 88#64 ∧
    (innerCallState s).regs.get .rbx = s.regs.get .rsi ∧
    (innerCallState s).regs.get .rbp = s.regs.get .rdx ∧
    (innerCallState s).regs.get .rsp = s.regs.get .rsp - 8#64 ∧
    (innerCallState s).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.rip + 16#64) := by
  simp (config := { decide := true }) [innerCallState, Cpu.setRip, push_register, push_stack, push_memory,
    Regs.get_set_same, Regs.get_set_ne]

theorem outer_call_registers (s : Cpu) :
    (outerCallState s).regs.get .rdi = s.regs.get .rsp ∧
    (outerCallState s).regs.get .rsi = s.regs.get .rbp ∧
    (outerCallState s).regs.get .rsp = s.regs.get .rsp - 8#64 ∧
    (outerCallState s).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.rip + 11#64) := by
  simp (config := { decide := true }) [outerCallState, Cpu.setRip, push_register, push_stack, push_memory,
    Regs.get_set_same, Regs.get_set_ne]

theorem inner_link (base : Val) (s : Cpu) (pc : s.rip = routineAddress base finish + 0x11#64) :
    (innerCallState s).mem.readSize .q ((innerCallState s).regs.get .rsp) =
      routineAddress base finish + 0x21#64 := by
  obtain ⟨_, _, _, _, sp, mem⟩ := inner_call_registers s
  rw [mem, sp, read64_write64, pc, BitVec.add_assoc]
  rfl

theorem outer_link (base : Val) (s : Cpu) (pc : s.rip = routineAddress base finish + 0xa4#64) :
    (outerCallState s).mem.readSize .q ((outerCallState s).regs.get .rsp) =
      routineAddress base finish + 0xaf#64 := by
  obtain ⟨_, _, sp, mem⟩ := outer_call_registers s
  rw [mem, sp, read64_write64, pc, BitVec.add_assoc]
  rfl

/-- Pushing the real return address leaves all bytes of the freshly
serialized outer list, at offsets 0 through 119 above RSP, intact. -/
theorem outer_encoding_at_call (s : Cpu) (k0 : Crypto.Reference.HmacKeyBlock)
    (digest : Crypto.Reference.Digest)
    (encoding : EncodedByteList (byteView s.mem) (s.regs.get .rsp) (Crypto.Reference.hmacOuter k0 digest)) :
    EncodedByteList (byteView (outerCallState s).mem) ((outerCallState s).regs.get .rdi)
      (Crypto.Reference.hmacOuter k0 digest) := by
  obtain ⟨input, _, _, mem⟩ := outer_call_registers s
  have frame (j : Nat) (within : j < 120) :
      (byteView (outerCallState s).mem).cells (s.regs.get .rsp + BitVec.ofNat 64 j) =
        (byteView s.mem).cells (s.regs.get .rsp + BitVec.ofNat 64 j) := by
    rw [mem, byteView_write64]
    apply Crypto.ARM64.Imported.write64_cells_outside
    let sp := s.regs.get .rsp
    have address : sp + BitVec.ofNat 64 j - (sp - 8#64) = BitVec.ofNat 64 (8 + j) := by
      calc
        _ = (sp - 8#64) + 8#64 + BitVec.ofNat 64 j - (sp - 8#64) := by rw [BitVec.sub_add_cancel]
        _ = _ := by
          rw [BitVec.add_assoc, Crypto.ARM64.Imported.address_delta, BitVec.ofNat_add]
    change 8 ≤ (sp + BitVec.ofNat 64 j - (sp - 8#64)).toNat
    rw [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 + j < 2 ^ 64)]
    omega
  have word (j : Nat) (within : j + 8 ≤ 120) :
      (byteView (outerCallState s).mem).read64 (s.regs.get .rsp + BitVec.ofNat 64 j) =
        (byteView s.mem).read64 (s.regs.get .rsp + BitVec.ofNat 64 j) := by
    apply read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frame _ (by have := i.isLt; omega)
  rw [input]
  refine ⟨?_, (word 8 (by decide)).trans encoding.offset, (word 16 (by decide)).trans encoding.count, ?_⟩
  · simpa using (word 0 (by decide)).trans (by simpa using encoding.size)
  · intro i
    have n : i.val < 96 := by simpa only [Crypto.Reference.hmacOuter_length] using i.isLt
    have preserved := frame (24 + i.val) (by omega)
    change (byteView (outerCallState s).mem).read8 (s.regs.get .rsp + BitVec.ofNat 64 (24 + i.val)) = _
    unfold Arm64.Memory.read8
    rw [preserved]
    exact encoding.bytes i

theorem entry_key_call_decoded :
    decodeRange entry 0x3a 3 = some [
      ⟨.mov .q (.reg .rdi) (.reg .rbx), 3⟩,
      ⟨.mov .q (.reg .rsi) (.reg .rsp), 3⟩,
      ⟨.call (.rel 0x2bb#64), 5⟩] := by decide +kernel

def entryKeyCall (s : Cpu) : Cpu :=
  let args := (s.regs.set .rdi (s.regs.get .rbx)).set .rsi (s.regs.get .rsp)
  ({s with regs := args}.push .q (s.rip + 11#64)).setRip (s.rip + 710#64)

theorem entry_key_target (base : Val) (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x3a#64) :
    (entryKeyCall s).rip = routineAddress base key := by
  have relocated : BitVec.ofInt 64 entry.offset + (0x3a#64 + 710#64) =
      BitVec.ofInt 64 key.offset := by decide +kernel
  change s.rip + 710#64 = _
  rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, relocated]

set_option maxRecDepth 8192 in
theorem entry_key_call (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 710#64) = true) :
    runRange entry 0x3a 3 s = some (entryKeyCall s) := by
  unfold runRange
  rw [entry_key_call_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [move_reg _ .rdi .rbx _ live]
  rw [move_reg _ .rsi .rsp] <;> try exact live
  rw [direct_call _ 0x2bb#64] <;> try exact live
  · simp (config := {decide := true}) only [entryKeyCall, Regs.get_set_ne, BitVec.add_assoc] <;> rfl
  · simp only [BitVec.add_assoc]
    exact target

theorem entry_key_arguments (s : Cpu) :
    (entryKeyCall s).regs.get .rdi = s.regs.get .rbx ∧
    (entryKeyCall s).regs.get .rsi = s.regs.get .rsp ∧
    (entryKeyCall s).regs.get .rsp = s.regs.get .rsp - 8#64 ∧
    (entryKeyCall s).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.rip + 11#64) := by
  simp (config := {decide := true}) [entryKeyCall, Cpu.setRip, push_register, push_stack,
    push_memory, Regs.get_set_same, Regs.get_set_ne]

theorem entry_finish_call_decoded :
    decodeRange entry 0xeb 4 = some [
      ⟨.lea .q .rdi { base := some .r12, disp := 8#64 }, 5⟩,
      ⟨.mov .q (.reg .rsi) (.reg .rsp), 3⟩,
      ⟨.mov .q (.reg .rdx) (.reg .r13), 3⟩,
      ⟨.call (.rel 0x265#64), 5⟩] := by decide +kernel

def entryFinishCall (s : Cpu) : Cpu :=
  let args := ((s.regs.set .rdi (s.regs.get .r12 + 8#64)).set .rsi (s.regs.get .rsp)).set
    .rdx (s.regs.get .r13)
  ({s with regs := args}.push .q (s.rip + 16#64)).setRip (s.rip + 629#64)

theorem entry_finish_target (base : Val) (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xeb#64) :
    (entryFinishCall s).rip = routineAddress base finish := by
  have relocated : BitVec.ofInt 64 entry.offset + (0xeb#64 + 629#64) =
      BitVec.ofInt 64 finish.offset := by decide +kernel
  change s.rip + 629#64 = _
  rw [pc, routineAddress, routineAddress, BitVec.add_assoc, BitVec.add_assoc, relocated]

theorem entry_scratch_pointer (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.lea .q .rdi { base := some .r12, disp := 8#64 }, 5⟩ s =
      {s with regs := s.regs.set .rdi (s.regs.get .r12 + 8#64), rip := s.rip + 5#64} := by
  simp [X86.step, Cpu.stopped, live, Ea.addr, Ea.offset, Cpu.setReg, Cpu.setRip, Value.writeView]

set_option maxRecDepth 8192 in
theorem entry_finish_call (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip + 629#64) = true) :
    runRange entry 0xeb 4 s = some (entryFinishCall s) := by
  unfold runRange
  rw [entry_finish_call_decoded]
  simp only [Option.map_some, X86.run, List.foldl_cons, List.foldl_nil]
  rw [entry_scratch_pointer _ live]
  rw [move_reg _ .rsi .rsp] <;> try exact live
  rw [move_reg _ .rdx .r13] <;> try exact live
  rw [direct_call _ 0x265#64] <;> try exact live
  · simp (config := {decide := true}) only [entryFinishCall, Regs.get_set_ne, BitVec.add_assoc] <;> rfl
  · simp only [BitVec.add_assoc]
    exact target

theorem entry_finish_arguments (s : Cpu) :
    (entryFinishCall s).regs.get .rdi = s.regs.get .r12 + 8#64 ∧
    (entryFinishCall s).regs.get .rsi = s.regs.get .rsp ∧
    (entryFinishCall s).regs.get .rdx = s.regs.get .r13 ∧
    (entryFinishCall s).regs.get .rsp = s.regs.get .rsp - 8#64 ∧
    (entryFinishCall s).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.rip + 16#64) := by
  simp (config := {decide := true}) [entryFinishCall, Cpu.setRip, push_register, push_stack,
    push_memory, Regs.get_set_same, Regs.get_set_ne]

end Crypto.HMACSHA256.X86_64
