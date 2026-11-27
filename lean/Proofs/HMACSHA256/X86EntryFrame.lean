import Proofs.HMACSHA256.X86Entry
import Proofs.HMACSHA256.X86FrameMemory
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset)

def entrySaved (s : Cpu) : Region := ⟨savedBase s, 48⟩

structure EntryPrefix (base : Val) (s out : Cpu) (capacity count : Nat) where
  setup : Cpu
  enter : runRange entry 0 7 s = some (enteredFrame .entry s)
  arguments : runRange entry 0xe 7 (enteredFrame .entry s) = some setup
  guard : runGuard setup = some out
  pc : out.rip = if capacity < 96 + count then routineAddress base entry + 0x100#64
    else routineAddress base entry + 0x3a#64
  live : out.ms = none
  df : out.flags.df = s.flags.df
  sp : out.regs.get .rsp = s.regs.get .rsp - 120#64
  status : out.regs.get .rax = 1#64
  key : out.regs.get .rbx = s.regs.get .rdi
  message : out.regs.get .rbp = s.regs.get .rsi
  scratch : out.regs.get .r12 = s.regs.get .rdx
  mac : out.regs.get .r13 = s.regs.get .rcx
  memory : out.mem = (enteredFrame .entry s).mem

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2900000 in
theorem entry_prefix (base : Val) (s : Cpu) (capacity count : Nat)
    (cap64 : capacity < 2 ^ 64) (count64 : count < 2 ^ 64)
    (capacityAt : s.mem.readSize .q (s.regs.get .rdx) = BitVec.ofNat 64 capacity)
    (countAt : s.mem.readSize .q (s.regs.get .rsi + 16#64) = BitVec.ofNat 64 count)
    (scratchOutside : ∀ i < 8, 48 ≤ (s.regs.get .rdx + BitVec.ofNat 64 i - savedBase s).toNat)
    (countOutside : ∀ i < 8, 48 ≤
      (s.regs.get .rsi + 16#64 + BitVec.ofNat 64 i - savedBase s).toNat)
    (pc : s.rip = routineAddress base entry) (live : s.ms = none)
    (canonicalEnd : canonical (routineAddress base entry + 0x100#64) = true) :
    ∃ out, Nonempty (EntryPrefix base s out capacity count) := by
  let start := enteredFrame .entry s
  let setup := capacityState start
  have startLive := (entered_frame_live .entry s).trans live
  have setupLive : setup.ms = none := startLive
  obtain ⟨cap, len, status, keyAt, msgAt, scratchAt, macAt, stackAt⟩ := capacity_state_registers start
  have setupPC : setup.rip = routineAddress base entry + 0x27#64 := by
    change start.rip + 25#64 = _
    rw [entered_frame_pc, pc, BitVec.add_assoc]
    rfl
  have capAt : setup.regs.get .rcx = BitVec.ofNat 64 capacity := by
    rw [cap, entered_frame_register .entry s .rdx (by decide), ← capacityAt]
    apply Mem.readN_congr
    intro i hi
    exact frame_saved_outside .entry s _ (scratchOutside i hi)
  have lenAt : setup.regs.get .rdx = BitVec.ofNat 64 count := by
    rw [len, entered_frame_register .entry s .rsi (by decide), ← countAt]
    apply Mem.readN_congr
    intro i hi
    exact frame_saved_outside .entry s _ (countOutside i hi)
  have target : canonical (setup.rip + 0xd9#64) = true := by
    rw [setupPC, BitVec.add_assoc]
    exact canonicalEnd
  obtain ⟨out, guard, mem, running, preserved, next, direction⟩ := runGuard_result setup setupLive target
  have statusDF : out.flags.df = s.flags.df :=
    direction.trans (entered_frame_direction .entry s)
  have endPC : out.rip = if capacity < 96 + count then routineAddress base entry + 0x100#64
      else routineAddress base entry + 0x3a#64 := by
    rw [next, capAt, lenAt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt cap64, Nat.mod_eq_of_lt count64, setupPC]
    split <;> rw [BitVec.add_assoc] <;> rfl
  refine ⟨out, ⟨⟨setup, enter_frame .entry s live, entry_capacity_setup start startLive,
    guard, endPC, running, statusDF, ?_, (preserved .rax (by decide)).trans status, ?_, ?_, ?_, ?_, mem⟩⟩⟩
  · rw [preserved _ (by decide), stackAt, entered_frame_stack, HmacRoutine.locals, BitVec.sub_sub]
    rfl
  · exact (preserved _ (by decide)).trans (keyAt.trans (entered_frame_register .entry s .rdi (by decide)))
  · exact (preserved _ (by decide)).trans (msgAt.trans (entered_frame_register .entry s .rsi (by decide)))
  · exact (preserved _ (by decide)).trans (scratchAt.trans (entered_frame_register .entry s .rdx (by decide)))
  · exact (preserved _ (by decide)).trans (macAt.trans (entered_frame_register .entry s .rcx (by decide)))

theorem zero_status_decoded :
    decodeRange entry 0xfb 1 = some [⟨.mov .d (.reg .rax) (.imm 0#64), 5⟩] := by decide +kernel

def successState (s : Cpu) : Cpu := {s with regs := s.regs.set .rax 0#64, rip := s.rip + 5#64}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem entry_set_success (s : Cpu) (live : s.ms = none) :
    runRange entry 0xfb 1 s = some (successState s) := by
  rw [runRange, zero_status_decoded]
  change some (X86.step ⟨.mov .d (.reg .rax) (.imm 0#64), 5⟩ s) = _
  rw [X86.step_mov_reg_imm .d .rax 0#64 live]
  simp only [Value.writeView, Value.trunc, successState, Cpu.setReg, Cpu.setRip]
  rfl

set_option maxRecDepth 8192 in
theorem entry_return_frame (s before : Cpu) (live : before.ms = none)
    (stack : before.regs.get .rsp = s.regs.get .rsp - 120#64)
    (returnValid : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true)
    (linkRead : before.mem.readSize .q (s.regs.get .rsp) = s.mem.readSize .q (s.regs.get .rsp))
    (saved : ∀ i : Fin 6, before.mem.readSize .q (savedBase s + BitVec.ofNat 64 (savedOffset i)) =
      s.regs.get (savedReg i)) :
    ∃ out, runRange entry 0x100 8 before = some out ∧
      out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧ out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
      out.regs.get .rax = before.regs.get .rax ∧ out.ms = none ∧ out.flags.df = before.flags.df ∧
      (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧ out.mem = before.mem := by
  let out := restoredState before 72#64 4
  have linkBefore : before.regs.get .rsp + 120#64 = s.regs.get .rsp := by rw [stack, BitVec.sub_add_cancel]
  have nonvolatileBase : before.regs.get .rsp + 72#64 = savedBase s := by
    rw [stack, savedBase]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨sp, link, mem⟩ := restored_stack_and_link before 72#64 4
  refine ⟨out, (returns before live).1 (by rw [linkBefore, linkRead]; exact returnValid), ?_,
    ?_, restored_status _ _ _, (restored_live _ _ _).trans live, restored_direction _ _ _, ?_, mem⟩
  · rw [sp, BitVec.add_assoc]
    change before.regs.get .rsp + 128#64 = _
    rw [show (128#64 : Val) = 120#64 + 8#64 from rfl, ← BitVec.add_assoc, linkBefore]
  · rw [link, BitVec.add_assoc]
    change before.mem.readSize .q (before.regs.get .rsp + 120#64) = _
    rw [linkBefore, linkRead]
  · intro i
    rw [show out = restoredState before 72#64 4 from rfl, restored_register, nonvolatileBase]
    exact saved i

end Crypto.HMACSHA256.X86_64
