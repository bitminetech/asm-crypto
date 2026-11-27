import Proofs.HMACSHA256.X86Setup
import X86.Theorems

namespace Crypto.HMACSHA256.X86_64

open X86

inductive HmacRoutine where
  | entry | key | finish

def HmacRoutine.image : HmacRoutine → Routine
  | .entry => X86_64.entry
  | .key => X86_64.key
  | .finish => X86_64.finish

def HmacRoutine.locals : HmacRoutine → Val
  | .entry => 72#64
  | .key => 8#64
  | .finish => 136#64

def HmacRoutine.allocLength : HmacRoutine → Nat
  | .finish => 7
  | _ => 4

def saveSlots : List (GPR × Nat) :=
  [(.rbx, 1), (.rbp, 1), (.r12, 2), (.r13, 2), (.r14, 2), (.r15, 2)]

def allocate (r : HmacRoutine) : Instr :=
  ⟨.bin .sub .q (.reg .rsp) (.imm r.locals), r.allocLength⟩

def saveCode (r : HmacRoutine) : List Instr :=
  saveSlots.map (fun (reg, len) => ⟨.push .q (.reg reg), len⟩) ++ [allocate r]

theorem prologue_decoded (r : HmacRoutine) :
    decodeRange r.image 0 7 = some (saveCode r) := by cases r <;> decide +kernel

def saveRegister (s : Cpu) (slot : GPR × Nat) : Cpu := {
  s with
    mem := s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.regs.get slot.1)
    regs := s.regs.set .rsp (s.regs.get .rsp - 8#64)
    rip := s.rip + BitVec.ofNat 64 slot.2 }

def reserveFrame (r : HmacRoutine) (s : Cpu) : Cpu := {
  s with
    regs := s.regs.set .rsp (s.regs.get .rsp - r.locals)
    flags := Flags.sub .q (s.regs.get .rsp) r.locals s.flags
    rip := s.rip + BitVec.ofNat 64 r.allocLength }

def enteredFrame (r : HmacRoutine) (s : Cpu) : Cpu :=
  reserveFrame r (saveSlots.foldl saveRegister s)

theorem run_save_registers (slots : List (GPR × Nat)) (s : Cpu) (live : s.ms = none) :
    X86.run (slots.map (fun (r, n) => ⟨.push .q (.reg r), n⟩)) s = slots.foldl saveRegister s := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot tail ih =>
    have one : step ⟨.push .q (.reg slot.1), slot.2⟩ s = saveRegister s slot := by
      rw [step_push_reg _ _ live]
      simp [saveRegister, Cpu.getReg, q_trunc, Size.bytes]
    change X86.run (tail.map (fun (r, n) => ⟨.push .q (.reg r), n⟩))
      (step ⟨.push .q (.reg slot.1), slot.2⟩ s) = tail.foldl saveRegister (saveRegister s slot)
    rw [one]
    exact ih _ live

private theorem saved_live (slots : List (GPR × Nat)) (s : Cpu) :
    (slots.foldl saveRegister s).ms = s.ms := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot tail ih => exact ih (saveRegister s slot)

theorem allocate_frame (r : HmacRoutine) (s : Cpu) (live : s.ms = none) :
    step (allocate r) s = reserveFrame r s := by
  rw [allocate, step_sub_reg_imm _ _ _ live, Value.writeView_q, q_trunc]
  simp [reserveFrame, Cpu.getReg, Flags.subResult, q_trunc]

/-- Each System V prologue pushes the actual nonvolatile register values
and reserves the local space declared by the linked instructions. -/
theorem enter_frame (r : HmacRoutine) (s : Cpu) (live : s.ms = none) :
    runRange r.image 0 7 s = some (enteredFrame r s) := by
  unfold runRange
  rw [prologue_decoded]
  simp only [Option.map_some, saveCode, X86.run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change some (step (allocate r)
    (X86.run (saveSlots.map (fun (reg, len) => ⟨.push .q (.reg reg), len⟩)) s)) = _
  rw [run_save_registers _ _ live, allocate_frame _ _ ((saved_live _ _).trans live)]
  rfl

theorem entered_frame_register (r : HmacRoutine) (s : Cpu) (reg : GPR) (other : reg ≠ .rsp) :
    (enteredFrame r s).regs.get reg = s.regs.get reg := by
  have push (items : List (GPR × Nat)) (initial : Cpu) :
      (items.foldl saveRegister initial).regs.get reg = initial.regs.get reg := by
    induction items generalizing initial with
    | nil => rfl
    | cons slot tail ih =>
      rw [List.foldl_cons, ih]
      exact Regs.get_set_ne _ _ _ _ (Ne.symm other)
  unfold enteredFrame reserveFrame
  rw [Regs.get_set_ne _ _ _ _ (Ne.symm other)]
  exact push _ s

theorem entered_frame_stack (r : HmacRoutine) (s : Cpu) :
    (enteredFrame r s).regs.get .rsp = s.regs.get .rsp - 48#64 - r.locals := by
  simp only [enteredFrame, reserveFrame, saveSlots, List.foldl_cons, List.foldl_nil,
    saveRegister, Regs.get_set_same, BitVec.sub_sub]
  rfl

theorem entered_frame_pc (r : HmacRoutine) (s : Cpu) :
    (enteredFrame r s).rip = s.rip + BitVec.ofNat 64 (10 + r.allocLength) := by
  cases r <;> simp only [enteredFrame, reserveFrame, saveSlots, List.foldl_cons, List.foldl_nil,
    saveRegister, HmacRoutine.allocLength, BitVec.add_assoc] <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 900000 in
theorem entered_frame_live (r : HmacRoutine) (s : Cpu) :
    (enteredFrame r s).ms = s.ms := by
  change (saveSlots.foldl saveRegister s).ms = s.ms
  exact saved_live _ _

end Crypto.HMACSHA256.X86_64
