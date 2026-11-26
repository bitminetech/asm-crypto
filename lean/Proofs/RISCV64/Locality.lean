import Proofs.RISCV64.Permissions
import Proofs.ARM64.ImportedMemoryLocality

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (CellsOnRange SameCellsOn canRead_cells_eq canWrite_cells_eq
  canExec_cells_eq readSized_cells_eq sameCells_writeSized)

def Access.span : Access → Addr × Nat
  | .fetch a n => (a, n)
  | .read a w | .write a w => (a, w.bytes)

def Access.Within (P : Addr → Prop) (access : Access) : Prop :=
  ∀ i < access.span.2, P (access.span.1 + BitVec.ofNat 64 i)

private def Width.arm : Width → Arm64.MemWidth
  | .byte => .B8
  | .word => .W32
  | .double => .X64

private theorem Width.arm_bytes (w : Width) : w.arm.bytes = w.bytes := by cases w <;> rfl

private theorem Width.load_agrees (w : Width) (s t : Memory) (addr : Addr)
    (cells : CellsOnRange s t addr w.bytes) : w.load s addr = w.load t addr := by
  have same := readSized_cells_eq s t addr w.arm (match w with | .byte => false | _ => true)
    (by simpa only [w.arm_bytes] using cells)
  cases w <;> exact same

private theorem Width.store_agrees (w : Width) (s t : Memory) (addr value : Addr)
    (P : Addr → Prop) (cells : SameCellsOn P s t) : SameCellsOn P (w.store s addr value) (w.store t addr value) := by
  have same := sameCells_writeSized cells w.arm addr value
  cases w <;> exact same

theorem Access.permitted_agrees (a : Access) (s t : Memory) (P : Addr → Prop)
    (cells : SameCellsOn P s t) (within : a.Within P) : a.permitted s = a.permitted t := by
  have perByte : CellsOnRange s t a.span.1 a.span.2 := fun i hi => cells _ (within i hi)
  cases a with
  | fetch addr n => simp only [Access.permitted, canExec_cells_eq s t addr n perByte]
  | read addr w => simp only [Access.permitted, canRead_cells_eq s t addr w.bytes perByte]
  | write addr w => simp only [Access.permitted, canWrite_cells_eq s t addr w.bytes perByte]

structure BorrowAgreement (P : Addr → Prop) (s t : CPU) : Prop where
  pc : s.pc = t.pc
  registers : s.regs = t.regs
  memory : SameCellsOn P s.mem t.mem

theorem BorrowAgreement.refl (P : Addr → Prop) (s : CPU) : BorrowAgreement P s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem BorrowAgreement.trans {P : Addr → Prop} {s t u : CPU}
    (a : BorrowAgreement P s t) (b : BorrowAgreement P t u) : BorrowAgreement P s u :=
  ⟨a.pc.trans b.pc, a.registers.trans b.registers, fun p hp => (a.memory p hp).trans (b.memory p hp)⟩

private theorem BorrowAgreement.overlay {P : Addr → Prop} {s t : CPU} (h : BorrowAgreement P s t) :
    t = s.write t.mem := by
  cases s
  cases t
  exact congrArg₂ (fun pc regs => CPU.mk pc regs _) h.pc.symm h.registers.symm

theorem BorrowAgreement.observations {P : Addr → Prop} {s t : CPU} (h : BorrowAgreement P s t)
    (i : Instruction) : i.observations s = i.observations t := by
  rw [h.overlay]
  rcases i with ⟨op, size⟩
  cases op <;> rfl

theorem Instruction.step_local {P : Addr → Prop} {s t : CPU} (i : Instruction)
    (agree : BorrowAgreement P s t) (within : ∀ a ∈ i.op.accesses s, a.Within P) :
    BorrowAgreement P (i.step s) (i.step t) := by
  rw [agree.overlay]
  rcases i with ⟨op, size⟩
  cases op
  case load w d base off =>
    let a := s.reg base + off
    have inside := within (.read a w) (by simp [Op.accesses, a])
    have same := w.load_agrees s.mem t.mem a (fun i hi => agree.memory _ (inside i hi))
    change BorrowAgreement P ((s.advance size).put d (w.load s.mem a))
      (((s.write t.mem).advance size).put d (w.load t.mem a))
    rw [same]
    exact ⟨rfl, rfl, agree.memory⟩
  case store w r base off =>
    exact ⟨rfl, rfl, w.store_agrees s.mem t.mem _ _ P agree.memory⟩
  case branch b x y off =>
    simp only [Instruction.step, reg_write]
    split <;> exact ⟨rfl, rfl, agree.memory⟩
  all_goals exact ⟨rfl, rfl, agree.memory⟩

end Crypto.RISCV64
