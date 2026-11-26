import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

def Op.destination (op : Op) : Option Reg :=
  match op with
  | .add d .. | .addw d .. | .and d .. | .or d .. | .xor d ..
  | .addi d .. | .andi d .. | .slli d .. | .srli d .. | .slliw d .. | .srliw d ..
  | .auipc d .. | .load _ d .. => some d
  | .store .. | .branch .. | .jump .. | .ret => none

theorem Instruction.reg_unchanged (i : Instruction) (s : CPU) (r : Reg)
    (noWrite : i.op.destination ≠ some r) : (i.step s).reg r = s.reg r := by
  have different (d : Reg) (result : i.op.destination = some d) : r ≠ d := by
    intro h
    subst d
    exact noWrite result
  by_cases zero : r = 0#5
  · subst r
    simp [CPU.reg]
  · rcases i with ⟨op, bytes⟩
    cases op <;> first
    | rfl
    | solve | simp [Instruction.step, zero, different _ rfl]
    | simp only [Instruction.step]; split <;> rfl

theorem run_reg_unchanged (s : CPU) (code : List Instruction) (r : Reg)
    (noWrite : ∀ i ∈ code, i.op.destination ≠ some r) :
    (run code s).reg r = s.reg r := by
  induction code generalizing s with
  | nil => rfl
  | cons i tail ih =>
    change (run tail (i.step s)).reg r = s.reg r
    rw [ih _ (fun j hj => noWrite j (List.mem_cons_of_mem _ hj))]
    exact i.reg_unchanged s r (noWrite i (by simp))

theorem ImageExecution.register_unchanged {base : Addr} {s out : CPU} {code : List Instruction}
    (exec : ImageExecution base s code out) (r : Reg)
    (noWrite : ∀ i ∈ code, i.op.destination ≠ some r) :
    out.reg r = s.reg r := by
  induction exec with
  | nil => rfl
  | @cons s out i tail _ _ _ ih =>
    exact (ih (fun j hj => noWrite j (List.mem_cons_of_mem _ hj))).trans
      (i.reg_unchanged s r (noWrite i (by simp)))

theorem ImageExecution.register_checked {base : Addr} {s out : CPU} {code : List Instruction}
    (exec : ImageExecution base s code out) (r : Reg)
    (kept : code.all (fun i => i.op.destination != some r) = true) :
    out.reg r = s.reg r := by
  apply exec.register_unchanged
  intro i hi
  simpa using List.all_eq_true.mp kept i hi

end Crypto.RISCV64
