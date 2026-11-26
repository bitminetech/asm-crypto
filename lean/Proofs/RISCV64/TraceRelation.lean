import Proofs.RISCV64.AccessTrace
import Proofs.RISCV64.RegisterFrame

namespace Crypto.RISCV64

abbrev PublicMask := Reg → Bool

def publicRegs (rs : List Reg) : PublicMask := fun r => r == 0 || rs.contains r

structure PublicAgreement (mask : PublicMask) (s t : CPU) : Prop where
  pc : s.pc = t.pc
  reg : ∀ r, mask r = true → s.reg r = t.reg r

private def Op.observationsPublic (op : Op) (mask : PublicMask) : Bool :=
  match op with
  | .load _ _ base _ | .store _ _ base _ => mask base
  | .branch _ lhs rhs _ => mask lhs && mask rhs
  | .ret => mask 1
  | _ => true

private def Op.resultPublic (op : Op) (mask : PublicMask) : Bool :=
  match op with
  | .add _ lhs rhs | .addw _ lhs rhs | .and _ lhs rhs | .or _ lhs rhs | .xor _ lhs rhs =>
    mask lhs && mask rhs
  | .addi _ src _ | .andi _ src _ | .slli _ src _ | .srli _ src _
  | .slliw _ src _ | .srliw _ src _ => mask src
  | .auipc .. => true
  | _ => false

private def Op.transfer (op : Op) (mask : PublicMask) : PublicMask := fun reg =>
  if reg == 0 then true else
  if op.destination == some reg then op.resultPublic mask else mask reg

private theorem Instruction.public_step (i : Instruction) {mask : PublicMask} {s t : CPU}
    (agree : PublicAgreement mask s t) (allowed : i.op.observationsPublic mask = true) :
    i.observations s = i.observations t ∧ PublicAgreement (i.op.transfer mask) (i.step s) (i.step t) := by
  rcases i with ⟨op, bytes⟩
  have pc := agree.pc
  constructor
  · cases op <;> simp only [Instruction.observations, Op.accesses, pc]
    all_goals rw [agree.reg _ allowed]
  · constructor
    · cases op
      case branch test x y off =>
        simp only [Op.observationsPublic, Bool.and_eq_true] at allowed
        simp only [Instruction.step, agree.reg x allowed.1, agree.reg y allowed.2]
        split <;> simp only [pc, pc_advance]
      case ret =>
        change mask 1 = true at allowed
        change s.reg 1 &&& _ = t.reg 1 &&& _
        rw [agree.reg 1 allowed]
      case jump => simp only [Instruction.step, pc]
      all_goals exact congrArg (· + BitVec.ofNat 64 bytes) pc
    · intro r hr
      by_cases zero : r = 0
      · subst r; rw [reg_zero, reg_zero]
      simp only [Op.transfer, beq_false_of_ne zero, Bool.false_eq_true, if_false] at hr
      by_cases dest : op.destination = some r
      · simp only [dest, beq_self_eq_true, if_true] at hr
        cases op <;> simp only [Op.destination, Option.some.injEq, reduceCtorEq] at dest
        all_goals subst r
        all_goals simp only [Op.resultPublic, Bool.and_eq_true, Bool.false_eq_true] at hr
        all_goals simp only [Instruction.step, reg_put, if_neg zero, if_pos trivial]
        all_goals first
          | rw [pc]
          | rw [agree.reg _ hr]
          | rw [agree.reg _ hr.1, agree.reg _ hr.2]
      · simp only [beq_false_of_ne dest, Bool.false_eq_true, if_false] at hr
        rw [Instruction.reg_unchanged _ _ _ dest, Instruction.reg_unchanged _ _ _ dest]
        exact agree.reg r hr

private def scanPublic : List Instruction → PublicMask → Option PublicMask
  | [], mask => some mask
  | i :: code, mask =>
    if i.op.observationsPublic mask then scanPublic code (i.op.transfer mask) else none

private theorem scan_sound {code : List Instruction} {before after : PublicMask} {s t : CPU}
    (scan : scanPublic code before = some after) (agree : PublicAgreement before s t) :
    accessTrace code s = accessTrace code t ∧ PublicAgreement after (run code s) (run code t) := by
  induction code generalizing before after s t with
  | nil =>
    simp only [scanPublic, Option.some.injEq] at scan
    subst after
    exact ⟨rfl, agree⟩
  | cons i tail ih =>
    unfold scanPublic at scan
    split at scan
    next allowed =>
      obtain ⟨headObs, stepAgree⟩ := i.public_step agree allowed
      obtain ⟨tailObs, finalAgree⟩ := ih scan stepAgree
      exact ⟨by simp only [accessTrace, headObs, tailObs], finalAgree⟩
    next => contradiction

def PublicFragment (code : List Instruction) (inputs outputs : List Reg) : Prop :=
  ∀ ⦃s t⦄, PublicAgreement (publicRegs inputs) s t →
    accessTrace code s = accessTrace code t ∧ PublicAgreement (publicRegs outputs) (run code s) (run code t)

def checkedFragment (code : List Instruction) (inputs outputs : List Reg) : Bool :=
  match scanPublic code (publicRegs inputs) with
  | none => false
  | some mask => outputs.all mask

theorem checked_public_fragment (code : List Instruction) (inputs outputs : List Reg)
    (checked : checkedFragment code inputs outputs = true) : PublicFragment code inputs outputs := by
  unfold checkedFragment at checked
  split at checked
  · contradiction
  next mask scan =>
    intro s t agree
    obtain ⟨trace, final⟩ := scan_sound scan agree
    refine ⟨trace, final.pc, ?_⟩
    intro r h
    simp only [publicRegs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    rcases h with zero | member
    · subst r; rw [reg_zero, reg_zero]
    · exact final.reg r (List.all_eq_true.mp checked r member)

theorem PublicFragment.append {a b : List Instruction} {inputs mid outputs : List Reg}
    (left : PublicFragment a inputs mid) (right : PublicFragment b mid outputs) :
    PublicFragment (a ++ b) inputs outputs := by
  intro s t agree
  obtain ⟨obsA, midAgree⟩ := left agree
  obtain ⟨obsB, outAgree⟩ := right midAgree
  exact ⟨by simp only [accessTrace_append, obsA, obsB], by simpa only [run, List.foldl_append] using outAgree⟩

end Crypto.RISCV64
