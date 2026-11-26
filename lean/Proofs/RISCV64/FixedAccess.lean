import Proofs.RISCV64.DataTrace

namespace Crypto.RISCV64

structure FixedRegion where
  write : Bool
  reg : Reg
  size : Nat

def FixedRegion.allows (r : FixedRegion) (s : CPU) : Access → Prop
  | .read addr w => r.write = false ∧ InRegion (s.reg r.reg) r.size addr w
  | .write addr w => r.write = true ∧ InRegion (s.reg r.reg) r.size addr w
  | .fetch .. => False

private def fixedOperand (regions : List FixedRegion) (write : Bool) (base : Reg)
    (width : Width) (offset : Addr) : Bool :=
  regions.any fun r => (r.write == write) && (r.reg == base) &&
    decide (offset.toNat + width.bytes ≤ r.size) && (offset.toNat % width.bytes == 0)

private def fixedOp (regions : List FixedRegion) : Op → Bool
  | .load w _ base offset => fixedOperand regions false base w offset
  | .store w _ base offset => fixedOperand regions true base w offset
  | _ => true

def checkedFixedAccess (code : List Instruction) (regions : List FixedRegion) : Bool :=
  code.all fun inst => fixedOp regions inst.op && regions.all fun r => inst.op.destination != some r.reg

private theorem fixedOperand_sound {rs : List FixedRegion} {write : Bool} {base : Reg}
    {width : Width} {offset : Addr} (h : fixedOperand rs write base width offset = true) (s : CPU) :
    ∃ r ∈ rs, r.write = write ∧ InRegion (s.reg r.reg) r.size (s.reg base + offset) width := by
  obtain ⟨r, inList, check⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at check
  obtain ⟨⟨⟨writeEq, baseEq⟩, space⟩, align⟩ := check
  exact ⟨r, inList, writeEq, offset.toNat, space, align, by simp [baseEq]⟩

private theorem fixedOp_sound {rs : List FixedRegion} {op : Op} (h : fixedOp rs op = true)
    {s : CPU} {a : Access} (found : a ∈ op.accesses s) : ∃ r ∈ rs, r.allows s a := by
  cases op <;> simp only [Op.accesses, List.mem_cons, List.not_mem_nil, or_false] at found
  case load w d base offset =>
    subst a
    exact fixedOperand_sound h s
  case store w r base offset =>
    subst a
    exact fixedOperand_sound h s

theorem fixed_accesses {code : List Instruction} {regions : List FixedRegion}
    (checked : checkedFixedAccess code regions = true) {s : CPU} {access : Access}
    (found : access ∈ dataTrace code s) : ∃ r ∈ regions, r.allows s access := by
  induction code generalizing s with
  | nil => simp [dataTrace] at found
  | cons i tail ih =>
    simp only [checkedFixedAccess, List.all_cons, Bool.and_eq_true] at checked
    rcases List.mem_append.mp found with now | later
    · exact fixedOp_sound checked.1.1 now
    · obtain ⟨r, listed, allowed⟩ := ih checked.2 later
      have stable := i.reg_unchanged s r.reg (by simpa using List.all_eq_true.mp checked.1.2 r listed)
      refine ⟨r, listed, ?_⟩
      cases access
      · exact allowed
      · simpa only [FixedRegion.allows, stable] using allowed
      · simpa only [FixedRegion.allows, stable] using allowed

theorem empty_dataTrace {code : List Instruction} (checked : checkedFixedAccess code [] = true) (s : CPU) :
    dataTrace code s = [] := by
  cases trace : dataTrace code s with
  | nil => rfl
  | cons first rest =>
    have inside : first ∈ dataTrace code s := by rw [trace]; exact List.mem_cons_self
    obtain ⟨_, impossible, _⟩ := fixed_accesses checked inside
    nomatch impossible

end Crypto.RISCV64
