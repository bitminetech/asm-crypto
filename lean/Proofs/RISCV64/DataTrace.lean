import Proofs.RISCV64.CallCode
import Proofs.RISCV64.Permissions

namespace Crypto.RISCV64

def dataTrace : List Instruction → CPU → List Access
  | [], _ => []
  | i :: tail, s => i.op.accesses s ++ dataTrace tail (i.step s)

theorem dataTrace_eq (code : List Instruction) (s : CPU) :
    dataTrace code s = (accessTrace code s).filter Access.isData := by
  induction code generalizing s with
  | nil => rfl
  | cons i tail ih =>
    have onlyData : (i.op.accesses s).filter Access.isData = i.op.accesses s := by
      cases op : i.op <;> simp [Op.accesses, Access.isData]
    simp only [dataTrace, accessTrace, Instruction.observations, List.cons_append,
      List.filter_cons, Access.isData, Bool.false_eq_true, if_false, List.filter_append, onlyData, ih]

theorem dataTrace_append (a b : List Instruction) (s : CPU) :
    dataTrace (a ++ b) s = dataTrace a s ++ dataTrace b (run a s) := by
  simp only [dataTrace_eq, accessTrace_append, List.filter_append]

def InRegion (base : Addr) (length : Nat) (address : Addr) (width : Width) : Prop :=
  ∃ off, off + width.bytes ≤ length ∧ off % width.bytes = 0 ∧ address = base + BitVec.ofNat 64 off

theorem InRegion.enclose {base address : Addr} {start inner outer : Nat} {width : Width}
    (within : InRegion (base + BitVec.ofNat 64 start) inner address width) (size : start + inner ≤ outer)
    (aligned : start % width.bytes = 0) :
    InRegion base outer address width := by
  obtain ⟨off, fit, offAligned, addr⟩ := within
  refine ⟨start + off, by omega, by rw [Nat.add_mod, aligned, offAligned]; simp, ?_⟩
  rw [addr, BitVec.ofNat_add, BitVec.add_assoc]

private theorem latch_data (limit back : Addr) (s : CPU) : dataTrace (latch limit back) s = [] := rfl

set_option maxRecDepth 10000 in
theorem load_cycle_data (s : CPU) : dataTrace loadCycle s =
    [.read (tableAddress s 12) .byte, .read (tableAddress s 12 + 1) .byte,
      .read (tableAddress s 12 + 2) .byte, .read (tableAddress s 12 + 3) .byte,
      .write (tableAddress s 2) .word] := by
  simp (config := { decide := true }) [loadCycle, latch_data, dataTrace,
    inputWordBody, Op.accesses, Instruction.step, tableAddress]

set_option maxRecDepth 10000 in
theorem expand_cycle_data (s : CPU) : dataTrace expansionCycle s =
    [.read (tableAddress s 2 - 60) .word, .read (tableAddress s 2 - 8) .word,
      .read (tableAddress s 2 - 64) .word, .read (tableAddress s 2 - 28) .word,
      .write (tableAddress s 2) .word] := by
  simp (config := { decide := true }) [expansionCycle, latch_data, dataTrace,
    expansionBody, Op.accesses, Instruction.step, tableAddress, BitVec.sub_eq_add_neg]

set_option maxRecDepth 12000 in
theorem round_cycle_data (s : CPU) : dataTrace roundCycle s =
    [.read (tableAddress s 10) .word, .read (tableAddress s 2) .word] := by
  simp (config := { decide := true }) [roundCycle, latch_data, dataTrace,
    roundBody, Op.accesses, Instruction.step, tableAddress]

def BlockData (stack payload constants : Addr) : Access → Prop
  | .read addr w => InRegion stack 288 addr w ∨ InRegion payload 64 addr w ∨ InRegion constants 256 addr w
  | .write addr w => InRegion stack 288 addr w
  | .fetch .. => False

theorem load_cycle_within (s : CPU) (t : Fin 16) (index : s.reg 15 = BitVec.ofNat 64 t.val)
    (access : Access) (found : access ∈ dataTrace loadCycle s) :
    BlockData (s.reg 2) (s.reg 12) (s.reg 10) access := by
  let i : Fin 64 := ⟨t.val, by have := t.isLt; omega⟩
  rw [load_cycle_data, table_index s 12 i index, table_index s 2 i index] at found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with h | h | h | h | h <;> subst access
  · exact .inr (.inl ⟨4*t.val, by have := t.isLt; change 4*t.val+1 ≤ 64; omega, Nat.mod_one _, rfl⟩)
  · refine .inr (.inl ⟨4*t.val+1, by have := t.isLt; change 4*t.val+1+1 ≤ 64; omega, Nat.mod_one _, ?_⟩)
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · refine .inr (.inl ⟨4*t.val+2, by have := t.isLt; change 4*t.val+2+1 ≤ 64; omega, Nat.mod_one _, ?_⟩)
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · refine .inr (.inl ⟨4*t.val+3, by have := t.isLt; change 4*t.val+3+1 ≤ 64; omega, Nat.mod_one _, ?_⟩)
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · exact ⟨4*t.val, by have := t.isLt; change 4*t.val+4 ≤ 288; omega, by simp [Width.bytes], rfl⟩

theorem expand_cycle_within (s : CPU) (t : Fin 64) (advanced : 16 ≤ t.val)
    (index : s.reg 15 = BitVec.ofNat 64 t.val) (access : Access) (found : access ∈ dataTrace expansionCycle s) :
    BlockData (s.reg 2) (s.reg 12) (s.reg 10) access := by
  have := t.isLt
  have previous (k : Nat) (small : k ≤ t.val) :
      InRegion (s.reg 2) 288 (tableAddress s 2 - BitVec.ofNat 64 (4*k)) .word := by
    refine ⟨4*(t.val-k), by change 4*(t.val-k)+4 ≤ 288; omega, by simp [Width.bytes], ?_⟩
    rw [table_index s 2 t index, Crypto.ARM64.Imported.slot_address_back _ _ _ small]
  rw [expand_cycle_data] at found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with h | h | h | h | h <;> subst access
  · exact .inl (previous 15 (by omega))
  · exact .inl (previous 2 (by omega))
  · exact .inl (previous 16 advanced)
  · exact .inl (previous 7 (by omega))
  · exact ⟨4*t.val, by change 4*t.val+4 ≤ 288; omega, by simp [Width.bytes], table_index s 2 t index⟩

theorem round_cycle_within (s : CPU) (t : Fin 64) (index : s.reg 15 = BitVec.ofNat 64 t.val)
    (access : Access) (found : access ∈ dataTrace roundCycle s) :
    BlockData (s.reg 2) (s.reg 12) (s.reg 10) access := by
  have := t.isLt
  rw [round_cycle_data] at found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with h | h <;> subst access
  · exact .inr (.inr ⟨4*t.val, by change 4*t.val+4 ≤ 256; omega, by simp [Width.bytes], table_index s 10 t index⟩)
  · exact .inl ⟨4*t.val, by change 4*t.val+4 ≤ 288; omega, by simp [Width.bytes], table_index s 2 t index⟩

end Crypto.RISCV64
