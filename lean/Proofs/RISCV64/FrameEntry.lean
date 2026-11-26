import Proofs.RISCV64.Return
import Proofs.ARM64.ImportedZeroPad

namespace Crypto.RISCV64

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000

private def stackStores (slots : List (Reg × Nat)) : List Instruction :=
  slots.map fun (r,i) => ⟨.store .double r 2 (BitVec.ofNat 64 i), 2⟩

private theorem stack_store_values (slots : List (Reg × Nat)) (s : CPU) :
    let out := run (stackStores slots) s
    (∀ r, out.reg r = s.reg r) ∧ out.mem = slots.foldl (fun m (r,i) =>
      m.write64 (s.reg 2 + BitVec.ofNat 64 i) (s.reg r)) s.mem := by
  induction slots generalizing s with
  | nil => exact ⟨fun _ => rfl, rfl⟩
  | cons slot tail ih =>
    rcases slot with ⟨r,i⟩
    let step : Instruction := ⟨.store .double r 2 (BitVec.ofNat 64 i), 2⟩
    have keep (q : Reg) : (step.step s).reg q = s.reg q := rfl
    have memory : (step.step s).mem =
        s.mem.write64 (s.reg 2 + BitVec.ofNat 64 i) (s.reg r) := rfl
    exact ⟨fun q => ((ih (step.step s)).1 q).trans (keep q), by
      simpa only [List.foldl_cons, keep, memory] using (ih (step.step s)).2⟩

def savedSlots : List (Reg × Nat) :=
  [8,9,18,19,20,21,22,23].zipIdx.map fun (r,i) => (r, 416 + 8*i)

private def allocate : Instruction := ⟨.addi 2 2 (-480), 2⟩

def saveFrame : List Instruction := allocate :: stackStores savedSlots

private theorem saveFrame_decoded : decodeSeq 0 9 = some saveFrame := by decide +kernel

def spilled (s : CPU) (frame : Addr) : Memory :=
  savedSlots.foldl (fun m (r,i) => m.write64 (frame + BitVec.ofNat 64 i) (s.reg r)) s.mem

private theorem save_run (s : CPU) :
    run saveFrame s = run (stackStores savedSlots) (allocate.step s) := by
  simp only [saveFrame, run, List.foldl_cons]

private theorem spill_values (slots : List (Reg × Nat)) (m : Memory) (sp : Addr)
    (before after : Reg → Addr) (same : ∀ slot ∈ slots, before slot.1 = after slot.1) :
    slots.foldl (fun mem (r,i) => mem.write64 (sp + BitVec.ofNat 64 i) (before r)) m =
    slots.foldl (fun mem (r,i) => mem.write64 (sp + BitVec.ofNat 64 i) (after r)) m := by
  induction slots generalizing m with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨r,i⟩
    simp only [List.foldl_cons]
    rw [same (r,i) List.mem_cons_self]
    exact ih _ (fun slot h => same slot (List.mem_cons_of_mem _ h))

attribute [local irreducible] run Arm64.Memory.write64

theorem frame_entered (base : Addr) (s : CPU) (pc : s.pc = base) :
    let out := run saveFrame s
    ImageExecution base s saveFrame out ∧ out.pc = base + 0x12 ∧
      out.reg 2 = s.reg 2 - 480 ∧ out.mem = spilled s (s.reg 2 - 480) := by
  have linear : saveFrame.all Instruction.linear = true := by decide
  refine ⟨ImageExecution.linear_run base s _ 0 (by simpa using pc) (by decide)
    saveFrame_decoded linear, ?_, ?_⟩
  · rw [linear_end_pc _ s linear, pc]; rfl
  have sp : (allocate.step s).reg 2 = s.reg 2 - 480 := by
    simp (config := { decide := true }) [allocate, Instruction.step, BitVec.sub_eq_add_neg]
  have keep (r : Reg) (h : r ≠ 2#5) : (allocate.step s).reg r = s.reg r := by
    simp only [allocate, Instruction.step, reg_put, reg_advance]
    split
    · next hz => subst r; rfl
    · change r ≠ (2 : Reg) at h
      rw [if_neg h]
  have write := stack_store_values savedSlots (allocate.step s)
  rw [save_run]
  refine ⟨(write.1 2).trans sp, ?_⟩
  change (run (stackStores savedSlots) (allocate.step s)).mem = _
  rw [write.2, sp]
  have unchanged : (allocate.step s).mem = s.mem := rfl
  rw [unchanged]
  unfold spilled
  apply spill_values
  intro slot member
  apply keep
  have check : savedSlots.all (fun item => !(item.1 == 2#5)) = true := by decide
  simpa using List.all_eq_true.mp check slot member

private def paddingSlots : List (Reg × Nat) :=
  (List.range 16).map fun i => (0, 288 + 8*i)

def zeroPadding : List Instruction := stackStores paddingSlots

private theorem zeroPadding_decoded : decodeSeq 0x1e 16 = some zeroPadding := by decide +kernel

def cleared (m : Memory) (padding : Addr) : Memory :=
  (List.range 16).foldl (fun acc i => acc.write64 (padding + BitVec.ofNat 64 (8*i)) 0) m

theorem padding_cleared (base : Addr) (s : CPU) (pc : s.pc = base + 0x1e) :
    let out := run zeroPadding s
    ImageExecution base s zeroPadding out ∧ out.pc = base + 0x3e ∧
      out.reg 2 = s.reg 2 ∧ out.mem = cleared s.mem (s.reg 2 + 288) := by
  have linear : zeroPadding.all Instruction.linear = true := by decide
  have write := stack_store_values paddingSlots s
  refine ⟨ImageExecution.linear_run base s _ 0x1e pc (by decide) zeroPadding_decoded linear,
    ?_, write.1 2, ?_⟩
  · rw [linear_end_pc _ _ linear, pc, BitVec.add_assoc]; rfl
  · change (run (stackStores paddingSlots) s).mem = _
    rw [write.2]
    simp only [paddingSlots, cleared, List.foldl_map,
      reg_zero, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

end Crypto.RISCV64
