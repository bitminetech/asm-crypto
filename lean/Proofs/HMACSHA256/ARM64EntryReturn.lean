import Proofs.HMACSHA256.ARM64EntryResources

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported
open Crypto.Baseline (Region)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
/-- Restore the top-level calling convention from the original spill words,
whether the capacity guard or the successful helper call reached the return. -/
theorem entry_return (base : Addr) (s before : Arm64.State)
    (loaded : (programAt entry (routineAddress base entry)).CodeLoaded before.mem)
    (pc : before.pc = routineAddress base entry + 0x114#64)
    (running : before.status = .Running)
    (stack : before.sp = s.sp - 160#64)
    (aligned : before.spAligned = true)
    (readable : ∀ i : Fin 12, before.mem.canRead (before.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (spill : ∀ i : Fin 96, before.mem.cells (before.sp + BitVec.ofNat 64 i.val) =
      (frameMem s 160#64).cells (before.sp + BitVec.ofNat 64 i.val)) :
    let events := frameReturnEvents (routineAddress base entry + 0x114#64) (s.sp - 160#64) 160#64 (s.readReg64 .lr)
    ∃ out, LinkedExecution base before events out ∧
      out.readReg64 .x0 = before.readReg64 .x0 ∧ out.sp = s.sp ∧
      out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      out.mem = before.mem := by
  have words (i : Fin 12) : before.mem.read64 (before.sp + BitVec.ofNat 64 (8 * i.val)) =
      s.readReg64 (savedRegister i.val) := by
    calc
      _ = (frameMem s 160#64).read64 (before.sp + BitVec.ofNat 64 (8 * i.val)) := by
        apply read64_eq_of_cells
        intro j
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact spill ⟨8 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
      _ = _ := by
        rw [stack, frameMem]
        exact writeWords_word _ _ _ 12 _ i.isLt (by decide)
  let out := restoreState before 160#64
  have body : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨run, _⟩ := run_range_observes body pc (by decide) loaded (by decide +kernel)
    (returns before aligned readable).1 (show out.status = .Running from running)
  have events : rangeEvents entry 0x114 7 before =
      frameReturnEvents (routineAddress base entry + 0x114#64) (s.sp - 160#64) 160#64 (s.readReg64 .lr) := by
    have observed := restore_code_events before 160#64 aligned readable
    have wordLink : before.mem.read64 (before.sp + 8#64) = s.readReg64 .lr := words ⟨1, by decide⟩
    rw [wordLink, pc, stack] at observed
    simpa only [rangeEvents, entry_return_decoded, Option.getD_some] using observed
  rw [events] at run
  refine ⟨out, run, ?_, ?_, words ⟨1, by decide⟩, running, ?_, rfl⟩
  · simp (config := {decide := true}) [out, restoreState, restoreRegs, Arm64.Reg.x0, Arm64.Reg.x19,
      Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24, Arm64.Reg.x25,
      Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.lr, reg_write_gpr, reg_write_sp]
  · change before.sp + 160#64 = _
    rw [stack, BitVec.sub_add_cancel]
  · intro i
    exact (restored_register before 160#64 i).trans (words i)

end Crypto.HMACSHA256.ARM64
