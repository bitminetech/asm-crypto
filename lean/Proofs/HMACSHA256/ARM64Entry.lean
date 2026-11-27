import Proofs.HMACSHA256.ARM64Frame
import Proofs.HMACSHA256.ARM64Guard

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

theorem entry_guard_inputs_decoded :
    decodeRange entry 0x1c 7 = some [
      .logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0,
      .logicalShift .W64 .ORR .x20 .xzr .x1 .LSL 0,
      .logicalShift .W64 .ORR .x21 .xzr .x2 .LSL 0,
      .logicalShift .W64 .ORR .x22 .xzr .x3 .LSL 0,
      .moveWide .W64 .MOVZ .x0 1#16 0,
      .ldr .W64 .X64 false .x4 (.Offset .x21 0#64),
      .ldr .W64 .X64 false .x5 (.Offset .x20 16#64)] := by decide +kernel

def guardInputs (s : Arm64.State) : Arm64.State :=
  let st := s.writeReg64 .x19 (s.readReg64 .x0)
  let st := st.writeReg64 .x20 (s.readReg64 .x1)
  let st := st.writeReg64 .x21 (s.readReg64 .x2)
  let st := st.writeReg64 .x22 (s.readReg64 .x3)
  let st := st.writeReg64 .x0 1#64
  let st := st.writeReg64 .x4 (s.mem.read64 (s.readReg64 .x2))
  let st := st.writeReg64 .x5 (s.mem.read64 (s.readReg64 .x1 + 16#64))
  st.setPC (s.pc + 28#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
theorem entry_guard_inputs (s : Arm64.State)
    (capacityRead : s.mem.canRead (s.readReg64 .x2) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x1 + 16#64) 8 = true) :
    runRange entry 0x1c 7 s = some (guardInputs s) := by
  unfold runRange
  rw [entry_guard_inputs_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift,
    Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64, Arm64.execMoveWide, Arm64.execLdr,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3, Arm64.Reg.x4, Arm64.Reg.x5,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, guardInputs, capacityRead, countRead]
  simp (config := { decide := true }) [Arm64.State.writeReg64, Arm64.State.advancePC,
    Arm64.State.setPC, Arm64.RegFile.write, Arm64.RegFile.read, BitVec.add_assoc,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3, Arm64.Reg.x4, Arm64.Reg.x5,
    Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22]

/-- The undersized path reaches the shared epilogue, returns status 1, and
leaves every byte outside the save area unchanged. There are no helper calls
on this path. The range executions use the decoded instructions in the image. -/
theorem undersized_entry (s : Arm64.State) (aligned : s.spAligned = true)
    (frameAligned : (s.sp - 160#64) &&& 15#64 = 0#64)
    (stackWrite : ∀ i : Fin 12,
      s.mem.canWrite (s.sp - 160#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (stackRead : ∀ i : Fin 12,
      s.mem.canRead (s.sp - 160#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (capacityRead : s.mem.canRead (s.readReg64 .x2) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x1 + 16#64) 8 = true)
    (separate : ∀ p, p = s.readReg64 .x2 ∨ p = s.readReg64 .x1 + 16#64 →
      ∀ i : Fin 8, 96 ≤ (p + BitVec.ofNat 64 i.val - (s.sp - 160#64)).toNat)
    (short : (s.mem.read64 (s.readReg64 .x2)).toNat <
      96 + (s.mem.read64 (s.readReg64 .x1 + 16#64)).toNat) :
    ∃ afterSave afterLoads afterCheck out,
      runRange entry 0 7 s = some afterSave ∧
      runRange entry 0x1c 7 afterSave = some afterLoads ∧
      runGuard afterLoads = some afterCheck ∧ afterCheck.pc = s.pc + 0x114#64 ∧
      runRange entry 0x114 7 afterCheck = some out ∧
      out.readReg64 .x0 = 1#64 ∧ out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      (∀ p, 96 ≤ (p - (s.sp - 160#64)).toNat → out.mem.cells p = s.mem.cells p) := by
  let saved := enteredState s 160#64
  let loaded := guardInputs saved
  have saveSP : saved.sp = s.sp - 160#64 := rfl
  have savePC : saved.pc = s.pc + 28#64 := rfl
  have saveMem : saved.mem = frameMem s 160#64 := rfl
  have saveX1 : saved.readReg64 .x1 = s.readReg64 .x1 := by
    simp (config := { decide := true }) [saved, enteredState, Arm64.Reg.x1,
      Arm64.Reg.x29, Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.RegFile.read,
      Arm64.RegFile.write, Arm64.State.setPC, Arm64.State.setMem]
  have saveX2 : saved.readReg64 .x2 = s.readReg64 .x2 := by
    simp (config := { decide := true }) [saved, enteredState, Arm64.Reg.x2,
      Arm64.Reg.x29, Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.RegFile.read,
      Arm64.RegFile.write, Arm64.State.setPC, Arm64.State.setMem]
  have readable (p : Addr) (r : s.mem.canRead p 8 = true) : saved.mem.canRead p 8 = true := by
    rw [saveMem]
    exact writeWords_canRead _ _ _ 12 p 8 r
  have fixed (p : Addr) (part : p = s.readReg64 .x2 ∨ p = s.readReg64 .x1 + 16#64) :
      saved.mem.read64 p = s.mem.read64 p := by
    apply read64_eq_of_cells
    intro i
    rw [saveMem]
    exact writeWords_outside _ _ _ 12 _ (separate _ part i)
  have readCap : saved.mem.canRead (saved.readReg64 .x2) 8 = true := saveX2 ▸ readable _ capacityRead
  have readCount : saved.mem.canRead (saved.readReg64 .x1 + 16#64) 8 = true := by
    rw [saveX1]
    exact readable _ countRead
  have capacity : loaded.readReg64 .x4 = s.mem.read64 (s.readReg64 .x2) := by
    have field : loaded.readReg64 .x4 = saved.mem.read64 (saved.readReg64 .x2) := by
      simp (config := { decide := true }) [loaded, guardInputs, Arm64.Reg.x4, Arm64.Reg.x5]
    rw [field, saveX2, fixed _ (Or.inl rfl)]
  have count : loaded.readReg64 .x5 = s.mem.read64 (s.readReg64 .x1 + 16#64) := by
    have field : loaded.readReg64 .x5 = saved.mem.read64 (saved.readReg64 .x1 + 16#64) := by
      simp (config := { decide := true }) [loaded, guardInputs, Arm64.Reg.x5]
    rw [field, saveX1, fixed _ (Or.inr rfl)]
  have status : loaded.readReg64 .x0 = 1#64 := by
    simp (config := { decide := true }) [loaded, guardInputs, Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5]
  obtain ⟨checked, guardRun, guardMem, guardSP, guardStatus, guardPC⟩ := runGuard_result loaded
  have ss : checked.sp = s.sp - 160#64 := guardSP.trans saveSP
  have sm : checked.mem = frameMem s 160#64 := guardMem.trans saveMem
  have next : checked.pc = s.pc + 0x114#64 := by
    rw [guardPC, capacity, count, if_pos short]
    have lp : loaded.pc = saved.pc + 28#64 := rfl
    rw [lp, savePC]
    simp [BitVec.add_assoc]
  have retAligned : checked.spAligned = true := by
    simp [Arm64.State.spAligned, ss, frameAligned]
  have retRead (i : Fin 12) : checked.mem.canRead (checked.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [ss, sm]
    exact writeWords_canRead _ _ _ 12 _ _ (stackRead i)
  have finish := (returns checked retAligned retRead).1
  refine ⟨saved, loaded, checked, restoreState checked 160#64, enter_entry _ aligned frameAligned stackWrite,
    entry_guard_inputs _ readCap readCount, guardRun, next, finish, ?_, ?_, ?_, ?_, ?_⟩
  · have rest : (restoreState checked 160#64).readReg64 .x0 = checked.readReg64 .x0 := by
      simp (config := { decide := true }) [restoreState, restoreRegs, Arm64.Reg.x0, Arm64.Reg.x19,
        Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23, Arm64.Reg.x24, Arm64.Reg.x25,
        Arm64.Reg.x26, Arm64.Reg.x27, Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.lr,
        Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.State.setPC,
        Arm64.RegFile.read, Arm64.RegFile.write]
    exact rest.trans (guardStatus.trans status)
  · change checked.sp + 160#64 = s.sp
    rw [ss, BitVec.sub_add_cancel]
  · change checked.mem.read64 (checked.sp + 8#64) = _
    rw [ss, sm]
    exact writeWords_word _ _ _ 12 1 (by decide) (by decide)
  · intro i
    rw [restored_register, ss, sm]
    exact writeWords_word _ _ _ 12 i.val i.isLt (by decide)
  · intro p outside
    change checked.mem.cells p = s.mem.cells p
    rw [sm]
    exact writeWords_outside _ _ _ 12 p outside

end Crypto.HMACSHA256.ARM64
