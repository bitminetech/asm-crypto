import Proofs.ARM64.ImportedArithmetic
import Proofs.ARM64.ImportedScheduleCycle

/-!
The recorded padding-tail byte-copy cycle and terminating compare/branch.
The cycle is proved when the byte counter is below the remainder, with the
actual byte read/write guards. Its state frame preserves all GPRs other than
X6/X7 and all modeled nonvolatile state. Byte-range helpers frame the stores.
Complete copying, padding, fetching and whole-call `equal` remain separate.
-/
namespace Crypto.ARM64.Imported

def copyRegisters (s : Arm64.State) : BitVec 5 → BitVec 64 :=
  fun j => if j = 6#5 ∨ j = 7#5 then 0 else s.readReg64 (.gpr j)

@[simp] theorem copyRegs_advance (s : Arm64.State) : copyRegisters s.advancePC = copyRegisters s := by
  funext j; simp [copyRegisters]
@[simp] theorem copyRegs_pstate (s : Arm64.State) (ps : Arm64.PState) : copyRegisters (s.setPState ps) = copyRegisters s := by
  funext j; simp [copyRegisters]
@[simp] theorem copyRegs_mem (s : Arm64.State) (m : Arm64.Memory) : copyRegisters (s.setMem m) = copyRegisters s := by
  funext j; simp [copyRegisters]
@[simp] theorem copyRegs_pc (s : Arm64.State) (pc : BitVec 64) : copyRegisters (s.setPC pc) = copyRegisters s := by
  funext j; simp [copyRegisters]
@[simp] theorem copyRegs_write67 (s : Arm64.State) (index : BitVec 5) (v : BitVec 64)
    (h : index = 6#5 ∨ index = 7#5) : copyRegisters (s.writeReg64 (.gpr index) v) = copyRegisters s := by
  rcases h with rfl | rfl <;> funext j
  all_goals
    by_cases h31 : j = 31#5
    · subst j; simp [copyRegisters, Arm64.State.readReg64]
    · by_cases h6 : j = 6#5 <;> by_cases h7 : j = 7#5 <;> simp [copyRegisters, h31, h6, h7]

@[simp] theorem mem_set_pstate (s : Arm64.State) (ps : Arm64.PState) : (s.setPState ps).mem = s.mem := by cases s; rfl
@[simp] theorem nonMemory_advance (s : Arm64.State) : nonMemory s.advancePC = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) : nonMemory (s.writeReg64 (.gpr i) v) = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_pstate (s : Arm64.State) (ps : Arm64.PState) : nonMemory (s.setPState ps) = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_pc (s : Arm64.State) (pc : BitVec 64) : nonMemory (s.setPC pc) = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_mem (s : Arm64.State) (m : Arm64.Memory) : nonMemory (s.setMem m) = nonMemory s := by cases s; rfl

@[simp] theorem copy_mem_set_pc (s : Arm64.State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by cases s; rfl

def tailCopyCycleCode : List (BitVec 32) := (imageWords.toList.drop 17).take 6
private theorem tail_copy_cycle_decoded : tailCopyCycleCode.mapM Arm64.decode = some [
  .addSubShift .W64 .SUBS .xzr .x6 .x17 .LSL 0,
  .bCond .CS 20#64,
  .ldr .W32 .B8 false .x7 (.RegOffset .x5 .x6 .UXTX 0),
  .str .B8 .x7 (.RegOffset .x16 .x6 .UXTX 0),
  .addSubImm .W64 .ADD .x6 .x6 1#12 false,
  .b 0xffffffffffffffec#64] := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem tail_copy_cycle (s : Arm64.State)
    (hlt : (s.readReg64 .x6).toNat < (s.readReg64 .x17).toNat)
    (hr : s.mem.canRead (s.readReg64 .x5 + s.readReg64 .x6) 1 = true)
    (hw : s.mem.canWrite (s.readReg64 .x16 + s.readReg64 .x6) 1 = true) :
    (runWords tailCopyCycleCode s).map (fun out =>
      (nonMemory out, copyRegisters out, out.mem, out.pc, nonvolatile out, out.readReg64 .x6)) =
      some (nonMemory s, copyRegisters s,
        s.mem.write8 (s.readReg64 .x16 + s.readReg64 .x6)
          (s.mem.read8 (s.readReg64 .x5 + s.readReg64 .x6)),
        s.pc, nonvolatile s, s.readReg64 .x6 + 1#64) := by
  have hnot : ¬(s.readReg64 .x17).toNat ≤ (s.readReg64 .x6).toNat := Nat.not_le.mpr hlt
  rw [runWords_decode, tail_copy_cycle_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execAddSubShift, Arm64.execAddSubImm, Arm64.execLdr, Arm64.execStr,
    Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.extendVal, Arm64.MemWidth.bytes,
    Arm64.Memory.readSized, Arm64.Memory.writeSized, Arm64.ConditionHolds,
    carry64_sub_ge, addWithCarry64_add, hnot, hr, hw, BitVec.truncate_eq_setWidth,
    BitVec.add_assoc]

theorem copyRegisters_read {before after : Arm64.State}
    (h : copyRegisters after = copyRegisters before) (j : BitVec 5)
    (hj : ¬(j = 6#5 ∨ j = 7#5)) :
    after.readReg64 (.gpr j) = before.readReg64 (.gpr j) := by
  have point := congrFun h j
  simpa only [copyRegisters, if_neg hj] using point

def tailCopyEndCode : List (BitVec 32) := tailCopyCycleCode.take 2
private theorem tail_copy_end_decoded : tailCopyEndCode.mapM Arm64.decode = some [
  .addSubShift .W64 .SUBS .xzr .x6 .x17 .LSL 0,
  .bCond .CS 20#64] := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem tail_copy_end (s : Arm64.State)
    (hge : (s.readReg64 .x17).toNat ≤ (s.readReg64 .x6).toNat) :
    (runWords tailCopyEndCode s).map (fun out =>
      (nonMemory out, copyRegisters out, out.mem, out.pc, nonvolatile out, out.readReg64 .x6)) =
      some (nonMemory s, copyRegisters s, s.mem,
        s.pc + 24#64, nonvolatile s, s.readReg64 .x6) := by
  rw [runWords_decode, tail_copy_end_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execAddSubShift, Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.ConditionHolds,
    carry64_sub_ge, hge, BitVec.add_assoc]

@[simp] theorem canWrite_write8 (m : Arm64.Memory) (base : BitVec 64) (value : BitVec 8)
    (a : BitVec 64) (n : Nat) : (m.write8 base value).canWrite a n = m.canWrite a n := by
  simp [Arm64.Memory.canWrite]

theorem byte128_outside (base p : BitVec 64) (i : Fin 128)
    (h : 128 ≤ (p - base).toNat) : p ≠ base + BitVec.ofNat 64 i.val := by
  intro he
  rw [he, address_delta] at h
  have hi := i.isLt
  have bound : i.val < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at h
  omega

theorem byte128_store_outside (m : Arm64.Memory) (base p : BitVec 64) (i : Fin 128)
    (v : BitVec 8) (h : 128 ≤ (p - base).toNat) :
    (m.write8 (base + BitVec.ofNat 64 i.val) v).cells p = m.cells p :=
  cells_write8_outside m _ p v (byte128_outside base p i h)

theorem byte128_address_inj (base : BitVec 64) (i j : Fin 128) :
    (base + BitVec.ofNat 64 i.val = base + BitVec.ofNat 64 j.val) ↔ i.val = j.val := by
  rw [BitVec.add_right_inj]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    have hi : i.val < 2 ^ 64 := by have := i.isLt; omega
    have hj : j.val < 2 ^ 64 := by have := j.isLt; omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hn
  · intro h
    rw [h]

end Crypto.ARM64.Imported
