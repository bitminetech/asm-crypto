import Proofs.ARM64.ImportedRound
import equiv.SHA256.Foldl.Schedule

/-!
One SHA-256 schedule-expansion body under the unchanged imported ISA model:
15 recorded words at offsets 0xc4–0xfc, excluding the counter/branch at 0x100.
The proof keeps the four read guards and one write guard active. It establishes
exactly the native 32-bit store and preserves the remaining architectural state,
X0–X6 and X18–X30, while advancing PC by 60 bytes.

The FIPS bridge relates this one stored word to `specScheduleStep`. The whole
48-iteration loop, the stack-array layout, instruction fetching and complete
`equal` baseline are separate proof obligations.
-/

namespace Crypto.ARM64.Imported

theorem addWithCarry64_add (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x y false).1 = x + y := by
  simp [Arm64.AddWithCarry64, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_add, BitVec.add_comm]

@[simp] theorem mem_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).mem = m := by cases s; rfl

@[simp] theorem stable_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    stable (s.setMem m) = { stable s with mem := m } := by cases s; rfl
@[simp] theorem reg_set_mem (s : Arm64.State) (m : Arm64.Memory) (r : Arm64.Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] theorem sp_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[simp] theorem pc_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).pc = s.pc := by cases s; rfl
@[simp] theorem status_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
@[simp] theorem nv_set_mem (s : Arm64.State) (m : Arm64.Memory) :
    nonvolatile (s.setMem m) = nonvolatile s := by funext i; exact reg_set_mem s m _

theorem bv_add_left_comm {n : Nat} (x y z : BitVec n) : x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

def scheduleCode : List (BitVec 32) := (imageWords.toList.drop 49).take 15

def scheduleAddress (s : Arm64.State) : BitVec 64 := s.sp + (s.readReg64 .x5 <<< 2)

def scheduleValue (s : Arm64.State) : BitVec 32 :=
  SHS.SHA256.smallSigma1 (s.mem.read32 (scheduleAddress s + 0xfffffffffffffff8#64)) +
  s.mem.read32 (scheduleAddress s + 0xffffffffffffffe4#64) +
  SHS.SHA256.smallSigma0 (s.mem.read32 (scheduleAddress s + 0xffffffffffffffc4#64)) +
  s.mem.read32 (scheduleAddress s + 0xffffffffffffffc0#64)

private theorem schedule_decoded : scheduleCode.mapM Arm64.decode = some [
    .addSubExt .W64 .ADD .x17 .sp .x5 .UXTX 2,
    .ldr .W32 .W32 false .x15 (.UnscaledOffset .x17 0xffffffffffffffc4#64),
    .extr .W32 .x16 .x15 .x15 7,
    .logicalShift .W32 .EOR .x16 .x16 .x15 .ROR 18,
    .logicalShift .W32 .EOR .x16 .x16 .x15 .LSR 3,
    .ldr .W32 .W32 false .x15 (.UnscaledOffset .x17 0xfffffffffffffff8#64),
    .extr .W32 .x7 .x15 .x15 17,
    .logicalShift .W32 .EOR .x7 .x7 .x15 .ROR 19,
    .logicalShift .W32 .EOR .x7 .x7 .x15 .LSR 10,
    .ldr .W32 .W32 false .x15 (.UnscaledOffset .x17 0xffffffffffffffc0#64),
    .addSubShift .W32 .ADD .x16 .x16 .x15 .LSL 0,
    .ldr .W32 .W32 false .x15 (.UnscaledOffset .x17 0xffffffffffffffe4#64),
    .addSubShift .W32 .ADD .x16 .x16 .x15 .LSL 0,
    .addSubShift .W32 .ADD .x16 .x16 .x7 .LSL 0,
    .str .W32 .x16 (.Offset .x17 0x0000000000000000#64)] := by decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem schedule_computes (s : Arm64.State)
    (h15 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc4#64) 4 = true)
    (h2 : s.mem.canRead (scheduleAddress s + 0xfffffffffffffff8#64) 4 = true)
    (h16 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc0#64) 4 = true)
    (h7 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffe4#64) 4 = true)
    (hw : s.mem.canWrite (scheduleAddress s) 4 = true) :
    (runWords scheduleCode s).map (fun out => (out.mem, out.sp, out.pc, out.status)) =
      some (s.mem.write32 (scheduleAddress s) (scheduleValue s), s.sp, s.pc + 60, s.status) := by
  simp only [scheduleAddress, BitVec.add_assoc] at h15 h2 h16 h7 hw
  rw [runWords_decode, schedule_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execLdr, Arm64.execStr,
    Arm64.evalAddSub, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift32,
    Arm64.extendVal, Arm64.evalAddrMode, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.State.readReg32, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.Memory.writeSized, addWithCarry32_add, addWithCarry64_add,
    Round.extr_same, BitVec.truncate_eq_setWidth, scheduleAddress,
    h15, h2, h16, h7, hw, BitVec.add_assoc]
  simp (config := { decide := true }) [scheduleValue, scheduleAddress,
    SHS.SHA256.smallSigma0, SHS.SHA256.smallSigma1, SHS.ROTR, SHS.SHR,
    Round.narrow_shift, BitVec.rotateRight_def, BitVec.xor_assoc,
    BitVec.add_comm, bv_add_left_comm]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem schedule_frame (s : Arm64.State)
    (h15 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc4#64) 4 = true)
    (h2 : s.mem.canRead (scheduleAddress s + 0xfffffffffffffff8#64) 4 = true)
    (h16 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc0#64) 4 = true)
    (h7 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffe4#64) 4 = true)
    (hw : s.mem.canWrite (scheduleAddress s) 4 = true) :
    (runWords scheduleCode s).map (fun out =>
      (stable out, out.pc, nonvolatile out,
       out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
       out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
      some ({ stable s with mem := s.mem.write32 (scheduleAddress s) (scheduleValue s) },
       s.pc + 60, nonvolatile s,
       s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
       s.readReg64 .x3, s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6) := by
  simp only [scheduleAddress, BitVec.add_assoc] at h15 h2 h16 h7 hw
  rw [runWords_decode, schedule_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execLdr, Arm64.execStr,
    Arm64.evalAddSub, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift32,
    Arm64.extendVal, Arm64.evalAddrMode, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.State.readReg32, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.Memory.writeSized, addWithCarry32_add, addWithCarry64_add,
    Round.extr_same, BitVec.truncate_eq_setWidth, scheduleAddress,
    h15, h2, h16, h7, hw, BitVec.add_assoc]
  simp (config := { decide := true }) [scheduleValue, scheduleAddress,
    SHS.SHA256.smallSigma0, SHS.SHA256.smallSigma1, SHS.ROTR, SHS.SHR,
    Round.narrow_shift, BitVec.rotateRight_def, BitVec.xor_assoc,
    BitVec.add_comm, bv_add_left_comm]


/-- The exact scalar word stored by the body is the word inserted by the
imported FIPS schedule step, once the four earlier words have been related. -/
theorem schedule_update_matches_spec (s : Arm64.State)
    (M : Vector (BitVec 32) 16) (W : Vector (BitVec 32) 64) (t : Fin 64)
    (ht : 16 ≤ t.val)
    (h15 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffc4#64) = W[t.val - 15]!)
    (h2 : s.mem.read32 (scheduleAddress s + 0xfffffffffffffff8#64) = W[t.val - 2]!)
    (h16 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffc0#64) = W[t.val - 16]!)
    (h7 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffe4#64) = W[t.val - 7]!) :
    W.set! t.val (scheduleValue s) =
      SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M t.val W := by
  simp [SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep,
    show ¬t.val < 16 by omega, scheduleValue, h15, h2, h16, h7]

end Crypto.ARM64.Imported
