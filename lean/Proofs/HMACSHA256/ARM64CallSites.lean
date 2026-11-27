import Proofs.HMACSHA256.ARM64Calls

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

def routineAddress (base : Addr) (routine : Routine) : Addr := base + BitVec.ofInt 64 routine.offset
def shaAddress (base : Addr) : Addr := base + BitVec.ofInt 64 sha256Offset

def innerCallState (s : Arm64.State) : Arm64.State :=
  let saved := (s.writeReg64 .x19 (s.readReg64 .x1)).writeReg64 .x20 (s.readReg64 .x2)
  let args := saved.writeReg64 .x1 (s.sp + 184#64)
  (args.writeReg64 .lr (s.pc + 16#64)).setPC (s.pc - 3580#64)

def outerCallState (s : Arm64.State) : Arm64.State :=
  let args := (s.writeReg64 .x0 (s.sp + 96#64)).writeReg64 .x1 (s.readReg64 .x20)
  (args.writeReg64 .lr (s.pc + 12#64)).setPC (s.pc - 3700#64)

theorem inner_call (s : Arm64.State) : runRange finish 0x1c 4 s = some (innerCallState s) := by
  unfold innerCallState
  rw [BitVec.sub_eq_add_neg]
  exact finish_inner_call s

theorem outer_call (s : Arm64.State) : runRange finish 0x94 3 s = some (outerCallState s) := by
  unfold outerCallState
  rw [BitVec.sub_eq_add_neg]
  exact finish_outer_call s

private theorem inner_relocation :
    BitVec.ofInt 64 finish.offset + (0x1c#64 + (-3580#64)) = BitVec.ofInt 64 sha256Offset := by decide +kernel

private theorem outer_relocation :
    BitVec.ofInt 64 finish.offset + (0x94#64 + (-3700#64)) = BitVec.ofInt 64 sha256Offset := by decide +kernel

theorem inner_target (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base finish + 0x1c#64) :
    (innerCallState s).pc = shaAddress base := by
  change s.pc - 3580#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc,
    inner_relocation]

theorem outer_target (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base finish + 0x94#64) :
    (outerCallState s).pc = shaAddress base := by
  change s.pc - 3700#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc,
    outer_relocation]

theorem inner_call_registers (s : Arm64.State) :
    (innerCallState s).readReg64 .x0 = s.readReg64 .x0 ∧
    (innerCallState s).readReg64 .x1 = s.sp + 184#64 ∧
    (innerCallState s).readReg64 .x19 = s.readReg64 .x1 ∧
    (innerCallState s).readReg64 .x20 = s.readReg64 .x2 ∧
    (innerCallState s).readReg64 .lr = s.pc + 16#64 ∧
    (innerCallState s).sp = s.sp ∧ (innerCallState s).mem = s.mem := by
  simp (config := { decide := true }) [innerCallState, Arm64.State.readReg64, Arm64.State.writeReg64,
    Arm64.State.setPC, Arm64.RegFile.read, Arm64.RegFile.write,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.lr]

theorem outer_call_registers (s : Arm64.State) :
    (outerCallState s).readReg64 .x0 = s.sp + 96#64 ∧
    (outerCallState s).readReg64 .x1 = s.readReg64 .x20 ∧
    (outerCallState s).readReg64 .lr = s.pc + 12#64 ∧
    (outerCallState s).sp = s.sp ∧ (outerCallState s).mem = s.mem := by
  simp (config := { decide := true }) [outerCallState, Arm64.State.readReg64, Arm64.State.writeReg64,
    Arm64.State.setPC, Arm64.RegFile.read, Arm64.RegFile.write,
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x20, Arm64.Reg.lr]

theorem inner_link (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base finish + 0x1c#64) :
    (innerCallState s).readReg64 .lr = routineAddress base finish + 0x2c#64 := by
  rw [(inner_call_registers s).2.2.2.2.1, pc, BitVec.add_assoc]
  rfl

theorem outer_link (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base finish + 0x94#64) :
    (outerCallState s).readReg64 .lr = routineAddress base finish + 0xa0#64 := by
  rw [(outer_call_registers s).2.2.1, pc, BitVec.add_assoc]
  rfl

end Crypto.HMACSHA256.ARM64
