import Proofs.ARM64.ImportedSchedule
import Mathlib.Tactic.IntervalCases

/-!
The recorded ADD/CMP/B.LO controls for the 64-round and schedule loops.
The carry-bit calculation is kernel-checked for every counter in 0..63.
These lemmas establish counter increment, branch destination, state framing and
preservation of working variables for loop composition.
-/
namespace Crypto.ARM64.Imported

def roundControlCode : List (BitVec 32) := (imageWords.toList.drop 103).take 3
private theorem round_control_decoded : roundControlCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x5 .x5 1#12 false,
  .addSubImm .W64 .SUBS .xzr .x5 64#12 false,
  .bCond .CC 0xffffffffffffff80#64] := by decide +kernel

set_option maxRecDepth 4096 in
theorem counter64_carry (t : Fin 64) :
    (Arm64.AddWithCarry64 (BitVec.ofNat 64 t.val + 1#64) 0xffffffffffffffbf#64 true).2.c =
      decide (64 ≤ t.val + 1) := by
  rcases t with ⟨t, ht⟩
  change (Arm64.AddWithCarry64 (BitVec.ofNat 64 t + 1#64) 0xffffffffffffffbf#64 true).2.c = decide (64 ≤ t + 1)
  interval_cases t <;> decide +kernel

@[simp] theorem write_xzr (s : Arm64.State) (v : BitVec 64) : s.writeReg64 .xzr v = s := by cases s; rfl
@[simp] theorem reg_set_pstate (s : Arm64.State) (p : Arm64.PState) (r : Arm64.Reg) :
    (s.setPState p).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] theorem reg_set_pc (s : Arm64.State) (pc : BitVec 64) (r : Arm64.Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] theorem pc_set_pstate (s : Arm64.State) (p : Arm64.PState) : (s.setPState p).pc = s.pc := by cases s; rfl
@[simp] theorem pc_set_pc (s : Arm64.State) (pc : BitVec 64) : (s.setPC pc).pc = pc := by cases s; rfl
@[simp] theorem pstate_advance (s : Arm64.State) : s.advancePC.pstate = s.pstate := by cases s; rfl
@[simp] theorem pstate_set_pstate (s : Arm64.State) (p : Arm64.PState) : (s.setPState p).pstate = p := by cases s; rfl
@[simp] theorem nv_set_pstate (s : Arm64.State) (p : Arm64.PState) :
    nonvolatile (s.setPState p) = nonvolatile s := by funext i; exact reg_set_pstate s p _
@[simp] theorem nv_set_pc (s : Arm64.State) (pc : BitVec 64) :
    nonvolatile (s.setPC pc) = nonvolatile s := by funext i; exact reg_set_pc s pc _

@[simp] theorem working_advance (s : Arm64.State) : working s.advancePC = working s := by
  simp [working, Arm64.State.readReg32]
@[simp] theorem working_set_pstate (s : Arm64.State) (p : Arm64.PState) : working (s.setPState p) = working s := by
  simp [working, Arm64.State.readReg32]
@[simp] theorem working_set_pc (s : Arm64.State) (pc : BitVec 64) : working (s.setPC pc) = working s := by
  simp [working, Arm64.State.readReg32]
@[simp] theorem working_write5 (s : Arm64.State) (v : BitVec 64) : working (s.writeReg64 .x5 v) = working s := by
  simp [working, Arm64.State.readReg32]

def controlStable (s : Arm64.State) : Arm64.State :=
  { s with regs := Arm64.RegFile.empty, pc := 0, pstate := Arm64.PState.zero }
@[simp] theorem controlStable_advance (s : Arm64.State) : controlStable s.advancePC = controlStable s := by cases s; rfl
@[simp] theorem controlStable_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    controlStable (s.writeReg64 (.gpr i) v) = controlStable s := by cases s; rfl
@[simp] theorem controlStable_pstate (s : Arm64.State) (p : Arm64.PState) :
    controlStable (s.setPState p) = controlStable s := by cases s; rfl
@[simp] theorem controlStable_pc (s : Arm64.State) (pc : BitVec 64) :
    controlStable (s.setPC pc) = controlStable s := by cases s; rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem round_control_step (s : Arm64.State) (t : Fin 64)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    (runWords roundControlCode s).map (fun out =>
      (controlStable out, out.pc, nonvolatile out, working out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
    some (controlStable s, (if t.val + 1 < 64 then s.pc - 120#64 else s.pc + 12#64),
      nonvolatile s, working s,
      s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
      s.readReg64 .x4, BitVec.ofNat 64 (t.val + 1), s.readReg64 .x6) := by
  rw [runWords_decode, round_control_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, addWithCarry64_add, hc,
    Arm64.ConditionHolds, counter64_carry, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    apply_ite, ite_apply]
  all_goals simp (config := { decide := true }) [BitVec.ofNat_add]
  all_goals split <;> omega

def scheduleControlCode : List (BitVec 32) := (imageWords.toList.drop 64).take 3
private theorem schedule_control_decoded : scheduleControlCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x5 .x5 1#12 false,
  .addSubImm .W64 .SUBS .xzr .x5 64#12 false,
  .bCond .CC 0xffffffffffffffbc#64] := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem schedule_control_step (s : Arm64.State) (t : Fin 64)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    (runWords scheduleControlCode s).map (fun out =>
      (controlStable out, out.pc, nonvolatile out, working out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
    some (controlStable s, (if t.val + 1 < 64 then s.pc - 60#64 else s.pc + 12#64),
      nonvolatile s, working s,
      s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
      s.readReg64 .x4, BitVec.ofNat 64 (t.val + 1), s.readReg64 .x6) := by
  rw [runWords_decode, schedule_control_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, addWithCarry64_add, hc,
    Arm64.ConditionHolds, counter64_carry, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    apply_ite, ite_apply]
  all_goals simp (config := { decide := true }) [BitVec.ofNat_add]
  all_goals split <;> omega

end Crypto.ARM64.Imported
