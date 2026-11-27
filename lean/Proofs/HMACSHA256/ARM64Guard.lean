import Proofs.HMACSHA256.Capacity
import Proofs.HMACSHA256.ARM64Setup
import Proofs.HMACSHA256.GuardDecoding
import Proofs.ARM64.ImportedArithmetic
import Proofs.ARM64.ImportedRound

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported (addWithCarry64_sub carry64_sub_ge)

/-- Execute the checked ARM64 capacity-check fragment after the two header
loads. The state at entry has the capacity in X4 and the count in X5. -/
def runGuard (s : Arm64.State) : Option Arm64.State := do
  let sub ← decodeAt entry 0x38
  let checkCapacity ← decodeAt entry 0x3c
  let checked := Arm64.execInstWithSvc Arm64.noSyscalls checkCapacity
    (Arm64.execInstWithSvc Arm64.noSyscalls sub s)
  if checked.pc = s.pc + 8 then
    let cmp ← decodeAt entry 0x40
    let checkCount ← decodeAt entry 0x44
    return Arm64.execInstWithSvc Arm64.noSyscalls checkCount
      (Arm64.execInstWithSvc Arm64.noSyscalls cmp checked)
  else
    return checked

theorem branch_step (s : Arm64.State) (disp : BitVec 64) :
    Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CC disp) s =
      s.setPC (if s.pstate.c then s.pc + 4#64 else s.pc + disp) := by
  cases carry : s.pstate.c <;> simp [Arm64.execInstWithSvc, Arm64.ConditionHolds, carry,
    Arm64.State.advancePC, Arm64.State.setPC]

theorem sub_step (s : Arm64.State) :
    Arm64.execInstWithSvc Arm64.noSyscalls (.addSubImm .W64 .SUBS .x4 .x4 96#12 false) s =
      let arithmetic := Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~96#64) true
      ((s.writeReg64 .x4 (s.readReg64 .x4 - 96#64)).setPState arithmetic.2).advancePC := by
  let arithmetic := Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~96#64) true
  change ((s.writeReg64 .x4 arithmetic.1).setPState arithmetic.2).advancePC = _
  rw [show arithmetic.1 = s.readReg64 .x4 - 96#64 from addWithCarry64_sub _ _]

theorem cmp_step (s : Arm64.State) :
    Arm64.execInstWithSvc Arm64.noSyscalls (.addSubShift .W64 .SUBS .xzr .x4 .x5 .LSL 0) s =
      let arithmetic := Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~s.readReg64 .x5) true
      (s.setPState arithmetic.2).advancePC := by
  have shift0 (x : BitVec 64) : Arm64.shiftVal .W64 x .LSL 0 = x := by
    simp [Arm64.shiftVal, Arm64.shift64]
  change ((s.writeReg64 .xzr
    (Arm64.AddWithCarry64 (s.readReg64 .x4)
      (~~~Arm64.shiftVal .W64 (s.readReg64 .x5) .LSL 0) true).1).setPState
    (Arm64.AddWithCarry64 (s.readReg64 .x4)
      (~~~Arm64.shiftVal .W64 (s.readReg64 .x5) .LSL 0) true).2).advancePC = _
  rw [shift0]
  rfl

theorem runGuard_result (s : Arm64.State) :
    ∃ out, runGuard s = some out ∧ out.mem = s.mem ∧ out.sp = s.sp ∧
      out.readReg64 .x0 = s.readReg64 .x0 ∧
      out.pc = if (s.readReg64 .x4).toNat < 96 + (s.readReg64 .x5).toNat then
        s.pc + 0xdc#64 else s.pc + 16#64 := by
  obtain ⟨sub, first, cmp, second⟩ := guard_decoded
  unfold runGuard
  rw [sub, first, cmp, second]
  let a := Arm64.execInstWithSvc Arm64.noSyscalls (.addSubImm .W64 .SUBS .x4 .x4 96#12 false) s
  let b := Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CC 216#64) a
  let c := Arm64.execInstWithSvc Arm64.noSyscalls (.addSubShift .W64 .SUBS .xzr .x4 .x5 .LSL 0) b
  let d := Arm64.execInstWithSvc Arm64.noSyscalls (.bCond .CC 208#64) c
  change (∃ out, (if b.pc = s.pc + 8#64 then some d else some b) = some out ∧ _)
  let remaining := s.readReg64 .x4 - 96#64
  let wrote := s.writeReg64 .x4 remaining
  let flags := (Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~96#64) true).2
  have firstCarry : flags.c = decide (96 ≤ (s.readReg64 .x4).toNat) :=
    carry64_sub_ge _ 96#64
  have b_eq : b = { wrote with
      pstate := flags
      pc := if (s.readReg64 .x4).toNat < 96 then s.pc + 0xdc#64 else s.pc + 8#64 } := by
    rw [show b = _ from branch_step a 216#64, show a = _ from sub_step s]
    change { wrote with
      pstate := flags
      pc := if flags.c then s.pc + 4#64 + 4#64 else s.pc + 4#64 + 216#64 } = _
    rw [firstCarry]
    by_cases short : (s.readReg64 .x4).toNat < 96
    · simp [short, Nat.not_le.mpr short, BitVec.add_assoc]
    · simp [short, Nat.le_of_not_gt short, BitVec.add_assoc]
  have b4 : b.readReg64 .x4 = remaining := by
    rw [b_eq]
    change wrote.readReg64 .x4 = _
    simp [wrote, Arm64.Reg.x4]
  have b5 : b.readReg64 .x5 = s.readReg64 .x5 := by
    rw [b_eq]
    change wrote.readReg64 .x5 = _
    simp (config := { decide := true }) [wrote, Arm64.Reg.x4, Arm64.Reg.x5]
  have b0 : b.readReg64 .x0 = s.readReg64 .x0 := by
    rw [b_eq]
    change wrote.readReg64 .x0 = _
    simp (config := { decide := true }) [wrote, Arm64.Reg.x4, Arm64.Reg.x0]
  have bmem : b.mem = s.mem := by rw [b_eq]; rfl
  have bsp : b.sp = s.sp := by rw [b_eq]; rfl
  have resultSize := capacity_guard (s.readReg64 .x4) (s.readReg64 .x5)
  have branch : s.pc + 0xdc#64 ≠ s.pc + 8#64 :=
    fun eq => (by decide : 0xdc#64 ≠ 8#64) ((BitVec.add_right_inj s.pc).mp eq)
  by_cases short : (s.readReg64 .x4).toNat < 96
  · have required := resultSize.mp (Or.inl short)
    have bpc : b.pc = s.pc + 0xdc#64 := by simp [b_eq, short]
    simp [bpc, branch, required, bmem, bsp, b0]
  · have bpc : b.pc = s.pc + 8#64 := by simp [b_eq, short]
    let cmpFlags := (Arm64.AddWithCarry64 remaining (~~~s.readReg64 .x5) true).2
    have c_eq : c = (b.setPState cmpFlags).advancePC := by
      rw [show c = _ from cmp_step b, b4, b5]
    have cmpCarry : cmpFlags.c = decide ((s.readReg64 .x5).toNat ≤ remaining.toNat) :=
      carry64_sub_ge _ _
    have d_eq : d = (b.setPC (if cmpFlags.c then s.pc + 16#64 else s.pc + 0xdc#64)).setPState cmpFlags := by
      rw [show d = _ from branch_step c 208#64, c_eq]
      change { b with
        pstate := cmpFlags
        pc := if cmpFlags.c then b.pc + 4#64 + 4#64 else b.pc + 4#64 + 208#64 } = _
      rw [bpc]
      simp [Arm64.State.setPC, Arm64.State.setPState, BitVec.add_assoc]
    have dmem : d.mem = s.mem := by rw [d_eq]; exact bmem
    have dsp : d.sp = s.sp := by rw [d_eq]; exact bsp
    have d0 : d.readReg64 .x0 = s.readReg64 .x0 := by rw [d_eq]; exact b0
    by_cases shortCount : remaining.toNat < (s.readReg64 .x5).toNat
    · have required := resultSize.mp (Or.inr shortCount)
      have dpc : d.pc = s.pc + 0xdc#64 := by
        rw [d_eq, Arm64.State.setPState, Arm64.State.setPC, cmpCarry]
        simp [Nat.not_le.mpr shortCount]
      simp [bpc, dmem, dsp, d0, dpc, required]
    · have required : ¬ (s.readReg64 .x4).toNat < 96 + (s.readReg64 .x5).toNat :=
        fun h => (resultSize.mpr h).elim short shortCount
      have dpc : d.pc = s.pc + 16#64 := by
        rw [d_eq, Arm64.State.setPState, Arm64.State.setPC, cmpCarry]
        simp [Nat.le_of_not_gt shortCount]
      simp [bpc, dmem, dsp, d0, dpc, required]

theorem runGuard_segments {s out : Arm64.State} (run : runGuard s = some out) :
    out.status = s.status ∧
    (∀ r : BitVec 5, r ≠ 4#5 → out.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
    ∃ after, runRange entry 0x38 2 s = some after ∧ after.status = s.status ∧
      (if (s.readReg64 .x4).toNat < 96 then out = after
       else after.pc = s.pc + 8#64 ∧ runRange entry 0x40 2 after = some out) := by
  let sub := Arm64.Instr.addSubImm .W64 .SUBS .x4 .x4 96#12 false
  let first := Arm64.Instr.bCond .CC 216#64
  let cmp := Arm64.Instr.addSubShift .W64 .SUBS .xzr .x4 .x5 .LSL 0
  let second := Arm64.Instr.bCond .CC 208#64
  let a := Arm64.execInstWithSvc Arm64.noSyscalls sub s
  let checked := Arm64.execInstWithSvc Arm64.noSyscalls first a
  let finish := Arm64.execInstWithSvc Arm64.noSyscalls second
    (Arm64.execInstWithSvc Arm64.noSyscalls cmp checked)
  obtain ⟨dsub, dfirst, dcmp, dsecond⟩ := guard_decoded
  unfold runGuard at run
  rw [dsub, dfirst, dcmp, dsecond] at run
  change (if checked.pc = s.pc + 8#64 then some finish else some checked) = some out at run
  have firstRange : runRange entry 0x38 2 s = some checked := by
    have dec : decodeRange entry 0x38 2 = some [sub, first] := by decide +kernel
    rw [runRange, dec]
    rfl
  have secondRange : runRange entry 0x40 2 checked = some finish := by
    have dec : decodeRange entry 0x40 2 = some [cmp, second] := by decide +kernel
    rw [runRange, dec]
    rfl
  have firstPC : checked.pc =
      if (s.readReg64 .x4).toNat < 96 then s.pc + 0xdc#64 else s.pc + 8#64 := by
    have flags := carry64_sub_ge (s.readReg64 .x4) 96#64
    change (Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~96#64) true).2.c =
      decide (96 ≤ (s.readReg64 .x4).toNat) at flags
    rw [show checked = _ from branch_step a 216#64, show a = _ from sub_step s]
    change (if (Arm64.AddWithCarry64 (s.readReg64 .x4) (~~~96#64) true).2.c
      then (s.pc + 4#64) + 4#64 else (s.pc + 4#64) + 216#64) = _
    rw [flags]
    by_cases short : (s.readReg64 .x4).toNat < 96
    · simp [short, Nat.not_le.mpr short, BitVec.add_assoc]
    · simp [short, Nat.le_of_not_gt short, BitVec.add_assoc]
  have checkedReg (r : BitVec 5) (other : r ≠ 4#5) :
      checked.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    rw [show checked = _ from branch_step a 216#64, show a = _ from sub_step s]
    simp [Crypto.ARM64.Imported.reg_set_pc, Crypto.ARM64.Imported.reg_set_pstate,
      Crypto.ARM64.Imported.reg_write_gpr, Arm64.Reg.x4, other]
    intro zero
    subst r
    rfl
  have checkedStatus : checked.status = s.status := by
    rw [show checked = _ from branch_step a 216#64, show a = _ from sub_step s]
    rfl
  have finishStatus : finish.status = s.status := by
    rw [show finish = _ from branch_step _ 208#64, show
      Arm64.execInstWithSvc Arm64.noSyscalls cmp checked = _ from cmp_step checked]
    exact checkedStatus
  have finishedReg (r : BitVec 5) (other : r ≠ 4#5) :
      finish.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    rw [show finish = _ from branch_step _ 208#64, show
      Arm64.execInstWithSvc Arm64.noSyscalls cmp checked = _ from cmp_step checked]
    simp [Crypto.ARM64.Imported.reg_set_pc, Crypto.ARM64.Imported.reg_set_pstate, checkedReg _ other]
  by_cases short : (s.readReg64 .x4).toNat < 96
  · have different : s.pc + 0xdc#64 ≠ s.pc + 8#64 := by
      intro eq
      exact (by decide : 0xdc#64 ≠ 8#64) ((BitVec.add_right_inj s.pc).mp eq)
    rw [firstPC, if_pos short, if_neg different, Option.some.injEq] at run
    subst out
    exact ⟨checkedStatus, checkedReg, checked, firstRange, checkedStatus, by simp [short]⟩
  · rw [firstPC, if_neg short, if_pos rfl, Option.some.injEq] at run
    subst out
    exact ⟨finishStatus, finishedReg, checked, firstRange, checkedStatus,
      by rw [if_neg short]; exact ⟨by simpa only [if_neg short] using firstPC, secondRange⟩⟩

end Crypto.HMACSHA256.ARM64
