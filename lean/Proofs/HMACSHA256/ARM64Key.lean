import Proofs.HMACSHA256.ARM64CopyLoop
import Proofs.HMACSHA256.ARM64LongKey

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference

private theorem key_length_decoded :
    decodeRange key 0x2c 3 = some [
      .ldr .W64 .X64 false .x2 (.Offset .x0 16#64),
      .addSubImm .W64 .SUBS .xzr .x2 64#12 false,
      .bCond .HI 60#64] := by decide +kernel

private theorem length_branch (count : Addr) :
    Arm64.ConditionHolds .HI (Arm64.AddWithCarry64 count (~~~64#64) true).2 =
      decide (64 < count.toNat) := by
  let flags := (Arm64.AddWithCarry64 count (~~~64#64) true).2
  have carry : flags.c = decide (64 ≤ count.toNat) := carry64_sub_ge _ 64#64
  have zero : flags.z = (count - 64#64 == 0#64) := by
    have sub := addWithCarry64_sub count 64#64
    change flags.z = _
    change ((Arm64.AddWithCarry64 count (~~~64#64) true).1 == 0#64) = _
    rw [sub]
  change (flags.c && !flags.z) = _
  rw [carry, zero]
  by_cases enough : 64 < count.toNat
  · have unequal : count - 64#64 ≠ 0#64 := by
      intro h
      have eq := BitVec.sub_add_cancel count 64#64
      rw [h, BitVec.zero_add] at eq
      symm at eq
      rw [eq] at enough
      contradiction
    simp [enough, Nat.le_of_lt enough, unequal]
  · by_cases eq : count = 64#64
    · subst count
      decide
    · have small : count.toNat < 64 := by
        have ne : count.toNat ≠ 64 := fun equal => eq (BitVec.eq_of_toNat_eq equal)
        omega
      simp [enough, Nat.not_le_of_gt small]

def keyTestState (s : Arm64.State) (count : Addr) : Arm64.State :=
  let flags := (Arm64.AddWithCarry64 count (~~~64#64) true).2
  ((s.writeReg64 .x2 count).setPState flags).setPC
    (if 64 < count.toNat then s.pc + 68#64 else s.pc + 12#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem key_length_test (s : Arm64.State) (count : Addr)
    (headerAt : s.mem.read64 (s.readReg64 .x0 + 16#64) = count)
    (headerRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true) :
    runRange key 0x2c 3 s = some (keyTestState s count) := by
  unfold runRange
  rw [key_length_decoded]
  have branch : Arm64.ConditionHolds .HI (Arm64.AddWithCarry64 count 0xffffffffffffffbf#64 true).2 =
      decide (64 < count.toNat) := length_branch count
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execLdr,
    Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.State.readReg, Arm64.State.writeReg, reg_advance, reg_write_gpr,
    Arm64.Reg.x0, Arm64.Reg.x2, headerRead, headerAt, branch,
    keyTestState, BitVec.add_assoc]
  split <;> simp [Arm64.State.setPC, Arm64.State.advancePC, Arm64.State.setPState, BitVec.add_assoc] <;> rfl

private theorem key_source_decoded :
    decodeRange key 0x38 2 = some [
      .ldr .W64 .X64 false .x3 (.Offset .x0 8#64),
      .addSubShift .W64 .ADD .x3 .x0 .x3 .LSL 0] := by decide +kernel

def keyCopyStart (s : Arm64.State) : Arm64.State :=
  (s.writeReg64 .x3 (s.readReg64 .x0 + s.mem.read64 (s.readReg64 .x0 + 8#64))).setPC (s.pc + 8#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem key_short_source (s : Arm64.State)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true) :
    runRange key 0x38 2 s = some (keyCopyStart s) := by
  unfold runRange
  rw [key_source_decoded]
  simp (config := {decide := true}) [runDecoded, Arm64.execInstWithSvc, Arm64.execLdr,
    Arm64.execAddSubShift, Arm64.evalAddSub, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.shiftVal, Arm64.shift64, Arm64.Reg.x0,
    Arm64.Reg.x3, offsetRead, addWithCarry64_add, BitVec.add_assoc, keyCopyStart]
  simp (config := {decide := true}) [Arm64.State.writeReg64, Arm64.State.setPC,
    Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, BitVec.add_assoc]
  funext r
  by_cases same : r = 3#5 <;> simp [same]

private theorem key_jump_decoded :
    decodeRange key 0x6c 1 = some [.b 8#64] := by decide +kernel

private theorem key_jump (s : Arm64.State) : runRange key 0x6c 1 s = some (s.setPC (s.pc + 8#64)) := by
  simp [runRange, key_jump_decoded, runDecoded, Arm64.execInstWithSvc]

def keyTestEvents (base sp input : Addr) (long : Bool) : List InstructionObservation :=
  let pc := routineAddress base key + 0x2c#64
  [⟨pc, pc + 4#64, sp, sp, [⟨false, input + 16#64, 8⟩]⟩,
   ⟨pc + 4#64, pc + 8#64, sp, sp, []⟩,
   ⟨pc + 8#64, routineAddress base key + (if long then 0x70#64 else 0x38#64), sp, sp, []⟩]

def keySourceEvents (base sp input : Addr) : List InstructionObservation :=
  let pc := routineAddress base key + 0x38#64
  [⟨pc, pc + 4#64, sp, sp, [⟨false, input + 8#64, 8⟩]⟩,
   ⟨pc + 4#64, pc + 8#64, sp, sp, []⟩]

def keyJumpEvents (base sp : Addr) : List InstructionObservation :=
  [⟨routineAddress base key + 0x6c#64, routineAddress base key + 0x74#64, sp, sp, []⟩]

def keyShortEvents (base sp input output : Addr) (message : ByteList) : List InstructionObservation :=
  keyTestEvents base sp input false ++ keySourceEvents base sp input ++
  copyPayloadEvents (routineAddress base key + 0x40#64) sp (input + BitVec.ofNat 64 message.offset)
    output message.bytes.size ++ keyJumpEvents base sp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
set_option linter.unusedSimpArgs false in
theorem key_test_events (base : Addr) (s : Arm64.State) (count : Addr)
    (pc : s.pc = routineAddress base key + 0x2c#64)
    (headerAt : s.mem.read64 (s.readReg64 .x0 + 16#64) = count)
    (headerRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true) :
    rangeEvents key 0x2c 3 s = keyTestEvents base s.sp (s.readReg64 .x0) (decide (64 < count.toNat)) := by
  have branch : Arm64.ConditionHolds .HI (Arm64.AddWithCarry64 count 0xffffffffffffffbf#64 true).2 =
      decide (64 < count.toNat) := length_branch count
  have read : s.mem.canRead (s.regs.regs 0#5 + 16#64) 8 = true := headerRead
  have value : s.mem.read64 (s.regs.regs 0#5 + 16#64) = count := headerAt
  by_cases long : 64 < count.toNat <;>
    simp (config := {decide := true}) [rangeEvents, key_length_decoded, keyTestEvents, decodedEvents,
      instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execAddSubImm,
      Arm64.evalAddSub, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
      Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.State.readReg,
      Arm64.State.writeReg, Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.State.advancePC,
      Arm64.State.setPC, Arm64.State.setPState, Arm64.RegFile.read, Arm64.RegFile.write, Arm64.Reg.x0, Arm64.Reg.x2,
      Arm64.Reg.xzr, pc, read, value, headerAt, headerRead, branch, long, BitVec.add_assoc]

set_option maxHeartbeats 1400000 in
set_option linter.unusedSimpArgs false in
private theorem key_setup_events (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base key + 0x38#64)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true) :
    rangeEvents key 0x38 2 s = keySourceEvents base s.sp (s.readReg64 .x0) := by
  have read : s.mem.canRead (s.regs.regs 0#5 + 8#64) 8 = true := offsetRead
  simp (config := {decide := true}) [rangeEvents, key_source_decoded, keySourceEvents, decodedEvents,
    instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execAddSubShift,
    Arm64.evalAddSub, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.State.readReg,
    Arm64.State.writeReg, Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.State.advancePC,
    Arm64.State.setPC, Arm64.RegFile.read, Arm64.RegFile.write, Arm64.Reg.x0, Arm64.Reg.x3,
    read, offsetRead, pc, BitVec.add_assoc]

private theorem key_jump_events (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base key + 0x6c#64) :
    rangeEvents key 0x6c 1 s = keyJumpEvents base s.sp := by
  simp [rangeEvents, key_jump_decoded, keyJumpEvents, decodedEvents, instructionObservation, dataAccesses,
    Arm64.execInstWithSvc, Arm64.State.setPC, pc, BitVec.add_assoc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3800000 in
/-- The short key follows the decoded branch and copy, and reaches the
native epilogue with the padded EthLib K0 and unchanged nonvolatile state. -/
theorem short_key_after_clear (base : Addr) (s : Arm64.State) (input : ByteList)
    (pc : s.pc = routineAddress base key + 0x2c#64)
    (code : (programAt key (routineAddress base key)).CodeLoaded s.mem)
    (live : s.status = .Running) (short : input.bytes.size ≤ 64)
    (countAt : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 input.bytes.size)
    (offsetAt : s.mem.read64 (s.readReg64 .x0 + 8#64) = BitVec.ofNat 64 input.offset)
    (countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true)
    (payload : ∀ i, i < input.bytes.size → s.mem.read8 (s.readReg64 .x0 + BitVec.ofNat 64 (input.offset + i)) =
      input.bytes[i]!.toBitVec)
    (zeroTail : ∀ i : Fin 64, input.bytes.size ≤ i.val →
      s.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = 0#8)
    (apart : ∀ i < input.bytes.size, input.bytes.size ≤
      (s.readReg64 .x0 + BitVec.ofNat 64 (input.offset + i) - s.readReg64 .x1).toNat)
    (readable : ∀ w i, i + (copyWidth w).bytes ≤ input.bytes.size →
      s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (input.offset + i)) (copyWidth w).bytes = true)
    (writable : ∀ w i, i + (copyWidth w).bytes ≤ input.bytes.size →
      s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 i) (copyWidth w).bytes = true) :
    let events := keyShortEvents base s.sp (s.readReg64 .x0) (s.readReg64 .x1) input
    ∃ out, LinkedExecution base s events out ∧
      events.length = 9 + 6 * (input.bytes.size / 8) + 5 * (input.bytes.size % 8) ∧
      out.pc = routineAddress base key + 0x74#64 ∧ out.status = .Running ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, input.bytes.size ≤ (p - s.readReg64 .x1).toNat → out.mem.cells p = s.mem.cells p) ∧
      nonvolatile out = nonvolatile s ∧ nonMemory out = nonMemory s := by
  let count := BitVec.ofNat 64 input.bytes.size
  let tested := keyTestState s count
  let prepared := keyCopyStart tested
  have countBound : input.bytes.size < 2 ^ 64 := by omega
  have test : runRange key 0x2c 3 s = some tested := key_length_test s count countAt countRead
  have testedPC : tested.pc = routineAddress base key + 0x38#64 := by
    change (if 64 < count.toNat then s.pc + 68#64 else s.pc + 12#64) = _
    have condition : ¬ 64 < count.toNat := by
      change ¬ 64 < (BitVec.ofNat 64 input.bytes.size).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
      omega
    rw [if_neg condition, pc, BitVec.add_assoc]
    rfl
  have x0 : tested.readReg64 .x0 = s.readReg64 .x0 := by
    simp (config := {decide := true}) [tested, keyTestState, reg_set_pstate, reg_set_pc, reg_write_gpr, Arm64.Reg.x0, Arm64.Reg.x2]
  have prepare : runRange key 0x38 2 tested = some prepared :=
    key_short_source tested (by rw [x0]; exact offsetRead)
  have prepPC : prepared.pc = routineAddress base (copyRoutine false) + BitVec.ofNat 64 (copyOffset false true) := by
    change tested.pc + 8#64 = _
    rw [testedPC, BitVec.add_assoc]
    rfl
  have src : prepared.readReg64 (copySource false) = s.readReg64 .x0 + BitVec.ofNat 64 input.offset := by
    have mem : tested.mem = s.mem := rfl
    simp (config := {decide := true}) [prepared, keyCopyStart, copySource, x0, mem, offsetAt,
      reg_set_pc, reg_write_gpr, Arm64.Reg.x3]
  have dst : prepared.readReg64 (copyDestination false) = s.readReg64 .x1 := by
    simp (config := {decide := true}) [prepared, tested, keyCopyStart, keyTestState, copyDestination,
      reg_set_pstate, reg_set_pc, reg_write_gpr, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3]
  have n : prepared.readReg64 (copyCount false) = count := by
    simp (config := {decide := true}) [prepared, tested, keyCopyStart, keyTestState, copyCount,
      reg_set_pstate, reg_set_pc, reg_write_gpr, Arm64.Reg.x2, Arm64.Reg.x3]
  have belongs : key = entry ∨ key = key ∨ key = finish := .inr (.inl rfl)
  obtain ⟨checked, na⟩ := run_range_observes belongs pc (by decide) code (by decide +kernel) test
    (show tested.status = .Running from live)
  obtain ⟨setup, nb⟩ := run_range_observes belongs testedPC (by decide) (checked.keeps_code _ code)
    (by decide +kernel) prepare (show prepared.status = .Running from live)
  have front := checked.append setup
  obtain ⟨copied, copy, ncopy, copiedPC, _, values, frames, nv, unchanged, _, _⟩ :=
    copy_payload false base prepared input.bytes.size prepPC (front.keeps_code _ code) live n countBound
      (by intro i hi; rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add]; exact apart i hi)
      (by intro w i hi; rw [src, BitVec.add_assoc, ← BitVec.ofNat_add]; exact readable w i hi)
      (by intro w i hi; rw [dst]; exact writable w i hi)
  have reach : copied.pc = routineAddress base key + 0x6c#64 := by
    rw [copiedPC, prepPC, BitVec.add_assoc]
    rfl
  have running : copied.status = .Running := (congrArg Arm64.State.status unchanged).trans live
  let out := copied.setPC (copied.pc + 8#64)
  have throughCopy := front.append copy
  obtain ⟨jump, nc⟩ := run_range_observes belongs reach (by decide) (throughCopy.keeps_code _ code)
    (by decide +kernel) (key_jump copied) (show out.status = .Running from running)
  have shortTrace := key_test_events base s count pc countAt countRead
  have small : ¬64 < count.toNat := by
    change ¬64 < (BitVec.ofNat 64 input.bytes.size).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
    omega
  have noLong : decide (64 < count.toNat) = false := by simp [small]
  rw [noLong] at shortTrace
  have preparedTrace := key_setup_events base tested testedPC (by rw [x0]; exact offsetRead)
  have testedSP : tested.sp = s.sp := rfl
  have preparedSP : prepared.sp = s.sp := rfl
  have copiedSP : copied.sp = s.sp := by
    change (nonMemory copied).sp = _
    rw [unchanged]
    exact preparedSP
  rw [testedSP, x0] at preparedTrace
  have jumpedTrace := key_jump_events base copied reach
  rw [copiedSP] at jumpedTrace
  have copyPC : prepared.pc = routineAddress base key + 0x40#64 := prepPC
  rw [copyPC, preparedSP, src, dst] at copy ncopy
  rw [shortTrace] at checked na
  rw [preparedTrace] at setup nb
  rw [jumpedTrace] at jump nc
  refine ⟨out, ((checked.append setup).append copy).append jump, ?_, ?_, running, ?_, ?_, ?_, ?_⟩
  · simp only [keyShortEvents, List.length_append, na, nb, ncopy, nc]
    omega
  · change copied.pc + 8#64 = _
    rw [reach, BitVec.add_assoc]
    rfl
  · intro i
    rw [hmacKey_short_byte input short i]
    by_cases inside : i.val < input.bytes.size
    · rw [if_pos inside]
      change copied.mem.read8 _ = _
      rw [← dst, values _ inside, src, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact payload i.val inside
    · rw [if_neg inside]
      change copied.mem.read8 _ = _
      have off : input.bytes.size ≤ (s.readReg64 .x1 + BitVec.ofNat 64 i.val - s.readReg64 .x1).toNat := by
        rw [address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
        omega
      have keep := frames _ (by rw [dst]; exact off)
      exact (read8_of_cell _ keep).trans (zeroTail i (by omega))
  · intro p off
    exact frames p (by rw [dst]; exact off)
  · change nonvolatile copied = _
    rw [nv]
    have testedNV : nonvolatile tested = nonvolatile s := by
      change nonvolatile (s.writeReg64 .x2 count) = _
      simpa only using nv_write_gpr s 2#5 count (by decide)
    change nonvolatile (tested.writeReg64 .x3 _) = _
    rw [nv_write_gpr _ _ _ (by decide), testedNV]
  · rw [nonMemory_pc, unchanged]
    exact rfl

end Crypto.HMACSHA256.ARM64
