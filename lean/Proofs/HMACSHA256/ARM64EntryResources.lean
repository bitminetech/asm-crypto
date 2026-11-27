import Proofs.HMACSHA256.ARM64EntryCalls
import Proofs.HMACSHA256.ARM64KeyResources

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference
open Crypto.Baseline (Region)

def entryKeyInput (s : Arm64.State) (extent : Nat) : Region := ⟨s.readReg64 .x0, extent⟩
def entryMessage (s : Arm64.State) (extent : Nat) : Region := ⟨s.readReg64 .x1, extent⟩
def entryScratch (s : Arm64.State) (capacity : Nat) : Region := ⟨s.readReg64 .x2, capacity⟩
def entryMac (s : Arm64.State) : Region := ⟨s.readReg64 .x3, 32⟩
def entryWorkspace (s : Arm64.State) : Region := stackRegion s.sp 800
def entrySaved (s : Arm64.State) : Region := ⟨s.sp - 160#64, 96⟩

structure EntryResources (base : Addr) (s : Arm64.State) (keyExtent messageExtent capacity : Nat) : Prop where
  available : 800 ≤ s.sp.toNat
  aligned : s.sp.toNat % 16 = 0
  keyAligned : (s.readReg64 .x0).toNat % 8 = 0
  messageAligned : (s.readReg64 .x1).toNat % 8 = 0
  scratchAligned : (s.readReg64 .x2).toNat % 8 = 0
  macAligned : (s.readReg64 .x3).toNat % 8 = 0
  keyValid : (entryKeyInput s keyExtent).Valid
  messageValid : (entryMessage s messageExtent).Valid
  scratchValid : (entryScratch s capacity).Valid
  macValid : (entryMac s).Valid
  imageValid : (callerImage (shaAddress base)).Valid
  stackKey : (entryWorkspace s).Disjoint (entryKeyInput s keyExtent)
  stackMessage : (entryWorkspace s).Disjoint (entryMessage s messageExtent)
  stackScratch : (entryWorkspace s).Disjoint (entryScratch s capacity)
  stackMac : (entryWorkspace s).Disjoint (entryMac s)
  stackImage : (entryWorkspace s).Disjoint (callerImage (shaAddress base))
  scratchKey : (entryScratch s capacity).Disjoint (entryKeyInput s keyExtent)
  scratchMessage : (entryScratch s capacity).Disjoint (entryMessage s messageExtent)
  scratchMac : (entryScratch s capacity).Disjoint (entryMac s)
  scratchImage : (entryScratch s capacity).Disjoint (callerImage (shaAddress base))
  macKey : (entryMac s).Disjoint (entryKeyInput s keyExtent)
  macMessage : (entryMac s).Disjoint (entryMessage s messageExtent)
  macImage : (entryMac s).Disjoint (callerImage (shaAddress base))
  keyRead : ∀ p, (entryKeyInput s keyExtent).Contains p → s.mem.canRead p 1 = true
  messageRead : ∀ p, (entryMessage s messageExtent).Contains p → s.mem.canRead p 1 = true
  scratchRead : ∀ p, (entryScratch s capacity).Contains p → s.mem.canRead p 1 = true
  scratchWrite : ∀ p, (entryScratch s capacity).Contains p → s.mem.canWrite p 1 = true
  macWrite : ∀ p, (entryMac s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (entryWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (entryWorkspace s).Contains p → s.mem.canWrite p 1 = true

def entryArgumentEvents (pc sp scratch message : Addr) : List InstructionObservation :=
  (List.range 7).map fun i =>
    let ip := pc + BitVec.ofNat 64 (4 * i)
    let accesses : List DataAccess :=
      if i = 5 then [⟨false, scratch, 8⟩] else if i = 6 then [⟨false, message + 16#64, 8⟩] else []
    ⟨ip, ip + 4#64, sp, sp, accesses⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
set_option linter.unusedSimpArgs false in
private theorem entry_argument_events (s : Arm64.State)
    (scratchRead : s.mem.canRead (s.readReg64 .x2) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x1 + 16#64) 8 = true) :
    rangeEvents entry 0x1c 7 s = entryArgumentEvents s.pc s.sp (s.readReg64 .x2) (s.readReg64 .x1) := by
  have scratch : s.mem.canRead (s.regs.regs 2#5) 8 = true := scratchRead
  have count : s.mem.canRead (s.regs.regs 1#5 + 16#64) 8 = true := countRead
  simp (config := {decide := true, maxDischargeDepth := 64}) [rangeEvents, entry_guard_inputs_decoded, decodedEvents,
    entryArgumentEvents, List.range_succ, instructionObservation, dataAccesses, Arm64.execInstWithSvc,
    Arm64.execLogicalShift, Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64, Arm64.execMoveWide, Arm64.execLdr,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.State.advancePC, Arm64.State.setPC,
    Arm64.RegFile.write, Arm64.RegFile.read, BitVec.add_assoc, Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2,
    Arm64.Reg.x3, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22,
    scratchRead, countRead, scratch, count]

def guardPairEvents (pc sp target : Addr) : List InstructionObservation :=
  [⟨pc, pc + 4#64, sp, sp, []⟩, ⟨pc + 4#64, target, sp, sp, []⟩]

def entryGuardEvents (pc sp : Addr) (capacity count : Nat) : List InstructionObservation :=
  if capacity < 96 then guardPairEvents pc sp (pc + 0xdc#64) else
    guardPairEvents pc sp (pc + 8#64) ++ guardPairEvents (pc + 8#64) sp
      (if capacity < 96 + count then pc + 0xdc#64 else pc + 16#64)

private theorem guard_first_events {s out : Arm64.State}
    (run : runRange entry 0x38 2 s = some out) :
    rangeEvents entry 0x38 2 s = guardPairEvents s.pc s.sp out.pc ∧ out.sp = s.sp := by
  have decoded : decodeRange entry 0x38 2 = some
    [.addSubImm .W64 .SUBS .x4 .x4 96#12 false, .bCond .CC 216#64] := by decide +kernel
  simp only [runRange, decoded, Option.map_some, Option.some.injEq] at run
  rw [← run]
  simp only [rangeEvents, decoded, Option.getD_some, decodedEvents, runDecoded, instructionObservation, dataAccesses]
  rw [sub_step, branch_step]
  exact ⟨rfl, rfl⟩

private theorem guard_second_events {s out : Arm64.State}
    (run : runRange entry 0x40 2 s = some out) :
    rangeEvents entry 0x40 2 s = guardPairEvents s.pc s.sp out.pc := by
  have decoded : decodeRange entry 0x40 2 = some
    [.addSubShift .W64 .SUBS .xzr .x4 .x5 .LSL 0, .bCond .CC 208#64] := by decide +kernel
  simp only [runRange, decoded, Option.map_some, Option.some.injEq] at run
  rw [← run]
  simp only [rangeEvents, decoded, Option.getD_some, decodedEvents, runDecoded, instructionObservation, dataAccesses]
  rw [cmp_step, branch_step]
  rfl

private theorem guard_fetched (base : Addr) (s out : Arm64.State)
    (pc : s.pc = routineAddress base entry + 0x38#64)
    (loaded : (programAt entry (routineAddress base entry)).CodeLoaded s.mem)
    (running : s.status = .Running) (run : runGuard s = some out) :
    LinkedExecution base s (entryGuardEvents s.pc s.sp (s.readReg64 .x4).toNat (s.readReg64 .x5).toNat) out := by
  obtain ⟨outLive, _, after, first, live, remaining⟩ := runGuard_segments run
  have body : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨front, _⟩ := run_range_observes body pc (by decide) loaded
    (by decide +kernel) first (live.trans running)
  obtain ⟨trace, stack⟩ := guard_first_events first
  obtain ⟨result, canonical, _, _, _, endPC⟩ := runGuard_result s
  have eq := Option.some.inj (canonical.symm.trans run)
  subst result
  rw [trace] at front
  by_cases small : (s.readReg64 .x4).toNat < 96
  · rw [if_pos small] at remaining
    subst out
    have endAddress : after.pc = s.pc + 0xdc#64 := by rw [endPC, if_pos (by omega)]
    rw [entryGuardEvents, if_pos small]
    rw [endAddress] at front
    exact front
  · rw [if_neg small] at remaining
    have next : after.pc = routineAddress base entry + 0x40#64 := by
      rw [remaining.1, pc, BitVec.add_assoc]
      rfl
    obtain ⟨tail, _⟩ := run_range_observes body next (by decide) (front.keeps_code _ loaded)
      (by decide +kernel) remaining.2 (outLive.trans running)
    rw [remaining.1] at front
    rw [guard_second_events remaining.2, remaining.1, stack, endPC] at tail
    rw [entryGuardEvents, if_neg small]
    exact front.append tail

def entryPrefixEvents (base : Addr) (s : Arm64.State) (capacity count : Nat) : List InstructionObservation :=
  frameEnterEvents s.pc s.sp 160#64 ++
  entryArgumentEvents (routineAddress base entry + 0x1c#64) (s.sp - 160#64)
    (s.readReg64 .x2) (s.readReg64 .x1) ++
  entryGuardEvents (routineAddress base entry + 0x38#64) (s.sp - 160#64) capacity count

structure EntryPrefix (base : Addr) (s checked : Arm64.State) (capacity count : Nat) where
  execution : LinkedExecution base s (entryPrefixEvents base s capacity count) checked
  pc : checked.pc = (if capacity < 96 + count then routineAddress base entry + 0x114#64
    else routineAddress base entry + 0x48#64)
  live : checked.status = .Running
  sp : checked.sp = s.sp - 160#64
  memory : checked.mem = frameMem s 160#64
  status : checked.readReg64 .x0 = 1#64
  key : checked.readReg64 .x19 = s.readReg64 .x0
  message : checked.readReg64 .x20 = s.readReg64 .x1
  scratch : checked.readReg64 .x21 = s.readReg64 .x2
  mac : checked.readReg64 .x22 = s.readReg64 .x3
  frame : ∀ p, ¬ (entrySaved s).Contains p → checked.mem.cells p = s.mem.cells p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem entry_prefix (base : Addr) (s : Arm64.State) (keyExtent messageExtent capacity count : Nat)
    (g : EntryResources base s keyExtent messageExtent capacity) (capMin : 8 ≤ capacity)
    (msgMin : 24 ≤ messageExtent) (cap64 : capacity < 2 ^ 64) (count64 : count < 2 ^ 64)
    (capacityAt : s.mem.read64 (s.readReg64 .x2) = BitVec.ofNat 64 capacity)
    (countAt : s.mem.read64 (s.readReg64 .x1 + 16#64) = BitVec.ofNat 64 count)
    (pc : s.pc = routineAddress base entry) (running : s.status = .Running)
    (loaded : (programAt entry (routineAddress base entry)).CodeLoaded s.mem) :
    ∃ checked, Nonempty (EntryPrefix base s checked capacity count) := by
  let work := entryWorkspace s
  let saved := enteredState s 160#64
  let setup := guardInputs saved
  have valid := stackRegion_valid s.sp 800 g.available
  have low : 160 ≤ s.sp.toNat := by have := g.available; omega
  have mask := stack_mask _ (stackRegion_aligned s.sp 160 g.aligned (by decide) low)
  have aligned : s.spAligned = true := by simp [Arm64.State.spAligned, stack_mask _ g.aligned]
  have slot (off : Nat) : work.base + BitVec.ofNat 64 (640 + off) =
      (s.sp - 160#64) + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact congrArg (· + BitVec.ofNat 64 off)
      (congrArg Region.base (stackRegion_slice s.sp 800 640 96 (by decide)))
  have writes (i : Fin 12) : s.mem.canWrite (s.sp - 160#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [← slot]
    exact caller_region_write _ work valid g.stackWrite (640 + 8 * i.val) 8
      (by change _ ≤ 800; have := i.isLt; omega)
  let spill := entrySaved s
  have spillEq : spill = regionSlice work 640 96 := by
    exact (stackRegion_slice s.sp 800 640 96 (by decide)).symm
  have spillValid : spill.Valid := by
    rw [spillEq]
    exact regionSlice_valid work 640 96 valid (by change _ ≤ 800; decide)
  have spillInside (p : Addr) (h : spill.Contains p) : work.Contains p := by
    rw [spillEq] at h
    exact regionSlice_inside work 640 96 valid (by change _ ≤ 800; decide) p h
  have frame (p : Addr) (outside : ¬ spill.Contains p) : saved.mem.cells p = s.mem.cells p :=
    writeWords_outside _ _ _ 12 _ (caller_outside_delta spill spillValid p outside)
  have reg (r : BitVec 5) (other : r ≠ 29#5) : saved.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    by_cases zero : r = 31#5
    · subst r; rfl
    simp only [saved, enteredState, reg_set_pc, reg_write_gpr, Arm64.Reg.x29,
      if_neg zero, if_neg other, reg_write_sp, reg_set_mem, ite_self]
  let scratch := entryScratch s capacity
  let msg := entryMessage s messageExtent
  have inputAt (reg : BitVec 5) (src : Region) (off : Nat)
      (pointer : src.base = s.readReg64 (.gpr reg)) (okay : src.Valid) (fit : off + 8 ≤ src.bytes)
      (apart : work.Disjoint src) :
      saved.mem.read64 (s.readReg64 (.gpr reg) + BitVec.ofNat 64 off) =
        s.mem.read64 (s.readReg64 (.gpr reg) + BitVec.ofNat 64 off) := by
    rw [← pointer]
    apply read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frame _ (fun hit => apart _ ⟨spillInside _ hit,
      caller_region_contains_offset src okay _ (by have := i.isLt; omega)⟩)
  have cap : saved.mem.read64 (saved.readReg64 .x2) = BitVec.ofNat 64 capacity := by
    rw [reg 2#5 (by decide)]
    have m := inputAt 2#5 scratch 0 rfl g.scratchValid capMin g.stackScratch
    change saved.mem.read64 (s.readReg64 .x2 + 0#64) = _ at m
    rw [BitVec.add_zero] at m
    exact m.trans capacityAt
  have countMem : saved.mem.read64 (saved.readReg64 .x1 + 16#64) = BitVec.ofNat 64 count := by
    rw [reg 1#5 (by decide)]
    exact (inputAt 1#5 msg 16 rfl g.messageValid msgMin g.stackMessage).trans countAt
  have body : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨pro, _⟩ := run_range_observes body (by simpa only [BitVec.add_zero] using pc)
    (by decide) loaded (by decide +kernel) (enter_entry s aligned mask writes)
    (show saved.status = .Running from running)
  have readCap : saved.mem.canRead (saved.readReg64 .x2) 8 = true := by
    rw [reg 2#5 (by decide)]
    apply pro.grants.read
    simpa only [BitVec.add_zero] using caller_region_read _ scratch g.scratchValid g.scratchRead 0 8 capMin
  have readCount : saved.mem.canRead (saved.readReg64 .x1 + 16#64) 8 = true := by
    rw [reg 1#5 (by decide)]
    exact pro.grants.read _ _ (caller_region_read _ msg g.messageValid g.messageRead 16 8 msgMin)
  have savedPC : saved.pc = routineAddress base entry + 0x1c#64 := by
    change s.pc + 28#64 = _
    rw [pc]
  obtain ⟨args, _⟩ := run_range_observes body savedPC (by decide) (pro.keeps_code _ loaded)
    (by decide +kernel) (entry_guard_inputs saved readCap readCount)
    (show setup.status = .Running from running)
  have front := pro.append args
  have setupPC : setup.pc = routineAddress base entry + 0x38#64 := by
    change saved.pc + 28#64 = _
    rw [savedPC, BitVec.add_assoc]
    rfl
  have gotCap : setup.readReg64 .x4 = BitVec.ofNat 64 capacity := by
    simpa (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x4, Arm64.Reg.x5, if_false, if_true] using cap
  have gotCount : setup.readReg64 .x5 = BitVec.ofNat 64 count := by
    simpa (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x5, if_false, if_true] using countMem
  obtain ⟨out, guard, mem, sp, _, endPC⟩ := runGuard_result setup
  obtain ⟨outLive, outRegs, _⟩ := runGuard_segments guard
  have checked := guard_fetched base setup out setupPC (front.keeps_code _ loaded)
    (show setup.status = .Running from running) guard
  have next : out.pc = (if capacity < 96 + count then routineAddress base entry + 0x114#64
    else routineAddress base entry + 0x48#64) := by
    rw [endPC, gotCap, gotCount, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt cap64, Nat.mod_eq_of_lt count64, setupPC]
    split <;> rw [BitVec.add_assoc] <;> rfl
  have enterEvents : rangeEvents entry 0 7 s = frameEnterEvents s.pc s.sp 160#64 := by
    simpa only [rangeEvents, entry_enter_decoded, Option.getD_some] using
      save_code_events s 160#64 aligned mask writes
  have savedSP : saved.sp = s.sp - 160#64 := rfl
  have argEvents := entry_argument_events saved readCap readCount
  rw [savedPC, savedSP, reg 2#5 (by decide), reg 1#5 (by decide)] at argEvents
  have setupSP : setup.sp = s.sp - 160#64 := rfl
  rw [enterEvents] at pro
  rw [argEvents] at args
  rw [setupPC, setupSP, gotCap, gotCount, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt cap64, Nat.mod_eq_of_lt count64] at checked
  refine ⟨out, ⟨⟨(pro.append args).append checked, next, outLive.trans running, sp, mem,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [outRegs 0#5 (by decide)]
    simp (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5, if_false, if_true]
  · rw [outRegs 19#5 (by decide)]
    simp (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x19, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22,
      if_false, if_true]
    exact reg 0#5 (by decide)
  · rw [outRegs 20#5 (by decide)]
    simp (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, if_false, if_true]
    exact reg 1#5 (by decide)
  · rw [outRegs 21#5 (by decide)]
    simp (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x21, Arm64.Reg.x22, if_false, if_true]
    exact reg 2#5 (by decide)
  · rw [outRegs 22#5 (by decide)]
    simp (config := {decide := true}) only [setup, guardInputs, reg_set_pc, reg_write_gpr,
      Arm64.Reg.x0, Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x22, if_false, if_true]
    exact reg 3#5 (by decide)
  · intro p off
    rw [mem]
    exact frame p off

end Crypto.HMACSHA256.ARM64
