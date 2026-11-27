import Proofs.HMACSHA256.ARM64Ranges
import Proofs.ARM64.ImportedTailCopy

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

def copyCount (message : Bool) : Arm64.Reg := if message then .x5 else .x2
def copySource (message : Bool) : Arm64.Reg := if message then .x6 else .x3
def copyDestination (message : Bool) : Arm64.Reg := if message then .x8 else .x1

def copyRoutine (message : Bool) : Routine := if message then entry else key
private def wordOffset (message : Bool) : Nat := if message then 0xd4 else 0x40
private def byteOffset (message : Bool) : Nat := if message then 0xec else 0x58

private def wordCheck (message : Bool) : List Arm64.Instr :=
  [.addSubImm .W64 .SUBS .xzr (copyCount message) 8#12 false, .bCond .CC 20#64]

private def byteCheck (message : Bool) : List Arm64.Instr :=
  [.cbz .W64 false (copyCount message) 20#64]

private def copyBody (message wide : Bool) : List Arm64.Instr :=
  let size := if wide then Arm64.MemWidth.X64 else .B8
  let w := if wide then Arm64.RegWidth.W64 else .W32
  let n := if wide then 8 else 1
  [.ldr w size false .x9 (.PostIndex (copySource message) n),
   .str size .x9 (.PostIndex (copyDestination message) n),
   .addSubImm .W64 .SUB (copyCount message) (copyCount message) (if wide then 8 else 1) false,
   .b (if wide then -20 else -16)]

private theorem word_chunks (message : Bool) :
    decodeRange (copyRoutine message) (wordOffset message) 2 = some (wordCheck message) ∧
    decodeRange (copyRoutine message) (wordOffset message + 8) 4 = some (copyBody message true) := by
  cases message <;> decide +kernel

private theorem byte_chunks (message : Bool) :
    decodeRange (copyRoutine message) (byteOffset message) 1 = some (byteCheck message) ∧
    decodeRange (copyRoutine message) (byteOffset message + 4) 4 = some (copyBody message false) := by
  cases message <;> decide +kernel

def runCopyCycle (message wide : Bool) (s : Arm64.State) : Option Arm64.State := do
  let offset := if wide then wordOffset message else byteOffset message
  let count := if wide then 2 else 1
  let checked ← runRange (copyRoutine message) offset count s
  if checked.pc = s.pc + BitVec.ofNat 64 (4 * count) then
    runRange (copyRoutine message) (offset + 4 * count) 4 checked
  else
    return checked

private theorem cmp8_carry (x : Addr) :
    (Arm64.AddWithCarry64 x 0xfffffffffffffff7#64 true).2.c = decide (8 ≤ x.toNat) :=
  carry64_sub_ge x 8#64

theorem word_branch (message : Bool) (s : Arm64.State) :
    runDecoded (wordCheck message) s =
      let ps := (Arm64.AddWithCarry64 (s.readReg64 (copyCount message)) (~~~8#64) true).2
      (s.setPState ps).setPC (if (s.readReg64 (copyCount message)).toNat < 8 then
        s.pc + 24#64 else s.pc + 8#64) := by
  by_cases small : (s.readReg64 (copyCount message)).toNat < 8
  · have noCarry := Nat.not_le.mpr small
    simp (config := { decide := true }) [wordCheck, runDecoded, Arm64.execInstWithSvc,
      Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
      Arm64.ConditionHolds, cmp8_carry, small, noCarry, Arm64.State.setPState,
      Arm64.State.setPC, Arm64.State.advancePC, BitVec.add_assoc]
  · have carry := Nat.le_of_not_gt small
    simp (config := { decide := true }) [wordCheck, runDecoded, Arm64.execInstWithSvc,
      Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
      Arm64.ConditionHolds, cmp8_carry, small, carry, Arm64.State.setPState,
      Arm64.State.setPC, Arm64.State.advancePC, BitVec.add_assoc]

theorem byte_branch (message : Bool) (s : Arm64.State) :
    runDecoded (byteCheck message) s = s.setPC
      (if s.readReg64 (copyCount message) = 0#64 then s.pc + 20#64 else s.pc + 4#64) := by
  by_cases empty : s.readReg64 (copyCount message) = 0#64 <;>
    simp (config := { decide := true }) [byteCheck, runDecoded, Arm64.execInstWithSvc,
      Arm64.State.readReg, Arm64.State.setPC, Arm64.State.advancePC, empty]

def copyBodyState (message wide : Bool) (s : Arm64.State) : Arm64.State :=
  let width := if wide then Arm64.MemWidth.X64 else .B8
  let distance := BitVec.ofNat 64 width.bytes
  let src := s.readReg64 (copySource message)
  let dst := s.readReg64 (copyDestination message)
  let v := s.mem.readSized width false src
  let st := s.setMem (s.mem.writeSized width dst v)
  let st := st.writeReg64 .x9 v
  let st := st.writeReg64 (copySource message) (src + distance)
  let st := st.writeReg64 (copyDestination message) (dst + distance)
  let st := st.writeReg64 (copyCount message) (s.readReg64 (copyCount message) - distance)
  st.setPC (if wide then s.pc - 8#64 else s.pc - 4#64)

private theorem subtract1 (x : Addr) :
    (Arm64.AddWithCarry64 x 0xfffffffffffffffe#64 true).1 = x + 0xffffffffffffffff#64 := by
  have effect := addWithCarry64_sub x 1#64
  rw [BitVec.sub_eq_add_neg] at effect
  exact effect

private theorem subtract8 (x : Addr) :
    (Arm64.AddWithCarry64 x 0xfffffffffffffff7#64 true).1 = x + 0xfffffffffffffff8#64 := by
  have effect := addWithCarry64_sub x 8#64
  rw [BitVec.sub_eq_add_neg] at effect
  exact effect

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
theorem copy_body (message wide : Bool) (s : Arm64.State)
    (read : s.mem.canRead (s.readReg64 (copySource message)) (if wide then 8 else 1) = true)
    (write : s.mem.canWrite (s.readReg64 (copyDestination message)) (if wide then 8 else 1) = true) :
    runDecoded (copyBody message wide) s = copyBodyState message wide s := by
  cases message <;> cases wide <;>
    simp only [copySource, copyDestination, Bool.false_eq_true, if_false, if_true,
      Arm64.Reg.x1, Arm64.Reg.x3, Arm64.Reg.x6, Arm64.Reg.x8] at read write
  all_goals
    simp (config := { decide := true }) [copyBody, copyBodyState, runDecoded, Arm64.execInstWithSvc,
      Arm64.execLdr, Arm64.execStr, Arm64.execAddSubImm, Arm64.evalAddSub,
      Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.writeReg32,
      Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
      Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized, addWithCarry64_sub,
      Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3, Arm64.Reg.x5, Arm64.Reg.x6, Arm64.Reg.x8,
      Arm64.Reg.x9, copyCount, copySource, copyDestination, read, write, BitVec.add_assoc,
      BitVec.sub_eq_add_neg, BitVec.truncate_eq_setWidth]
  all_goals simp (config := { decide := true }) [Arm64.State.writeReg64, Arm64.State.setPC,
    Arm64.State.advancePC, Arm64.State.setMem, Arm64.RegFile.write, Arm64.RegFile.read,
    BitVec.add_assoc, subtract1, subtract8]
  all_goals
    funext i
    by_cases h1 : i = 1#5 <;> by_cases h2 : i = 2#5 <;> by_cases h3 : i = 3#5 <;>
      by_cases h6 : i = 6#5 <;> by_cases h8 : i = 8#5 <;> by_cases h9 : i = 9#5 <;>
      simp_all

/-- Execute the taken fragment of either copy loop, with no data accesses
on the zero-count byte path. -/
theorem copy_cycle (message wide : Bool) (s : Arm64.State)
    (read : s.mem.canRead (s.readReg64 (copySource message)) (if wide then 8 else 1) = true)
    (write : s.mem.canWrite (s.readReg64 (copyDestination message)) (if wide then 8 else 1) = true) :
    runCopyCycle message wide s =
      let checked := runDecoded (if wide then wordCheck message else byteCheck message) s
      if checked.pc = s.pc + (if wide then 8#64 else 4#64) then
        some (copyBodyState message wide checked)
      else some checked := by
  cases wide
  · obtain ⟨head, tail⟩ := byte_chunks message
    have body := copy_body message false (runDecoded (byteCheck message) s)
      (by rw [byte_branch]; exact read)
      (by rw [byte_branch]; exact write)
    simp only [runCopyCycle, Bool.false_eq_true, if_false, runRange, head, tail, Option.map_some]
    let checked := runDecoded (byteCheck message) s
    change (if checked.pc = s.pc + 4#64 then some (runDecoded (copyBody message false) checked)
      else some checked) = _
    rw [body]
  · obtain ⟨head, tail⟩ := word_chunks message
    have body := copy_body message true (runDecoded (wordCheck message) s)
      (by rw [word_branch]; exact read)
      (by rw [word_branch]; exact write)
    simp only [runCopyCycle, if_true, runRange, head, tail, Option.map_some]
    let checked := runDecoded (wordCheck message) s
    change (if checked.pc = s.pc + 8#64 then some (runDecoded (copyBody message true) checked)
      else some checked) = _
    rw [body]


/-- The word loop exits without a data access once fewer than eight bytes
remain. Its returned state enters the byte loop with the public flags set. -/
theorem word_copy_exits (message : Bool) (s : Arm64.State)
    (short : (s.readReg64 (copyCount message)).toNat < 8) :
    runCopyCycle message true s = some
      (Arm64.State.setPC
        (s.setPState (Arm64.AddWithCarry64 (s.readReg64 (copyCount message)) (~~~8#64) true).2)
        (s.pc + 24#64)) := by
  obtain ⟨head, _⟩ := word_chunks message
  have different : s.pc + 24#64 ≠ s.pc + 8#64 := by
    intro eq
    have same := congrArg (fun p : Addr => p - s.pc) eq
    change s.pc + 24#64 - s.pc = s.pc + 8#64 - s.pc at same
    rw [address_delta, address_delta] at same
    contradiction
  simp only [runCopyCycle, if_true, runRange, head, Option.map_some, pure, bind, Option.bind_some]
  rw [word_branch, if_pos short]
  simp [different, Arm64.State.setPC]

/-- The byte loop exits without loading or storing when all bytes have
already been copied. The end state is valid even at the end of a mapping. -/
theorem byte_copy_exits (message : Bool) (s : Arm64.State)
    (empty : s.readReg64 (copyCount message) = 0#64) :
    runCopyCycle message false s = some (s.setPC (s.pc + 20#64)) := by
  obtain ⟨head, _⟩ := byte_chunks message
  have different : s.pc + 20#64 ≠ s.pc + 4#64 := by
    intro eq
    have same := congrArg (fun p : Addr => p - s.pc) eq
    change s.pc + 20#64 - s.pc = s.pc + 4#64 - s.pc at same
    rw [address_delta, address_delta] at same
    contradiction
  simp only [runCopyCycle, Bool.false_eq_true, if_false, runRange, head, Option.map_some, pure, bind, Option.bind_some]
  rw [byte_branch, if_pos empty]
  simp [different, Arm64.State.setPC]

def copyWidth (wide : Bool) : Arm64.MemWidth := if wide then .X64 else .B8

structure CopyStepResult (message wide : Bool) (before out : Arm64.State) : Prop where
  pc : out.pc = before.pc
  count : out.readReg64 (copyCount message) =
    before.readReg64 (copyCount message) - BitVec.ofNat 64 (copyWidth wide).bytes
  source : out.readReg64 (copySource message) =
    before.readReg64 (copySource message) + BitVec.ofNat 64 (copyWidth wide).bytes
  dest : out.readReg64 (copyDestination message) =
    before.readReg64 (copyDestination message) + BitVec.ofNat 64 (copyWidth wide).bytes
  memory : out.mem = before.mem.writeSized (copyWidth wide)
    (before.readReg64 (copyDestination message))
    (before.mem.readSized (copyWidth wide) false (before.readReg64 (copySource message)))
  nonvolatile : nonvolatile out = nonvolatile before
  nonMemory : nonMemory out = nonMemory before

private theorem saved_register_diff (i : Fin 13) (n : BitVec 5)
    (other : n.toNat < 18 ∨ n = 31#5) : BitVec.ofNat 5 (18 + i.val) ≠ n := by
  intro eq
  have below := i.isLt
  have address := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 18 + i.val < 2 ^ 5)] at address
  rcases other with low | last
  · omega
  · rw [last] at address
    change 18 + i.val = 31 at address
    omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
/-- One taken loop iteration performs one checked read and store, advances
the two pointers by the width, decrements the count and jumps back. -/
theorem copy_cycle_taken (message wide : Bool) (s : Arm64.State)
    (enough : (copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat)
    (read : s.mem.canRead (s.readReg64 (copySource message)) (copyWidth wide).bytes = true)
    (write : s.mem.canWrite (s.readReg64 (copyDestination message)) (copyWidth wide).bytes = true) :
    ∃ out, runCopyCycle message wide s = some out ∧ CopyStepResult message wide s out := by
  have execution := copy_cycle message wide s
    (by cases wide <;> exact read) (by cases wide <;> exact write)
  cases wide
  · have more : s.readReg64 (copyCount message) ≠ 0#64 := by
      intro zero
      rw [zero] at enough
      change 1 ≤ 0 at enough
      omega
    simp only [Bool.false_eq_true, if_false] at execution
    rw [byte_branch, if_neg more] at execution
    simp only [Arm64.State.setPC, if_true] at execution
    refine ⟨_, execution, ?_⟩
    cases message <;> constructor <;>
      simp (config := { decide := true }) [copyBodyState, copyCount, copySource, copyDestination,
        copyWidth, Arm64.MemWidth.bytes, Arm64.State.setPC, BitVec.add_sub_cancel,
        Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3, Arm64.Reg.x5,
        Arm64.Reg.x6, Arm64.Reg.x8, Arm64.Reg.x9, Arm64.State.readReg64,
        Arm64.State.writeReg64, Arm64.State.setMem, Arm64.RegFile.write, Arm64.RegFile.read]
    all_goals first | rfl | (
      funext i
      simp (config := { decide := true }) [nonvolatile, Arm64.State.readReg64, Arm64.RegFile.read,
        saved_register_diff])
  · have enough8 : ¬ (s.readReg64 (copyCount message)).toNat < 8 := Nat.not_lt.mpr enough
    simp only [if_pos (show (true : Bool) = true from rfl), if_true] at execution
    rw [word_branch, if_neg enough8] at execution
    simp only [Arm64.State.setPC, Arm64.State.setPState, if_true] at execution
    refine ⟨_, execution, ?_⟩
    cases message <;> constructor <;>
      simp (config := { decide := true }) [copyBodyState, copyCount, copySource, copyDestination,
        copyWidth, Arm64.MemWidth.bytes, Arm64.State.setPC, BitVec.add_sub_cancel,
        Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3, Arm64.Reg.x5,
        Arm64.Reg.x6, Arm64.Reg.x8, Arm64.Reg.x9, Arm64.State.readReg64,
        Arm64.State.writeReg64, Arm64.State.setMem, Arm64.RegFile.write, Arm64.RegFile.read]
    all_goals first | rfl | (
      funext i
      simp (config := { decide := true }) [nonvolatile, Arm64.State.readReg64, Arm64.RegFile.read,
        saved_register_diff])

def copyOffset (message wide : Bool) : Nat := if wide then wordOffset message else byteOffset message
def copyGuardCount (wide : Bool) : Nat := if wide then 2 else 1

private def copyGuardCode (message wide : Bool) : List Arm64.Instr :=
  if wide then wordCheck message else byteCheck message

private theorem copy_guard_decode (message wide : Bool) :
    decodeRange (copyRoutine message) (copyOffset message wide) (copyGuardCount wide) =
      some (copyGuardCode message wide) := by
  cases wide
  · exact (byte_chunks message).1
  · exact (word_chunks message).1

private theorem copy_guard_supported (message wide : Bool) :
    rangeSupported (copyRoutine message) (copyOffset message wide) (copyGuardCount wide) = true := by
  cases message <;> cases wide <;> decide +kernel

private theorem copy_body_supported (message wide : Bool) :
    rangeSupported (copyRoutine message) (copyOffset message wide + 4 * copyGuardCount wide) 4 = true := by
  cases message <;> cases wide <;> decide +kernel

private theorem copy_guard_fits (message wide : Bool) :
    copyOffset message wide + 4 * copyGuardCount wide ≤ 2 ^ 64 := by
  cases message <;> cases wide <;> decide +kernel

private theorem copy_body_fits (message wide : Bool) :
    (copyOffset message wide + 4 * copyGuardCount wide) + 4 * 4 ≤ 2 ^ 64 := by
  cases message <;> cases wide <;> decide +kernel

def copyGuardEvents (wide take : Bool) (pc sp : Addr) : List InstructionObservation :=
  if wide then
    [⟨pc, pc + 4#64, sp, sp, []⟩, ⟨pc + 4#64, pc + (if take then 8#64 else 24#64), sp, sp, []⟩]
  else [⟨pc, pc + (if take then 4#64 else 20#64), sp, sp, []⟩]

def copyBodyEvents (wide : Bool) (pc sp src dst : Addr) : List InstructionObservation :=
  let width := (copyWidth wide).bytes
  [⟨pc, pc + 4#64, sp, sp, [⟨false, src, width⟩]⟩,
   ⟨pc + 4#64, pc + 8#64, sp, sp, [⟨true, dst, width⟩]⟩,
   ⟨pc + 8#64, pc + 12#64, sp, sp, []⟩,
   ⟨pc + 12#64, pc - (if wide then 8#64 else 4#64), sp, sp, []⟩]

def copyCycleEvents (wide take : Bool) (pc sp src dst : Addr) : List InstructionObservation :=
  copyGuardEvents wide take pc sp ++
    if take then copyBodyEvents wide (pc + (if wide then 8#64 else 4#64)) sp src dst else []

set_option maxHeartbeats 900000 in
private theorem copy_guard_events (message wide : Bool) (s : Arm64.State) :
    decodedEvents (copyGuardCode message wide) s =
      copyGuardEvents wide (decide ((copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat)) s.pc s.sp := by
  cases wide
  · by_cases zero : s.readReg64 (copyCount message) = 0#64
    · simp [copyGuardCode, copyGuardEvents, copyWidth, byteCheck, decodedEvents, instructionObservation,
        dataAccesses, Arm64.execInstWithSvc, Arm64.State.readReg, zero]
    · have positive : 1 ≤ (s.readReg64 (copyCount message)).toNat := by
        have nonzero : (s.readReg64 (copyCount message)).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        omega
      simp [copyGuardCode, copyGuardEvents, copyWidth, byteCheck, decodedEvents, instructionObservation,
        dataAccesses, Arm64.execInstWithSvc, Arm64.State.readReg, zero, positive, Arm64.MemWidth.bytes]
  · by_cases enough : 8 ≤ (s.readReg64 (copyCount message)).toNat <;>
      simp [copyGuardCode, copyGuardEvents, copyWidth, wordCheck, decodedEvents, instructionObservation,
        dataAccesses, Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.ConditionHolds,
        Arm64.State.readReg, Arm64.State.writeReg, cmp8_carry, enough, Arm64.MemWidth.bytes, BitVec.add_assoc, Arm64.State.setPState]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
set_option linter.unusedSimpArgs false in
private theorem copy_body_events (message wide : Bool) (s : Arm64.State)
    (read : s.mem.canRead (s.readReg64 (copySource message)) (copyWidth wide).bytes = true)
    (write : s.mem.canWrite (s.readReg64 (copyDestination message)) (copyWidth wide).bytes = true) :
    decodedEvents (copyBody message wide) s =
      copyBodyEvents wide s.pc s.sp (s.readReg64 (copySource message)) (s.readReg64 (copyDestination message)) := by
  cases message <;> cases wide <;>
    simp (config := {decide := true}) only [copySource, copyDestination, copyWidth, Bool.false_eq_true, if_false, if_true,
      Arm64.Reg.x1, Arm64.Reg.x3, Arm64.Reg.x6, Arm64.Reg.x8, Arm64.MemWidth.bytes, Arm64.State.readReg64,
      Arm64.RegFile.read] at read write
  all_goals
    simp (config := { decide := true }) [copyBody, copyBodyEvents, decodedEvents, instructionObservation,
      dataAccesses, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr, Arm64.execAddSubImm,
      Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.writeReg32,
      Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
      Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized, Arm64.Reg.x1, Arm64.Reg.x2,
      Arm64.Reg.x3, Arm64.Reg.x5, Arm64.Reg.x6, Arm64.Reg.x8, Arm64.Reg.x9, copyCount, copySource,
      copyDestination, copyWidth, read, write, Arm64.State.writeReg64, Arm64.State.setPC, Arm64.State.readReg64,
      Arm64.State.advancePC, Arm64.State.setMem, Arm64.RegFile.write, Arm64.RegFile.read,
      BitVec.add_assoc, BitVec.sub_eq_add_neg]

/-- Bind one copy-loop cycle to the linked instruction fetches. The real
guard determines whether the next four instructions execute, so the exit
checks do not fetch or access the body. -/
theorem copy_cycle_fetched (message wide : Bool) (base : Addr) (s out : Arm64.State)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message wide))
    (loaded : (programAt (copyRoutine message) (routineAddress base (copyRoutine message))).CodeLoaded s.mem)
    (run : runCopyCycle message wide s = some out) (alive : out.status = .Running)
    (grants : (copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat →
      s.mem.canRead (s.readReg64 (copySource message)) (copyWidth wide).bytes = true ∧
      s.mem.canWrite (s.readReg64 (copyDestination message)) (copyWidth wide).bytes = true) :
    let take := decide ((copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat)
    let events := copyCycleEvents wide take s.pc s.sp (s.readReg64 (copySource message)) (s.readReg64 (copyDestination message))
    LinkedExecution base s events out ∧ events.length =
      copyGuardCount wide + (if (copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat then 4 else 0) := by
  let r := copyRoutine message
  let off := copyOffset message wide
  let n := copyGuardCount wide
  let checked := runDecoded (copyGuardCode message wide) s
  have guardRun : runRange r off n s = some checked := by
    simp only [runRange, r, off, n, copy_guard_decode, Option.map_some, checked]
  have decision :
      checked.pc = s.pc + BitVec.ofNat 64 (4 * n) ↔
        (copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat := by
    cases wide
    · change (runDecoded (byteCheck message) s).pc = s.pc + 4#64 ↔
        1 ≤ (s.readReg64 (copyCount message)).toNat
      rw [byte_branch]
      by_cases zero : s.readReg64 (copyCount message) = 0#64
      · rw [if_pos zero, zero]
        change (s.pc + 20#64 = s.pc + 4#64) ↔ 1 ≤ 0
        rw [BitVec.add_right_inj]
        decide
      · rw [if_neg zero]
        have nonzero : (s.readReg64 (copyCount message)).toNat ≠ 0 := by
          intro h
          apply zero
          exact BitVec.eq_of_toNat_eq h
        change (s.pc + 4#64 = s.pc + 4#64) ↔ 1 ≤ (s.readReg64 (copyCount message)).toNat
        exact ⟨fun _ => Nat.pos_of_ne_zero nonzero, fun _ => rfl⟩
    · change (runDecoded (wordCheck message) s).pc = s.pc + 8#64 ↔
        8 ≤ (s.readReg64 (copyCount message)).toNat
      rw [word_branch]
      by_cases small : (s.readReg64 (copyCount message)).toNat < 8
      · rw [if_pos small]
        change (s.pc + 24#64 = s.pc + 8#64) ↔ _
        rw [BitVec.add_right_inj]
        have unequal : (24#64 : Addr) ≠ 8#64 := by decide
        exact ⟨fun h => (unequal h).elim, fun h => (Nat.not_le_of_gt small h).elim⟩
      · rw [if_neg small]
        change (s.pc + 8#64 = s.pc + 8#64) ↔ 8 ≤ (s.readReg64 (copyCount message)).toNat
        exact ⟨fun _ => Nat.le_of_not_gt small, fun _ => rfl⟩
  have linked : r = entry ∨ r = key ∨ r = finish := by
    cases message
    · exact .inr (.inl rfl)
    · exact .inl rfl
  have choice :
      (if checked.pc = s.pc + BitVec.ofNat 64 (4 * n) then runRange r (off + 4 * n) 4 checked
        else some checked) = some out := by
    change (do
      let guard ← runRange r off n s
      if guard.pc = s.pc + BitVec.ofNat 64 (4 * n) then runRange r (off + 4 * n) 4 guard
      else return guard) = some out at run
    rw [guardRun] at run
    exact run
  have guardEvents : rangeEvents r off n s =
      copyGuardEvents wide (decide ((copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat)) s.pc s.sp := by
    simpa only [rangeEvents, r, off, n, copy_guard_decode, Option.getD_some] using copy_guard_events message wide s
  dsimp only
  by_cases enough : (copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat
  · have fallThrough := decision.mpr enough
    rw [if_pos fallThrough] at choice
    have intermediate := run_range_running_before (copy_body_supported message wide) choice alive
    obtain ⟨guard, nf⟩ := run_range_observes linked pc (copy_guard_fits message wide) loaded
      (copy_guard_supported message wide) guardRun intermediate
    have pos : checked.pc = routineAddress base r + BitVec.ofNat 64 (off + 4 * n) := by
      rw [fallThrough, pc, BitVec.ofNat_add, BitVec.add_assoc]
    obtain ⟨body, nb⟩ := run_range_observes linked pos (copy_body_fits message wide)
      (guard.keeps_code _ loaded) (copy_body_supported message wide) choice alive
    have kept : checked.sp = s.sp ∧ checked.mem = s.mem ∧
        checked.readReg64 (copySource message) = s.readReg64 (copySource message) ∧
        checked.readReg64 (copyDestination message) = s.readReg64 (copyDestination message) := by
      cases wide <;> cases message <;>
        simp [checked, copyGuardCode, byte_branch, word_branch, Arm64.State.setPC, Arm64.State.setPState,
          copySource, copyDestination, Arm64.State.readReg64]
    have delta : BitVec.ofNat 64 (4 * n) = (if wide then 8#64 else 4#64) := by cases wide <;> rfl
    have bodyEvents : rangeEvents r (off + 4 * n) 4 checked =
        copyBodyEvents wide (s.pc + (if wide then 8#64 else 4#64)) s.sp
          (s.readReg64 (copySource message)) (s.readReg64 (copyDestination message)) := by
      have d : decodeRange r (off + 4 * n) 4 = some (copyBody message wide) := by
        cases wide
        · exact (byte_chunks message).2
        · exact (word_chunks message).2
      have observed := copy_body_events message wide checked
        (by rw [kept.2.1, kept.2.2.1]; exact (grants enough).1)
        (by rw [kept.2.1, kept.2.2.2]; exact (grants enough).2)
      rw [fallThrough, delta, kept.1, kept.2.2.1, kept.2.2.2] at observed
      simpa only [rangeEvents, d, Option.getD_some] using observed
    have taken : decide ((copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat) = true := by simp [enough]
    rw [guardEvents, taken] at guard nf
    rw [bodyEvents] at body nb
    refine ⟨?_, ?_⟩
    · simpa only [copyCycleEvents, if_pos enough, taken, if_true] using guard.append body
    · simp only [copyCycleEvents, if_pos enough, taken, if_true, List.length_append, nf, nb]
  have exits : checked.pc ≠ s.pc + BitVec.ofNat 64 (4 * n) := fun h => enough (decision.mp h)
  rw [if_neg exits] at choice
  have eq := Option.some.inj choice
  obtain ⟨guard, steps⟩ := run_range_observes linked pc (copy_guard_fits message wide) loaded
    (copy_guard_supported message wide) guardRun (eq.symm ▸ alive)
  have taken : decide ((copyWidth wide).bytes ≤ (s.readReg64 (copyCount message)).toNat) = false := by simp [enough]
  rw [guardEvents, taken] at guard steps
  refine ⟨?_, ?_⟩
  · simpa only [copyCycleEvents, taken, Bool.false_eq_true, if_false, List.append_nil]
      using (show LinkedExecution base s (copyGuardEvents wide false s.pc s.sp) out from eq ▸ guard)
  · simp only [copyCycleEvents, if_neg enough, taken, Bool.false_eq_true, if_false, List.append_nil,
      steps, Nat.add_zero]

end Crypto.HMACSHA256.ARM64
