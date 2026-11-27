import Proofs.HMACSHA256.ARM64FinishResources
import Proofs.HMACSHA256.ARM64Key
import Proofs.HMACSHA256.ARM64FrameTrace

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference
open Crypto.Baseline (Region)

def keyInput (s : Arm64.State) (extent : Nat) : Region := ⟨s.readReg64 .x0, extent⟩
def keyOutput (s : Arm64.State) : Region := ⟨s.readReg64 .x1, 64⟩
def keyWorkspace (s : Arm64.State) : Region := stackRegion s.sp 512

/-- The long key path uses the lower 416 bytes for SHA-256 and keeps
the helper's saved registers in the upper 96 bytes. -/
structure KeyResources (base : Addr) (s : Arm64.State) (extent : Nat) : Prop where
  available : 512 ≤ s.sp.toNat
  aligned : s.sp.toNat % 16 = 0
  inputAligned : (s.readReg64 .x0).toNat % 8 = 0
  outputAligned : (s.readReg64 .x1).toNat % 8 = 0
  inputValid : (keyInput s extent).Valid
  outputValid : (keyOutput s).Valid
  imageValid : (callerImage (shaAddress base)).Valid
  stackInput : (keyWorkspace s).Disjoint (keyInput s extent)
  stackOutput : (keyWorkspace s).Disjoint (keyOutput s)
  stackImage : (keyWorkspace s).Disjoint (callerImage (shaAddress base))
  outputInput : (keyOutput s).Disjoint (keyInput s extent)
  outputImage : (keyOutput s).Disjoint (callerImage (shaAddress base))
  inputRead : ∀ p, (keyInput s extent).Contains p → s.mem.canRead p 1 = true
  outputWrite : ∀ p, (keyOutput s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (keyWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (keyWorkspace s).Contains p → s.mem.canWrite p 1 = true

def keyZeroEvents (base sp output : Addr) : List InstructionObservation :=
  (List.range 4).map fun i =>
    let pc := routineAddress base key + BitVec.ofNat 64 (0x1c + 4 * i)
    let dst := output + BitVec.ofNat 64 (16 * i)
    ⟨pc, pc + 4#64, sp, sp, [⟨true, dst, 8⟩, ⟨true, dst + 8#64, 8⟩]⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem key_zero_events (base : Addr) (s : Arm64.State) (pc : s.pc = routineAddress base key + 0x1c#64)
    (canWrite : ∀ i : Fin 8, s.mem.canWrite
      (s.readReg64 .x1 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    rangeEvents key 0x1c 4 s = keyZeroEvents base s.sp (s.readReg64 .x1) := by
  have w (i : Nat) (hi : i < 8) :
      s.mem.canWrite (s.regs.regs 1#5 + BitVec.ofNat 64 (8 * i)) 8 = true := canWrite ⟨i,hi⟩
  have w0 : s.mem.canWrite (s.regs.regs 1#5) 8 = true := by simpa using w 0 (by decide)
  simp (config := {decide := true, maxDischargeDepth := 64}) [rangeEvents, key_zero_decoded, keyZeroEvents,
    List.range_succ, decodedEvents, instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.execStp,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
    Arm64.MemWidth.bytes, Arm64.Memory.writeSized, Arm64.State.readReg64, Arm64.RegFile.read, Arm64.Reg.x1,
    Arm64.State.setMem, Arm64.State.advancePC, Arm64.State.setPC, pc, BitVec.add_assoc,
    w0, w 1 (by decide), w 2 (by decide), w 3 (by decide), w 4 (by decide),
    w 5 (by decide), w 6 (by decide), w 7 (by decide)]

def keyInvokeEvents (base sp : Addr) : List InstructionObservation :=
  [⟨routineAddress base key + 0x70#64, shaAddress base, sp, sp, []⟩]

private theorem key_invoke_events (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base key + 0x70#64) :
    rangeEvents key 0x70 1 s = keyInvokeEvents base s.sp := by
  have decoded : decodeRange key 0x70 1 = some [.bl (-3520#64)] := by decide +kernel
  have target := key_call_target base s pc
  change s.pc - 3520#64 = _ at target
  rw [BitVec.sub_eq_add_neg] at target
  simp only [rangeEvents, decoded, Option.getD_some, decodedEvents, instructionObservation,
    dataAccesses, keyInvokeEvents, Arm64.execInstWithSvc]
  change ([⟨s.pc, s.pc + (-3520#64), s.sp, s.sp, []⟩] : List InstructionObservation) = _
  rw [target, pc]

/-- A key path either uses the fixed copy trace or contains an actual SHA
call whose public ABI values are tied to the incoming helper arguments. -/
inductive KeyBodyTrace (base sp input output : Addr) (message : ByteList) :
    List InstructionObservation → Prop where
  | short (small : message.bytes.size ≤ 64) :
      KeyBodyTrace base sp input output message (keyShortEvents base sp input output message)
  | long {callee out : Arm64.State} {events : List InstructionObservation}
      (large : 64 < message.bytes.size)
      (run : ShaCallResult (shaAddress base) callee out message events)
      (source : callee.readReg64 .x0 = input)
      (dest : callee.readReg64 .x1 = output)
      (stack : callee.sp = sp)
      (link : callee.readReg64 .lr = routineAddress base key + 0x74#64) :
      KeyBodyTrace base sp input output message
        (keyTestEvents base sp input true ++ keyInvokeEvents base sp ++ events)

def KeyWholeTrace (base : Addr) (s : Arm64.State) (input : ByteList) (events : List InstructionObservation) : Prop :=
  ∃ body, KeyBodyTrace base (s.sp - 96#64) (s.readReg64 .x0) (s.readReg64 .x1) input body ∧
    events = frameEnterEvents s.pc s.sp 96#64 ++ keyZeroEvents base (s.sp - 96#64) (s.readReg64 .x1) ++ body ++
      frameReturnEvents (routineAddress base key + 0x74#64) (s.sp - 96#64) 96#64 (s.readReg64 .lr)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 7500000 in
theorem key_execution_from_caller (base : Addr) (s : Arm64.State) (input : ByteList) (extent : Nat)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (sizeBound : input.size < 2 ^ 64) (lengthBound : input.bytes.size < 2 ^ 61)
    (typed : EncodedByteList s.mem (s.readReg64 .x0) input)
    (g : KeyResources base s extent) (pc : s.pc = routineAddress base key)
    (live : s.status = .Running)
    (shaLoaded : (program (shaAddress base)).CodeLoaded s.mem)
    (loaded : (programAt key (routineAddress base key)).CodeLoaded s.mem) :
    ∃ out events, LinkedExecution base s events out ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec) ∧
      (∀ p, ¬ (keyWorkspace s).Contains p → ¬ (keyOutput s).Contains p → out.mem.cells p = s.mem.cells p) ∧
      KeyWholeTrace base s input events := by
  let work := keyWorkspace s
  let nested := regionSlice work 0 416
  let spill := regionSlice work 416 96
  let start := enteredState s 96#64
  let cleared := (start.setMem (writeWords start.mem (start.readReg64 .x1) (fun _ => 0#64) 8)).setPC (start.pc + 16#64)
  have workValid : work.Valid := stackRegion_valid _ _ g.available
  have nestedFits : 0 + 416 ≤ work.bytes := by change 0 + 416 ≤ 512; decide
  have spillFits : 416 + 96 ≤ work.bytes := by change 416 + 96 ≤ 512; decide
  have nestedValid : nested.Valid := regionSlice_valid _ _ _ workValid nestedFits
  have spillValid : spill.Valid := regionSlice_valid _ _ _ workValid spillFits
  have inNested (p : Addr) (hit : nested.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ workValid nestedFits p hit
  have inSpill (p : Addr) (hit : spill.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ workValid spillFits p hit
  have low : 96 ≤ s.sp.toNat := by have := g.available; omega
  have stack := frame_base_end s.sp 96 low
  have startSP : start.sp = s.sp - 96#64 := rfl
  have aligned : s.spAligned = true := by simp [Arm64.State.spAligned, stack_mask _ g.aligned]
  have frameAligned : (s.sp - 96#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 96 g.aligned (by decide) low
  have frameMask := stack_mask _ frameAligned
  have spillBase : spill.base = start.sp :=
    congrArg Region.base (stackRegion_slice s.sp 512 416 96 (by decide))
  have stackAt (off n : Nat) (fits : off + n ≤ 96) :
      work.base + BitVec.ofNat 64 (416 + off) = start.sp + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact congrArg (· + BitVec.ofNat 64 off) spillBase
  have enterWrites (i : Fin 12) : s.mem.canWrite (s.sp - 96#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [← startSP, ← stackAt (8 * i.val) 8 (by have := i.isLt; omega)]
    exact caller_region_write _ work workValid g.stackWrite (416 + 8 * i.val) 8
      (by have := i.isLt; change _ ≤ 512; omega)
  have localReads (i : Fin 12) : s.mem.canRead (start.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [← stackAt (8 * i.val) 8 (by have := i.isLt; omega)]
    exact caller_region_read _ work workValid g.stackRead (416 + 8 * i.val) 8
      (by have := i.isLt; change _ ≤ 512; omega)
  have startIn : start.readReg64 .x0 = s.readReg64 .x0 :=
    by simp (config := {decide := true}) [start, enteredState, reg_write_gpr, Arm64.Reg.x0, Arm64.Reg.x29]
  have startOut : start.readReg64 .x1 = s.readReg64 .x1 :=
    by simp (config := {decide := true}) [start, enteredState, reg_write_gpr, Arm64.Reg.x1, Arm64.Reg.x29]
  have belongs : key = entry ∨ key = key ∨ key = finish := .inr (.inl rfl)
  have enter := enter_key s aligned frameMask enterWrites
  obtain ⟨prologue, _⟩ := run_range_observes belongs (by simpa only [BitVec.add_zero] using pc)
    (by decide) loaded (by decide +kernel) enter (show start.status = .Running from live)
  have startPC : start.pc = routineAddress base key + 0x1c#64 := by
    change s.pc + 28#64 = _
    rw [pc]
  have clearWrite (i : Fin 8) : start.mem.canWrite (start.readReg64 .x1 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [startOut, prologue.grants.write]
    exact caller_region_write _ _ g.outputValid g.outputWrite (8 * i.val) 8
      (by have := i.isLt; change _ ≤ 64; omega)
  have zeroRun : runRange key 0x1c 4 start = some cleared := key_zero start clearWrite
  obtain ⟨zeroed, zeroRange, zeros, zeroFrame⟩ := key_zero_byte start clearWrite
  have same := Option.some.inj (zeroRange.symm.trans zeroRun)
  subst zeroed
  obtain ⟨zero, _⟩ := run_range_observes belongs startPC (by decide) (prologue.keeps_code _ loaded)
    (by decide +kernel) zeroRun (show cleared.status = .Running from live)
  have initial := prologue.append zero
  have clearedPC : cleared.pc = routineAddress base key + 0x2c#64 := by
    change start.pc + 16#64 = _
    rw [startPC, BitVec.add_assoc]
    rfl
  have clearedIn : cleared.readReg64 .x0 = s.readReg64 .x0 := startIn
  have clearedOut : cleared.readReg64 .x1 = s.readReg64 .x1 := startOut
  have clearElsewhere (p : Addr) (off : ¬ (keyOutput s).Contains p) :
      cleared.mem.cells p = start.mem.cells p := by
    apply zeroFrame
    rw [startOut]
    exact caller_outside_delta _ g.outputValid p off
  have spillElsewhere (p : Addr) (off : ¬ work.Contains p) : start.mem.cells p = s.mem.cells p :=
    by
      have delta := caller_outside_delta spill spillValid p (fun h => off (inSpill p h))
      rw [spillBase, startSP] at delta
      exact writeWords_outside _ _ _ 12 p delta
  have inputHere : EncodedByteList cleared.mem (cleared.readReg64 .x0) input := by
    rw [clearedIn]
    apply typed.preserved layout accessible g.inputValid
    intro p inside
    exact (clearElsewhere p (fun h => g.outputInput p ⟨h, inside⟩)).trans
      (spillElsewhere p (fun h => g.stackInput p ⟨h, inside⟩))
  have header : 24 ≤ extent := by have fixed := layout.1; have off := layout.2.2.1; omega
  have readAt (off n : Nat) (fit : off + n ≤ extent) :
      cleared.mem.canRead (cleared.readReg64 .x0 + BitVec.ofNat 64 off) n = true := by
    rw [clearedIn]
    exact initial.grants.read _ _ (caller_region_read _ _ g.inputValid g.inputRead off n fit)
  have writeAt (off n : Nat) (fit : off + n ≤ 64) :
      cleared.mem.canWrite (cleared.readReg64 .x1 + BitVec.ofNat 64 off) n = true := by
    rw [clearedOut, initial.grants.write]
    exact caller_region_write _ _ g.outputValid g.outputWrite off n fit
  have payloadFits : input.offset + input.bytes.size ≤ extent := by
    have within := layout.2.2.2
    have offset := layout.2.2.1
    omega
  have body : ∃ after events, LinkedExecution base cleared events after ∧
      after.sp = start.sp ∧ after.pc = routineAddress base key + 0x74#64 ∧ after.status = .Running ∧
      (∀ i : Fin 64, after.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬ nested.Contains p → ¬ (keyOutput s).Contains p → after.mem.cells p = cleared.mem.cells p) ∧
      KeyBodyTrace base (s.sp - 96#64) (s.readReg64 .x0) (s.readReg64 .x1) input events := by
    by_cases short : input.bytes.size ≤ 64
    · have disjointPrefix (i : Nat) (within : i < input.bytes.size) :
          input.bytes.size ≤ (cleared.readReg64 .x0 + BitVec.ofNat 64 (input.offset + i) -
            cleared.readReg64 .x1).toNat := by
        rw [clearedIn, clearedOut]
        have inside := caller_region_contains_offset (keyInput s extent) g.inputValid (input.offset + i) (by change _ < extent; omega)
        have apart := caller_outside_delta _ g.outputValid _
          (fun h => g.outputInput _ ⟨h, inside⟩)
        exact short.trans apart
      obtain ⟨after, run, _, endPC, running, bytes, frame, _, stable⟩ :=
        short_key_after_clear base cleared input clearedPC (initial.keeps_code _ loaded) live short
          inputHere.count inputHere.offset (readAt 16 8 header) (readAt 8 8 (by omega))
          (fun i hi => inputHere.bytes ⟨i, hi⟩) (fun i _ => zeros i) disjointPrefix
          (fun w i hi => readAt (input.offset + i) (copyWidth w).bytes (by omega)) (fun _ _ hi => writeAt _ _ (by omega))
      have sameSP : (nonMemory after).sp = (nonMemory cleared).sp := congrArg Arm64.State.sp stable
      have clearedSP : cleared.sp = s.sp - 96#64 := startSP
      rw [clearedSP, clearedIn, clearedOut] at run
      refine ⟨after, _, run, sameSP, endPC, running,
        fun i => clearedOut ▸ bytes i, ?_, .short short⟩
      intro p _ out
      apply frame
      rw [clearedOut]
      exact short.trans (caller_outside_delta _ g.outputValid p out)
    · have long : 64 < input.bytes.size := by omega
      let tested := keyTestState cleared (BitVec.ofNat 64 input.bytes.size)
      let callee := longKeyCall tested
      have compare := key_length_test cleared (BitVec.ofNat 64 input.bytes.size) inputHere.count (readAt 16 8 header)
      have branch : tested.pc = routineAddress base key + 0x70#64 := by
        change (if 64 < (BitVec.ofNat 64 input.bytes.size).toNat then cleared.pc + 68#64
          else cleared.pc + 12#64) = _
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos long, clearedPC, BitVec.add_assoc]
        rfl
      obtain ⟨test, _⟩ := run_range_observes belongs clearedPC (by decide) (initial.keeps_code _ loaded)
        (by decide +kernel) compare (show tested.status = .Running from live)
      have beforeCall := initial.append test
      have calleeIn : callee.readReg64 .x0 = s.readReg64 .x0 := by
        have x : callee.readReg64 .x0 = cleared.readReg64 .x0 := by
          simp (config := {decide := true}) [callee, tested, longKeyCall, keyTestState, reg_write_gpr,
            Arm64.Reg.x0, Arm64.Reg.x2, Arm64.Reg.lr]
        exact x.trans clearedIn
      have calleeOut : callee.readReg64 .x1 = s.readReg64 .x1 := by
        have x : callee.readReg64 .x1 = cleared.readReg64 .x1 := by
          simp (config := {decide := true}) [callee, tested, longKeyCall, keyTestState, reg_write_gpr,
            Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.lr]
        exact x.trans clearedOut
      have testedOut : tested.readReg64 .x1 = s.readReg64 .x1 := by
        simp (config := {decide := true}) [tested, keyTestState, reg_write_gpr, Arm64.Reg.x1,
          Arm64.Reg.x2, clearedOut]
      have stk : callerStack callee = nested := by
        change (⟨(s.sp - 96#64) - 416#64, 416⟩ : Region) = _
        rw [BitVec.sub_sub]
        exact (stackRegion_slice _ 512 0 416 (by decide)).symm
      have src : callerInput callee extent = keyInput s extent := by rw [callerInput, calleeIn]; rfl
      have dst : callerOutput callee = regionSlice (keyOutput s) 0 32 := by
        simp [callerOutput, calleeOut, regionSlice, keyOutput]
      have outFits : 0 + 32 ≤ (keyOutput s).bytes := by change 0 + 32 ≤ 64; decide
      have outValid := regionSlice_valid (keyOutput s) 0 32 g.outputValid outFits
      have outInside (p : Addr) (h : (callerOutput callee).Contains p) : (keyOutput s).Contains p :=
        regionSlice_inside _ 0 32 g.outputValid outFits p (dst ▸ h)
      have resources : ShaResources (shaAddress base) callee extent := {
        loaded := beforeCall.keeps_code _ shaLoaded
        messageAligned := calleeIn.symm ▸ g.inputAligned
        digestAligned := calleeOut.symm ▸ g.outputAligned
        stackAligned := frameAligned
        stackAvailable := by change 416 ≤ (s.sp - 96#64).toNat; have := g.available; omega
        inputValid := src.symm ▸ g.inputValid
        outputValid := dst.symm ▸ outValid
        stackValid := stk.symm ▸ nestedValid
        imageValid := g.imageValid
        outputInput := fun p h => g.outputInput p ⟨outInside p h.1, src ▸ h.2⟩
        outputStack := fun p h => g.stackOutput p ⟨inNested p (stk ▸ h.2), outInside p h.1⟩
        outputImage := fun p h => g.outputImage p ⟨outInside p h.1, h.2⟩
        stackInput := fun p h => g.stackInput p ⟨inNested p (stk ▸ h.1), src ▸ h.2⟩
        stackImage := fun p h => g.stackImage p ⟨inNested p (stk ▸ h.1), h.2⟩
        inputRead := fun p h => beforeCall.grants.read _ _ (g.inputRead p (src ▸ h))
        stackRead := fun p h => beforeCall.grants.read _ _ (g.stackRead p (inNested p (stk ▸ h)))
        stackWrite := fun p h => by
          change tested.mem.canWrite p 1 = true
          rw [beforeCall.grants.write]
          exact g.stackWrite p (inNested p (stk ▸ h))
        outputWrite := fun p h => by
          change tested.mem.canWrite p 1 = true
          rw [beforeCall.grants.write]
          exact g.outputWrite p (outInside p h)
      }
      have actual : EncodedByteList callee.mem (callee.readReg64 .x0) input := by
        change EncodedByteList cleared.mem (callee.readReg64 .x0) input
        rw [calleeIn, ← clearedIn]
        exact inputHere
      have contract := establish_sha_entry layout accessible sizeBound lengthBound actual resources
        (key_call_target base tested branch) (show callee.status = .Running from live)
      have tail (i : Fin 64) : 416 ≤
          (tested.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack callee).toNat := by
        rw [testedOut]
        have inside := caller_region_contains_offset _ g.outputValid i.val i.isLt
        have outside := caller_outside_delta nested nestedValid _ (fun h => g.stackOutput _ ⟨inNested _ h, inside⟩)
        rw [← stk] at outside
        exact outside
      obtain ⟨out, events, call, checked, outPC, output⟩ := long_key_after_clear tested input long base extent branch contract
        (fun i _ => by rw [testedOut, ← startOut]; exact zeros i) (fun i _ => tail i)
      obtain ⟨transfer, _⟩ := run_range_observes belongs branch (by decide) (beforeCall.keeps_code _ loaded)
        (by decide +kernel) call (show callee.status = .Running from live)
      have lengthy : decide (64 < (BitVec.ofNat 64 input.bytes.size).toNat) = true := by
        apply decide_eq_true
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact long
      have testTrace := key_test_events base cleared (BitVec.ofNat 64 input.bytes.size) clearedPC
        inputHere.count (readAt 16 8 header)
      have clearedSP : cleared.sp = s.sp - 96#64 := startSP
      rw [lengthy, clearedSP, clearedIn] at testTrace
      have transferTrace := key_invoke_events base tested branch
      have testedSP : tested.sp = s.sp - 96#64 := startSP
      rw [testedSP] at transferTrace
      have calleeSP : callee.sp = s.sp - 96#64 := startSP
      have returnPC : callee.readReg64 .lr = routineAddress base key + 0x74#64 := by
        change tested.pc + 4#64 = _
        rw [branch, BitVec.add_assoc]
        rfl
      rw [testTrace] at test
      rw [transferTrace] at transfer
      have sha := LinkedExecution.shaCall checked (.nil out)
      rw [List.append_nil] at sha
      refine ⟨out, _, (test.append transfer).append sha, checked.abi.stack, outPC, checked.running,
        fun i => testedOut ▸ output i, ?_, .long long checked calleeIn calleeOut calleeSP returnPC⟩
      intro p offNested offOutput
      apply checked.frame
      · have delta := caller_outside_delta nested nestedValid p offNested
        rw [← stk] at delta
        exact delta
      · rw [calleeOut]
        exact (by decide : 32 ≤ 64).trans (caller_outside_delta _ g.outputValid p offOutput)
  obtain ⟨after, bodyEvents, ran, sp, afterPC, running, bytes, kept, trace⟩ := body
  have through := initial.append ran
  have saves (i : Fin 96) : after.mem.cells (start.sp + BitVec.ofNat 64 i.val) =
      start.mem.cells (start.sp + BitVec.ofNat 64 i.val) := by
    have hit : spill.Contains (start.sp + BitVec.ofNat 64 i.val) := by
      rw [← spillBase]
      exact caller_region_contains_offset spill spillValid i.val i.isLt
    have noNested : ¬ nested.Contains (start.sp + BitVec.ofNat 64 i.val) := fun near =>
      regionSlices_disjoint work 0 416 416 96 workValid (by decide) spillFits _ ⟨near, hit⟩
    have noOutput : ¬ (keyOutput s).Contains (start.sp + BitVec.ofNat 64 i.val) := fun near =>
      g.stackOutput _ ⟨inSpill _ hit, near⟩
    exact (kept _ noNested noOutput).trans (clearElsewhere _ noOutput)
  have words (i : Fin 12) : after.mem.read64 (after.sp + BitVec.ofNat 64 (8 * i.val)) =
      s.readReg64 (savedRegister i.val) := by
    rw [sp]
    calc
      _ = start.mem.read64 (start.sp + BitVec.ofNat 64 (8 * i.val)) := by
        apply read64_eq_of_cells
        intro j
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact saves ⟨8 * i.val + j.val, by have := j.isLt; have := i.isLt; omega⟩
      _ = _ := writeWords_word _ _ _ 12 i.val i.isLt (by decide)
  have afterAligned : after.spAligned = true := by simp [Arm64.State.spAligned, sp, startSP, frameMask]
  have canRead (i : Fin 12) : after.mem.canRead (after.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [sp]
    exact through.grants.read _ _ (localReads i)
  let out := restoreState after 96#64
  obtain ⟨returned, _⟩ := run_range_observes belongs afterPC (by decide) (through.keeps_code _ loaded)
    (by decide +kernel) (returns after afterAligned canRead).2.1 (show out.status = .Running from running)
  have prologueEvents : rangeEvents key 0 7 s = frameEnterEvents s.pc s.sp 96#64 := by
    simpa only [rangeEvents, key_enter_decoded, Option.getD_some] using
      save_code_events s 96#64 aligned frameMask enterWrites
  have zeroEvents := key_zero_events base start startPC clearWrite
  rw [startSP, startOut] at zeroEvents
  have returnEvents : rangeEvents key 0x74 7 after =
      frameReturnEvents (routineAddress base key + 0x74#64) (s.sp - 96#64) 96#64 (s.readReg64 .lr) := by
    have observed := restore_code_events after 96#64 afterAligned canRead
    have wordLink : after.mem.read64 (after.sp + 8#64) = s.readReg64 .lr := words ⟨1, by decide⟩
    rw [wordLink, afterPC, sp, startSP] at observed
    simpa only [rangeEvents, key_return_decoded, Option.getD_some] using observed
  rw [prologueEvents] at prologue
  rw [zeroEvents] at zero
  rw [returnEvents] at returned
  refine ⟨out, _, (((prologue.append zero).append ran).append returned), ?_,
    words ⟨1, by decide⟩, running, ?_, ?_, ?_, ⟨bodyEvents, trace, rfl⟩⟩
  · change after.sp + 96#64 = _
    rw [sp, startSP, BitVec.sub_add_cancel]
  · intro i
    rw [show out = restoreState after 96#64 from rfl, restored_register]
    exact words i
  · intro i
    have h := bytes i
    rw [getElem!_pos _ _ (by change i.val < (hmacKey input).toArray.size; rw [(hmacKey input).size_toArray]; exact i.isLt)] at h
    exact h
  · intro p offStack offOutput
    exact (kept p (fun h => offStack (inNested p h)) offOutput).trans
      ((clearElsewhere p offOutput).trans (spillElsewhere p offStack))

end Crypto.HMACSHA256.ARM64
