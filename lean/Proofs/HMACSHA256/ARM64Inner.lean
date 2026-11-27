import Proofs.HMACSHA256.ARM64InnerSetup
import Proofs.HMACSHA256.ARM64CopyLoop
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference EthLib.Cryptography.Hash
open Crypto.Baseline (Region)

def innerEvents (base : Addr) (s header masked padded : Arm64.State) (message : ByteList) :
    List InstructionObservation :=
  rangeEvents entry 0x54 8 s ++ rangeEvents entry 0x74 5 header ++
  rangeEvents entry 0x88 16 masked ++ rangeEvents entry 0xc8 3 padded ++
  copyPayloadEvents (routineAddress base entry + 0xd4#64) s.sp
    (s.readReg64 .x20 + BitVec.ofNat 64 message.offset) (s.readReg64 .x21 + 96#64) message.bytes.size

structure InnerTrace (base : Addr) (s : Arm64.State) (message : ByteList)
    (events : List InstructionObservation) where
  header : Arm64.State
  masked : Arm64.State
  padded : Arm64.State
  copier : Arm64.State
  writeHeader : runRange entry 0x54 8 s = some header
  mask : runRange entry 0x74 5 header = some masked
  pad : runRange entry 0x88 16 masked = some padded
  prepareCopy : runRange entry 0xc8 3 padded = some copier
  headerPC : header.pc = routineAddress base entry + 0x74#64
  maskedPC : masked.pc = routineAddress base entry + 0x88#64
  paddedPC : padded.pc = routineAddress base entry + 0xc8#64
  headerLive : header.status = .Running
  maskedLive : masked.status = .Running
  paddedLive : padded.status = .Running
  copyLive : copier.status = .Running
  trace : events = innerEvents base s header masked padded message

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3500000 in
/-- After the key helper returns, construct the serialized inner hash input.
The modified scratch span starts after the capacity word and ends at the
last byte to be hashed. -/
theorem entry_inner_list (base : Addr) (s : Arm64.State) (message : ByteList)
    (k0 : HmacKeyBlock) (capacity extent : Nat)
    (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (value : EncodedByteList s.mem (s.readReg64 .x20) message)
    (sizeAt : s.mem.read64 (s.readReg64 .x21) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (size64 : capacity < 2 ^ 64)
    (scratchValid : (⟨s.readReg64 .x21, capacity⟩ : Region).Valid)
    (messageValid : (⟨s.readReg64 .x20, extent⟩ : Region).Valid)
    (keyValid : (⟨s.sp + 96#64, 64⟩ : Region).Valid)
    (scratchMessage : (⟨s.readReg64 .x21, capacity⟩ : Region).Disjoint ⟨s.readReg64 .x20, extent⟩)
    (scratchKey : (⟨s.readReg64 .x21, capacity⟩ : Region).Disjoint ⟨s.sp + 96#64, 64⟩)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.sp + 96#64 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (scratchRead : s.mem.canRead (s.readReg64 .x21) 8 = true)
    (scratchWrite : ∀ p, (⟨s.readReg64 .x21, capacity⟩ : Region).Contains p → s.mem.canWrite p 1 = true)
    (messageRead : ∀ p, (⟨s.readReg64 .x20, extent⟩ : Region).Contains p → s.mem.canRead p 1 = true)
    (keyRead : ∀ p, (⟨s.sp + 96#64, 64⟩ : Region).Contains p → s.mem.canRead p 1 = true)
    (pc : s.pc = routineAddress base entry + 0x54#64)
    (loaded : (programAt entry (routineAddress base entry)).CodeLoaded s.mem)
    (live : s.status = .Running) :
    ∃ out events, LinkedExecution base s events out ∧
      out.pc = routineAddress base entry + 0x100#64 ∧ out.sp = s.sp ∧ out.status = .Running ∧
      out.readReg64 .x21 = s.readReg64 .x21 ∧ out.readReg64 .x22 = s.readReg64 .x22 ∧
      EncodedByteList out.mem (s.readReg64 .x21 + 8#64) (hmacInner message k0 capacity) ∧
      (∀ p, ¬ (⟨s.readReg64 .x21 + 8#64, 88 + message.bytes.size⟩ : Region).Contains p →
        out.mem.cells p = s.mem.cells p) ∧ Nonempty (InnerTrace base s message events) := by
  let scratch : Region := ⟨s.readReg64 .x21, capacity⟩
  let msg : Region := ⟨s.readReg64 .x20, extent⟩
  let kr : Region := ⟨s.sp + 96#64, 64⟩
  let changed := regionSlice scratch 8 (88 + message.bytes.size)
  let count := BitVec.ofNat 64 message.bytes.size
  let header := innerHeaderState s count
  let masked := ipadStart header
  have changedValid : changed.Valid := regionSlice_valid _ _ _ scratchValid (by change 8 + _ ≤ capacity; omega)
  have changedInside (p : Addr) (inWrite : changed.Contains p) : scratch.Contains p :=
    regionSlice_inside _ _ _ scratchValid (by change 8 + _ ≤ capacity; omega) p inWrite
  have away (off n : Nat) (start : 8 ≤ off) (fits : off + n ≤ 96 + message.bytes.size)
      (p : Addr) (apart : ¬ changed.Contains p) :
      n ≤ (p - (scratch.base + BitVec.ofNat 64 off)).toNat := by
    have span : regionSlice scratch off n = regionSlice changed (off - 8) n := by
      change (⟨scratch.base + BitVec.ofNat 64 off, n⟩ : Region) =
        ⟨(scratch.base + 8#64) + BitVec.ofNat 64 (off - 8), n⟩
      have add : 8#64 + BitVec.ofNat 64 (off - 8) = BitVec.ofNat 64 off := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [BitVec.add_assoc, add]
    have fit : off - 8 + n ≤ changed.bytes := by change _ ≤ 88 + _; omega
    change (regionSlice scratch off n).bytes ≤ (p - (regionSlice scratch off n).base).toNat
    rw [span]
    exact caller_outside_delta _ (regionSlice_valid _ _ _ changedValid fit) p
      (fun hit => apart (regionSlice_inside _ _ _ changedValid fit p hit))
  have msgAway (i : Nat) (fits : i < extent) : ¬ changed.Contains (msg.base + BitVec.ofNat 64 i) :=
    fun h => scratchMessage _ ⟨changedInside _ h, caller_region_contains_offset msg messageValid i fits⟩
  have keyAway (i : Fin 64) : ¬ changed.Contains (kr.base + BitVec.ofNat 64 i.val) :=
    fun h => scratchKey _ ⟨changedInside _ h, caller_region_contains_offset kr keyValid i.val i.isLt⟩
  have metadata : 24 ≤ extent := by have fixed := layout.1; have off := layout.2.2.1; omega
  have messageAt (offset n : Nat) (fit : offset + n ≤ extent) :=
    caller_region_read s.mem msg messageValid messageRead offset n fit
  have scratchAt (offset n : Nat) (fit : offset + n ≤ capacity) :=
    caller_region_write s.mem scratch scratchValid scratchWrite offset n fit
  have countOff (i : Fin 8) : 16 ≤
      (s.readReg64 .x20 + 16#64 + BitVec.ofNat 64 i.val - (s.readReg64 .x21 + 8#64)).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact away 8 16 (by decide) (by omega) _ (msgAway _ (by have := i.isLt; omega))
  have headerRun := entry_inner_header s count value.count countOff scratchRead
    (messageAt 16 8 metadata) (scratchAt 8 8 (by omega)) (scratchAt 16 8 (by omega))
    (scratchAt 24 8 (by omega))
  have headerLive : header.status = .Running := live
  have routine : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨execHeader, _⟩ := run_range_observes routine pc (by decide) loaded
    (by decide +kernel) headerRun headerLive
  have headerPC : header.pc = routineAddress base entry + 0x74#64 := by
    change s.pc + 32#64 = _
    rw [pc, BitVec.add_assoc]
    rfl
  have maskedPC : masked.pc = routineAddress base entry + 0x88#64 := by
    change header.pc + 20#64 = _
    rw [headerPC, BitVec.add_assoc]
    rfl
  have maskedLive : masked.status = .Running := live
  obtain ⟨execMask, _⟩ := run_range_observes routine headerPC (by decide)
    (execHeader.keeps_code _ loaded) (by decide +kernel) (entry_ipad_setup header) maskedLive
  have prePad := execHeader.append execMask
  have maskedReg (r : BitVec 5) (h4 : r ≠ 4#5) (h5 : r ≠ 5#5) (h8 : r ≠ 8#5)
      (h9 : r ≠ 9#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) :
      masked.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    by_cases hz : r = 31#5
    · subst r; rfl
    simp [masked, ipadStart, header, innerHeaderState, Arm64.State.setPC, Arm64.State.setMem,
      Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.write, Arm64.RegFile.read,
      Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x11, Arm64.Reg.x12,
      h4, h5, h8, h9, h11, h12, hz]
  have maskedX20 : masked.readReg64 .x20 = s.readReg64 .x20 :=
    maskedReg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have maskedX21 : masked.readReg64 .x21 = s.readReg64 .x21 :=
    maskedReg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have maskedX22 : masked.readReg64 .x22 = s.readReg64 .x22 :=
    maskedReg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have padSource : masked.readReg64 .x12 = kr.base := by
    simp (config := {decide := true}) [masked, ipadStart, header, innerHeaderState,
      Arm64.State.setPC, Arm64.State.setMem, Arm64.State.readReg64, Arm64.State.writeReg64,
      Arm64.Reg.x12, Arm64.RegFile.read, Arm64.RegFile.write, kr]
  have padDest : masked.readReg64 .x8 = scratch.base + 32#64 := by
    have reg : header.readReg64 .x21 = s.readReg64 .x21 := maskedX21
    change masked.readReg64 .x8 = s.readReg64 .x21 + 32#64
    calc
      _ = header.readReg64 .x21 + 32#64 := by
        simp (config := {decide := true}) only [masked, ipadStart, reg_set_pc, reg_write_gpr,
          Arm64.Reg.x8, Arm64.Reg.x12, if_true, if_false]
      _ = _ := by rw [reg]
  have padMask : masked.readReg64 .x11 = 0x3636363636363636#64 := by
    simp (config := {decide := true}) [masked, ipadStart, Arm64.State.setPC, Arm64.State.readReg64,
      Arm64.State.writeReg64, Arm64.Reg.x8, Arm64.Reg.x11, Arm64.Reg.x12,
      Arm64.RegFile.read, Arm64.RegFile.write]
  have maskedCount : masked.readReg64 .x5 = count := by
    simp (config := {decide := true}) [masked, ipadStart, header, innerHeaderState, Arm64.State.setPC,
      Arm64.State.setMem, Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.Reg.x4, Arm64.Reg.x5,
      Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x11, Arm64.Reg.x12, Arm64.RegFile.read, Arm64.RegFile.write]
  have padRead (i : Fin 8) : masked.mem.canRead (masked.readReg64 .x12 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [padSource]
    exact prePad.grants.read _ _ (caller_region_read _ kr keyValid keyRead _
      8 (by have := i.isLt; change _ ≤ 64; omega))
  have padWrite (i : Fin 8) : masked.mem.canWrite (masked.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [padDest, prePad.grants.write, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact scratchAt _ _ (by have := i.isLt; omega)
  obtain ⟨padded, padRun, padBytes, padFrame, padSP, padLive, padPC, _⟩ := pad_bytes masked .x12
    (.inl rfl) padRead padWrite (by intro i; rw [padSource, padDest]; exact away 32 64 (by decide) (by omega) _ (keyAway i))
  have padCode : runRange entry 0x88 16 masked = some padded := padRun
  have paddedLive : padded.status = .Running := padLive.trans live
  obtain ⟨execPad, _⟩ := run_range_observes routine maskedPC (by decide)
    (prePad.keeps_code _ loaded) (by decide +kernel) padCode paddedLive
  have preCopy := prePad.append execPad
  have keepPad (r : BitVec 5) (h9 : r ≠ 9#5) (h10 : r ≠ 10#5) :=
    pad_preserves_gpr (.inl rfl) padRead padWrite padRun r h9 h10
  have paddedMsg : padded.readReg64 .x20 = msg.base :=
    (keepPad 20#5 (by decide) (by decide)).trans maskedX20
  have paddedScratch : padded.readReg64 .x21 = scratch.base :=
    (keepPad 21#5 (by decide) (by decide)).trans maskedX21
  have paddedPC : padded.pc = routineAddress base entry + 0xc8#64 := by
    rw [padPC, maskedPC, BitVec.add_assoc]
    rfl
  have headFrame (p : Addr) (h : ¬ changed.Contains p) : padded.mem.cells p = s.mem.cells p := by
    rw [padFrame _ (by rw [padDest]; exact away 32 64 (by decide) (by omega) _ h)]
    exact inner_header_outside s count p (away 8 24 (by decide) (by omega) p h)
  have offset : padded.mem.read64 (padded.readReg64 .x20 + 8#64) = BitVec.ofNat 64 message.offset := by
    rw [paddedMsg]
    change padded.mem.read64 (s.readReg64 .x20 + 8#64) = _
    rw [← value.offset]
    apply read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact headFrame _ (msgAway _ (by have := i.isLt; omega))
  let copier := messageCopyStart padded
  have copyRun := entry_copy_setup padded (by rw [paddedMsg]; exact preCopy.grants.read _ _ (messageAt 8 8 (by omega)))
  have copierLive : copier.status = .Running := paddedLive
  obtain ⟨execCopySetup, _⟩ := run_range_observes routine paddedPC (by decide)
    (preCopy.keeps_code _ loaded) (by decide +kernel) copyRun copierLive
  have copyStart := preCopy.append execCopySetup
  have copyRegs (r : BitVec 5) (h6 : r ≠ 6#5) (h8 : r ≠ 8#5) :
      copier.readReg64 (.gpr r) = padded.readReg64 (.gpr r) := by
    by_cases hz : r = 31#5
    · subst r; rfl
    simp [copier, messageCopyStart, Arm64.State.setPC, Arm64.State.readReg64, Arm64.State.writeReg64,
      Arm64.Reg.x6, Arm64.Reg.x8, Arm64.RegFile.read, Arm64.RegFile.write, hz, h6, h8]
  have source : copier.readReg64 (copySource true) = msg.base + BitVec.ofNat 64 message.offset := by
    have addr : copier.readReg64 (copySource true) =
        padded.readReg64 .x20 + padded.mem.read64 (padded.readReg64 .x20 + 8#64) := by
      simp (config := {decide := true}) only [copier, messageCopyStart, copySource, reg_set_pc,
        reg_write_gpr, Arm64.Reg.x6, if_true, if_false]
    rw [addr, offset, paddedMsg]
  have dest : copier.readReg64 (copyDestination true) = scratch.base + 96#64 := by
    have addr : copier.readReg64 (copyDestination true) = padded.readReg64 .x21 + 96#64 := by
      simp (config := {decide := true}) only [copier, messageCopyStart, copyDestination, reg_set_pc,
        reg_write_gpr, Arm64.Reg.x6, Arm64.Reg.x8, if_true, if_false]
    rw [addr, paddedScratch]
  have copierCount : copier.readReg64 (copyCount true) = count :=
    (copyRegs 5#5 (by decide) (by decide)).trans ((keepPad 5#5 (by decide) (by decide)).trans maskedCount)
  have copierPC : copier.pc = routineAddress base (copyRoutine true) + BitVec.ofNat 64 (copyOffset true true) := by
    change padded.pc + 12#64 = routineAddress base entry + 0xd4#64
    rw [paddedPC, BitVec.add_assoc]
    rfl
  have messageEnd : message.offset + message.bytes.size ≤ extent := by
    have off := layout.2.2.1
    have payload := layout.2.2.2
    omega
  obtain ⟨out, loop, _, done, _, copied, copyFrame, nv, nm, _, _⟩ := copy_payload true base copier
    message.bytes.size copierPC (copyStart.keeps_code _ loaded) copierLive copierCount (by omega)
    (by
      intro i hi
      rw [source, dest, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact away 96 _ (by decide) (by omega) _ (msgAway _ (by omega)))
    (by
      intro w i fits
      rw [source, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact copyStart.grants.read _ _ (messageAt _ _ (by omega)))
    (by
      intro w i fits
      rw [dest, copyStart.grants.write, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact scratchAt _ _ (by omega))
  have outPC : out.pc = routineAddress base entry + 0x100#64 := by
    rw [done, copierPC]
    change (routineAddress base entry + 0xd4#64) + 44#64 = _
    rw [BitVec.add_assoc]
    rfl
  have outScratch : out.readReg64 .x21 = scratch.base :=
    (congrFun nv ⟨3, by decide⟩).trans ((copyRegs 21#5 (by decide) (by decide)).trans paddedScratch)
  have outMac : out.readReg64 .x22 = s.readReg64 .x22 :=
    (congrFun nv ⟨4, by decide⟩).trans ((copyRegs 22#5 (by decide) (by decide)).trans
      ((keepPad 22#5 (by decide) (by decide)).trans maskedX22))
  have keepFront (offset : Nat) (inside : offset < 96) :
      out.mem.cells (scratch.base + BitVec.ofNat 64 offset) =
        padded.mem.cells (scratch.base + BitVec.ofNat 64 offset) := by
    apply copyFrame
    rw [dest]
    exact outside_span_of_offset _ _ 96 _ (.inl inside) (by omega) (by omega)
  let start := scratch.base + 8#64
  have headerWord (off : Nat) (within : off + 8 ≤ 24) :
      out.mem.read64 (start + BitVec.ofNat 64 off) = header.mem.read64 (start + BitVec.ofNat 64 off) := by
    apply read64_eq_of_cells
    intro j
    have address : start + BitVec.ofNat 64 off + BitVec.ofNat 64 j.val =
        scratch.base + BitVec.ofNat 64 (8 + off + j.val) := by
      simp only [start, BitVec.ofNat_add, BitVec.add_assoc]
    rw [address, keepFront _ (by have := j.isLt; omega)]
    apply padFrame
    rw [padDest]
    exact outside_span_of_offset _ _ 32 64 (.inl (by have := j.isLt; omega)) (by decide)
      (by have := j.isLt; omega)
  have sizeReal : BitVec.ofNat 64 capacity - 8#64 = BitVec.ofNat 64 (capacity - 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt size64,
      Nat.mod_eq_of_lt (by omega : capacity - 8 < 2 ^ 64)]
    change (2 ^ 64 - 8 + capacity) % 2 ^ 64 = capacity - 8
    omega
  have padAt (i : Fin 64) : out.mem.read8 (start + 24#64 + BitVec.ofNat 64 i.val) =
      (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD)[i.val]!.toBitVec := by
    have b := padBytes i
    rw [padSource, padDest, padMask] at b
    have keySame : masked.mem.read8 (kr.base + BitVec.ofNat 64 i.val) =
        s.mem.read8 (kr.base + BitVec.ofNat 64 i.val) := by
      exact read8_of_cell _
        (inner_header_outside s count _ (away 8 24 (by decide) (by omega) _ (keyAway i)))
    have lane : (0x3636363636363636#64).extractLsb' (8 * (i.val % 8)) 8 = Hmac.IPAD.toBitVec := by
      have all : ∀ j : Fin 8, (0x3636363636363636#64).extractLsb' (8 * j.val) 8 = Hmac.IPAD.toBitVec := by decide +kernel
      exact all ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have hold : out.mem.read8 (scratch.base + 32#64 + BitVec.ofNat 64 i.val) =
        padded.mem.read8 (scratch.base + 32#64 + BitVec.ofNat 64 i.val) := by
      unfold Arm64.Memory.read8
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, keepFront _ (by have := i.isLt; omega)]
    have addr : start + 24#64 = scratch.base + 32#64 := by dsimp only [start]; rw [BitVec.add_assoc]; rfl
    rw [addr, hold, b, keySame, keyAt i, lane]
    have fit : i.val < (EthLib.Base.packBytes k0).size := by
      change i.val < k0.toArray.size
      rw [k0.size_toArray]
      exact i.isLt
    rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact fit), Hmac.xorPad_getElem fit]
    rfl
  have payloadAt (i : Fin message.bytes.size) :
      out.mem.read8 (start + 88#64 + BitVec.ofNat 64 i.val) = message.bytes[i.val]!.toBitVec := by
    have addr : start + 88#64 = scratch.base + 96#64 := by dsimp only [start]; rw [BitVec.add_assoc]; rfl
    rw [addr, ← dest, copied _ i.isLt, source, BitVec.add_assoc, ← BitVec.ofNat_add]
    change padded.mem.read8 _ = _
    unfold Arm64.Memory.read8
    rw [headFrame _ (msgAway _ (by have := i.isLt; omega))]
    exact value.bytes i
  have beforeSP : copier.sp = s.sp := padSP
  have spEq : (nonMemory out).sp = (nonMemory copier).sp := congrArg Arm64.State.sp nm
  have liveEq : (nonMemory out).status = (nonMemory copier).status := congrArg Arm64.State.status nm
  have copiedPC : copier.pc = routineAddress base entry + 0xd4#64 := copierPC
  rw [copiedPC, beforeSP, source, dest] at loop
  refine ⟨out, _, copyStart.append loop, outPC,
    (show out.sp = copier.sp from spEq).trans beforeSP, (show out.status = copier.status from liveEq).trans copierLive,
    outScratch, outMac, ?_, ?_, ⟨⟨header, masked, padded, copier, headerRun, entry_ipad_setup header, padCode,
      copyRun, headerPC, maskedPC, paddedPC, headerLive, maskedLive, paddedLive, copierLive, rfl⟩⟩⟩
  · obtain ⟨size, payloadOffset, payloadCount⟩ := inner_header_values s count
    refine encoded_hmac_inner out.mem start message k0 capacity ?_ ?_ ?_ padAt payloadAt
    · have eq : out.mem.read64 start = header.mem.read64 start := by simpa using headerWord 0 (by decide)
      exact eq.trans (size.trans (by rw [sizeAt]; exact sizeReal))
    · have eq := headerWord 8 (by decide)
      have addr : start + 8#64 = s.readReg64 .x21 + 16#64 := by
        change (s.readReg64 .x21 + 8#64) + 8#64 = _
        rw [BitVec.add_assoc]
        rfl
      change out.mem.read64 (start + 8#64) = _
      rw [eq, addr]
      exact payloadOffset
    · have eq := headerWord 16 (by decide)
      have addr : start + 16#64 = s.readReg64 .x21 + 24#64 := by
        change (s.readReg64 .x21 + 8#64) + 16#64 = _
        rw [BitVec.add_assoc]
        rfl
      change out.mem.read64 (start + 16#64) = _
      rw [eq, addr, payloadCount]
      change BitVec.ofNat 64 message.bytes.size + 64#64 = _
      rw [BitVec.ofNat_add]
      exact BitVec.add_comm _ _
  · intro p h
    exact (copyFrame p (by rw [dest]; exact away 96 _ (by decide) (by omega) _ h)).trans (headFrame p h)

end Crypto.HMACSHA256.ARM64
