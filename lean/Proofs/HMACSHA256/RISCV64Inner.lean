import Proofs.HMACSHA256.RISCV64PadTrace
import Proofs.HMACSHA256.RISCV64InnerSetup
import Proofs.HMACSHA256.RISCV64CopyExecution
import Proofs.HMACSHA256.EncodedByteList
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference EthLib.Cryptography.Hash
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (allPerm_true_iff caller_outside_delta caller_region_contains_offset)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3300000 in
/-- The success path constructs the reference inner list inside the scratch
extent after the incremental key helper has produced K0. The only stores in
these decoded ranges and copy loops are inside that scratch extent. -/
theorem entry_inner_list (s : CPU) (message : ByteList) (k0 : HmacKeyBlock) (capacity extent : Nat)
    (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (value : EncodedByteList s.mem (s.reg 18#5) message)
    (sizeAt : s.mem.read64 (s.reg 19#5) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (size64 : capacity < 2 ^ 64)
    (scratchValid : (⟨s.reg 19#5, capacity⟩ : Region).Valid)
    (messageValid : (⟨s.reg 18#5, extent⟩ : Region).Valid)
    (keyValid : (⟨s.reg 2#5, 64⟩ : Region).Valid)
    (scratchMessage : (⟨s.reg 19#5, capacity⟩ : Region).Disjoint ⟨s.reg 18#5, extent⟩)
    (scratchKey : (⟨s.reg 19#5, capacity⟩ : Region).Disjoint ⟨s.reg 2#5, 64⟩)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 2#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec) :
    ∃ header mask padded copier atTail out,
      runRange entry 0x46 8 s = some header ∧ runRange entry 0x62 9 header = some mask ∧
      runRange entry 0x80 24 mask = some padded ∧ runRange entry 0xd0 3 padded = some copier ∧
      wordCycles true copier (message.bytes.size / 8 + 1) = some atTail ∧
      byteCycles true atTail (message.bytes.size % 8 + 1) = some out ∧
      out.pc = s.pc + 190#64 ∧ out.reg 2#5 = s.reg 2#5 ∧
      out.reg 19#5 = s.reg 19#5 ∧ out.reg 20#5 = s.reg 20#5 ∧
      EncodedByteList out.mem (s.reg 19#5 + 8#64) (hmacInner message k0 capacity) ∧
      (∀ p, ¬ (regionSlice ⟨s.reg 19#5, capacity⟩ 8 (88 + message.bytes.size)).Contains p →
        out.mem.cells p = s.mem.cells p) ∧
      header.pc = s.pc + 28#64 ∧ mask.pc = s.pc + 58#64 ∧ padded.pc = s.pc + 138#64 ∧
      copier.pc = s.pc + 148#64 ∧ mask.reg 2#5 = s.reg 2#5 ∧
      mask.reg 29#5 = s.reg 19#5 + 32#64 ∧ padded.reg 18#5 = s.reg 18#5 ∧
      copier.reg 30#5 = s.reg 18#5 + BitVec.ofNat 64 message.offset ∧
      copier.reg 29#5 = s.reg 19#5 + 96#64 ∧ copier.reg 6#5 = BitVec.ofNat 64 message.bytes.size := by
  let scratch : Region := ⟨s.reg 19#5, capacity⟩
  let written := regionSlice scratch 8 (88 + message.bytes.size)
  let msg : Region := ⟨s.reg 18#5, extent⟩
  let key : Region := ⟨s.reg 2#5, 64⟩
  let count := BitVec.ofNat 64 message.bytes.size
  let header := innerHeaderState s count
  let masked := innerMaskState header
  have readableCount : 24 ≤ extent := by
    have h1 := layout.1
    have h2 := layout.2.2.1
    omega
  have outside (off len : Nat) (fits : off + len ≤ capacity) (p : Addr)
      (away : ¬ scratch.Contains p) : len ≤ (p - (s.reg 19#5 + BitVec.ofNat 64 off)).toNat := by
    change (regionSlice scratch off len).bytes ≤ (p - (regionSlice scratch off len).base).toNat
    exact caller_outside_delta _ (regionSlice_valid _ _ _ scratchValid fits) p
      (fun hit => away (regionSlice_inside _ _ _ scratchValid fits p hit))
  have withinWritten (off len : Nat) (low : 8 ≤ off) (high : off + len ≤ 96 + message.bytes.size)
      (p : Addr) (away : ¬ written.Contains p) : len ≤ (p - (s.reg 19#5 + BitVec.ofNat 64 off)).toNat := by
    have fits : off + len ≤ capacity := high.trans room
    change (regionSlice scratch off len).bytes ≤ (p - (regionSlice scratch off len).base).toNat
    exact caller_outside_delta _ (regionSlice_valid _ _ _ scratchValid fits) p
      (fun hit => away (regionSlice_subset scratch off len 8 (88 + message.bytes.size) scratchValid
        low (by omega) (by change 8 + (88 + message.bytes.size) ≤ capacity; omega) p hit))
  have msgAway (i : Nat) (fits : i < extent) : ¬ scratch.Contains (s.reg 18#5 + BitVec.ofNat 64 i) :=
    fun hit => scratchMessage _ ⟨hit, caller_region_contains_offset msg messageValid i fits⟩
  have keyAway (i : Fin 64) : ¬ scratch.Contains (s.reg 2#5 + BitVec.ofNat 64 i.val) :=
    fun hit => scratchKey _ ⟨hit, caller_region_contains_offset key keyValid i.val i.isLt⟩
  have countOff (i : Fin 8) : 16 ≤
      (s.reg 18#5 + 16#64 + BitVec.ofNat 64 i.val - (s.reg 19#5 + 8#64)).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact outside 8 16 (by omega) _ (msgAway _ (by have := i.isLt; omega))
  have headerRun := entry_inner_header s count value.count countOff
  have maskRun := entry_ipad_setup header
  have keepReg (r : Reg) (nz : r ≠ 0) (r5 : r ≠ 5#5) (r6 : r ≠ 6#5) (r28 : r ≠ 28#5)
      (r29 : r ≠ 29#5) : masked.reg r = s.reg r := by
    simp only [masked, innerMaskState, header, innerHeaderState, reg_advance, setPC_reg, reg_write, reg_put,
      if_neg nz, if_neg r5, if_neg r6, if_neg r28, if_neg r29]
  have hScratch : header.reg 19#5 = s.reg 19#5 := by
    simp (config := { decide := true }) only [header, innerHeaderState, setPC_reg, reg_write, reg_put,
      if_true, if_false]
  have dst : masked.reg 29#5 = s.reg 19#5 + 32#64 := by
    simp (config := { decide := true }) only [masked, innerMaskState, reg_advance, reg_put, if_true, if_false,
      hScratch]
  have ipadMask : masked.reg 28#5 = 0x3636363636363636#64 := by
    simp (config := { decide := true }) only [masked, innerMaskState, reg_advance, reg_put, if_true, if_false]
  have keyPointer : masked.reg 2#5 = s.reg 2#5 := keepReg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have srcPointer : masked.reg 18#5 = s.reg 18#5 := keepReg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have scratchPointer : masked.reg 19#5 = s.reg 19#5 := keepReg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have nreg : masked.reg 6#5 = count := by
    simp (config := { decide := true }) only [masked, innerMaskState, header, innerHeaderState,
      reg_advance, setPC_reg, reg_write, reg_put, if_true, if_false]
  have m0 : masked.mem = header.mem := by simp only [masked, innerMaskState, memory_advance, memory_put]
  obtain ⟨padded, pad, padBytes, padFrame, padRegs, padPC, _, _⟩ := pad_run masked false
    (by
      intro i
      change 64 ≤ (masked.reg 2#5 + BitVec.ofNat 64 i.val - masked.reg 29#5).toNat
      rw [keyPointer, dst]
      exact outside 32 64 (by omega) _ (keyAway i))
  change runRange entry 0x80 24 masked = some padded at pad
  let copier := messageCopyState padded
  have frameBeforeWritten (p : Addr) (away : ¬ written.Contains p) : padded.mem.cells p = s.mem.cells p := by
    rw [padFrame _ (by rw [dst]; exact withinWritten 32 64 (by decide) (by omega) _ away), m0]
    exact inner_header_outside s count p (withinWritten 8 24 (by decide) (by omega) p away)
  have frameBefore (p : Addr) (away : ¬ scratch.Contains p) : padded.mem.cells p = s.mem.cells p :=
    frameBeforeWritten p (fun h => away (regionSlice_inside scratch 8 (88 + message.bytes.size)
      scratchValid (by change 8 + (88 + message.bytes.size) ≤ capacity; omega) p h))
  have offset : padded.mem.read64 (s.reg 18#5 + 8#64) = BitVec.ofNat 64 message.offset := by
    rw [← value.offset]
    apply read64_eq_of_cells
    intro i
    apply frameBefore
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact msgAway _ (by have := i.isLt; omega)
  have src : copier.reg 30#5 = s.reg 18#5 + BitVec.ofNat 64 message.offset := by
    simp (config := { decide := true }) only [copier, messageCopyState, reg_advance, reg_put, if_true,
      if_false, padRegs _ (by decide : (18#5 : Reg) ≠ 31#5), srcPointer, offset]
    exact BitVec.add_comm _ _
  have dest : copier.reg 29#5 = s.reg 19#5 + 96#64 := by
    simp (config := { decide := true }) only [copier, messageCopyState, reg_advance, reg_put, if_true,
      if_false, padRegs _ (by decide : (19#5 : Reg) ≠ 31#5), scratchPointer]
  have num : copier.reg 6#5 = count := by
    simp (config := { decide := true }) only [copier, messageCopyState, reg_advance, reg_put, if_true,
      if_false, padRegs _ (by decide : (6#5 : Reg) ≠ 31#5), nreg]
  have mc : copier.mem = padded.mem := by simp only [copier, messageCopyState, memory_advance, memory_put]
  have nSmall : message.bytes.size < 2 ^ 64 := by omega
  have messageIndex (i : Nat) (bound : i < message.bytes.size) : message.offset + i < extent := by
    have within := layout.2.2.2
    have off := layout.2.2.1
    omega
  obtain ⟨tail, out, word, bytes, pc, _, copied, copyFrame, copySP⟩ :=
    complete_copy true copier message.bytes.size num nSmall (by
      intro i hi
      rw [src, dest, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact outside 96 message.bytes.size room _ (msgAway _ (messageIndex i hi)))
  have pcOut : out.pc = s.pc + 190#64 := by
    rw [pc]
    change padded.pc + 10#64 + 42#64 = _
    rw [padPC]
    change s.pc + 28#64 + 30#64 + 80#64 + 10#64 + 42#64 = _
    simp only [BitVec.add_assoc] <;> rfl
  have keepThroughCopy (r : Reg) (nz : r ≠ 0) (r5 : r ≠ 5#5) (r6 : r ≠ 6#5) (r28 : r ≠ 28#5)
      (r29 : r ≠ 29#5) (r30 : r ≠ 30#5) (r31 : r ≠ 31#5) : out.reg r = s.reg r := by
    rw [copySP r r6 r29 r30 r31]
    simp only [copier, messageCopyState, reg_advance, reg_put, if_neg nz, if_neg r29,
      if_neg r30, padRegs r r31]
    exact keepReg r nz r5 r6 r28 r29
  have spOut : out.reg 2#5 = s.reg 2#5 :=
    keepThroughCopy _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have scratchOut : out.reg 19#5 = s.reg 19#5 :=
    keepThroughCopy _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have macOut : out.reg 20#5 = s.reg 20#5 :=
    keepThroughCopy _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let start := s.reg 19#5 + 8#64
  have keepFront (off : Nat) (inside : 8 ≤ off ∧ off < 96) :
      out.mem.cells (s.reg 19#5 + BitVec.ofNat 64 off) = padded.mem.cells (s.reg 19#5 + BitVec.ofNat 64 off) := by
    rw [← mc]
    apply copyFrame
    rw [dest]
    exact outside_span_of_offset _ _ 96 _ (.inl inside.2) (by omega) (by omega)
  have headerWord (off : Nat) (within : off + 8 ≤ 24) :
      out.mem.read64 (start + BitVec.ofNat 64 off) = header.mem.read64 (start + BitVec.ofNat 64 off) := by
    apply read64_eq_of_cells
    intro j
    have address : start + BitVec.ofNat 64 off + BitVec.ofNat 64 j.val =
        s.reg 19#5 + BitVec.ofNat 64 (8 + off + j.val) := by
      simp only [start, BitVec.ofNat_add, BitVec.add_assoc]
    rw [address, keepFront _ (by have := j.isLt; omega), ← m0]
    apply padFrame
    rw [dst]
    exact outside_span_of_offset _ _ 32 64 (.inl (by have := j.isLt; omega)) (by decide)
      (by have := j.isLt; omega)
  obtain ⟨size, offsetWord, countWord⟩ := inner_header_values s count
  have sizeReal : BitVec.ofNat 64 capacity - 8#64 = BitVec.ofNat 64 (capacity - 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt size64,
      Nat.mod_eq_of_lt (by omega : capacity - 8 < 2 ^ 64)]
    change (2 ^ 64 - 8 + capacity) % 2 ^ 64 = capacity - 8
    omega
  have padAddress : start + 24#64 = s.reg 19#5 + 32#64 := by
    change s.reg 19#5 + 8#64 + 24#64 = _
    rw [BitVec.add_assoc]
    rfl
  have copyAddress : start + 88#64 = s.reg 19#5 + 96#64 := by
    change s.reg 19#5 + 8#64 + 88#64 = _
    rw [BitVec.add_assoc]
    rfl
  have padAt (i : Fin 64) : out.mem.read8 (start + 24#64 + BitVec.ofNat 64 i.val) =
      (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.IPAD)[i.val]!.toBitVec := by
    have b := padBytes i
    simp only [Bool.false_eq_true, if_false, keyPointer, dst, ipadMask, m0] at b
    have keySame : header.mem.read8 (s.reg 2#5 + BitVec.ofNat 64 i.val) =
        s.mem.read8 (s.reg 2#5 + BitVec.ofNat 64 i.val) := by
      unfold Arm64.Memory.read8
      rw [inner_header_outside _ _ _ (outside 8 24 (by omega) _ (keyAway i))]
    have lane : (0x3636363636363636#64).extractLsb' (8 * (i.val % 8)) 8 = Hmac.IPAD.toBitVec := by
      have all : ∀ j : Fin 8, (0x3636363636363636#64).extractLsb' (8 * j.val) 8 = Hmac.IPAD.toBitVec := by decide +kernel
      exact all ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have hold : out.mem.read8 (s.reg 19#5 + 32#64 + BitVec.ofNat 64 i.val) =
        padded.mem.read8 (s.reg 19#5 + 32#64 + BitVec.ofNat 64 i.val) := by
      unfold Arm64.Memory.read8
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, keepFront _ (by have := i.isLt; omega)]
    rw [padAddress, hold, b, keySame, keyAt i, lane]
    have fit : i.val < (EthLib.Base.packBytes k0).size := by
      change i.val < k0.toArray.size
      rw [k0.size_toArray]
      exact i.isLt
    rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact fit), Hmac.xorPad_getElem fit]
    rfl
  have payloadAt (i : Fin message.bytes.size) :
      out.mem.read8 (start + 88#64 + BitVec.ofNat 64 i.val) = message.bytes[i.val]!.toBitVec := by
    rw [copyAddress, ← dest, copied _ i.isLt, src, mc, BitVec.add_assoc, ← BitVec.ofNat_add]
    unfold Arm64.Memory.read8
    rw [frameBefore _ (msgAway _ (messageIndex i.val i.isLt))]
    exact value.bytes i
  have maskPC : masked.pc = s.pc + 58#64 := by
    change s.pc + 28#64 + 30#64 = _
    rw [BitVec.add_assoc]
    rfl
  have paddedPC : padded.pc = s.pc + 138#64 := by
    rw [padPC, maskPC, BitVec.add_assoc]
    rfl
  have copierPC : copier.pc = s.pc + 148#64 := by
    change padded.pc + 10#64 = _
    rw [paddedPC, BitVec.add_assoc]
    rfl
  refine ⟨header, masked, padded, copier, tail, out, headerRun, maskRun, pad,
    entry_message_copy_setup padded, word, bytes, pcOut, spOut, scratchOut, macOut, ?_, ?_,
    rfl, maskPC, paddedPC, copierPC, keyPointer, dst,
    (padRegs _ (by decide : (18#5 : Reg) ≠ 31#5)).trans srcPointer, src, dest, num⟩
  · refine encoded_hmac_inner out.mem start message k0 capacity ?_ ?_ ?_ padAt payloadAt
    · have eq : out.mem.read64 start = header.mem.read64 start := by simpa using headerWord 0 (by decide)
      exact eq.trans (size.trans (by rw [sizeAt]; exact sizeReal))
    · have address : start + 8#64 = s.reg 19#5 + 16#64 := by
        change s.reg 19#5 + 8#64 + 8#64 = _
        rw [BitVec.add_assoc]
        rfl
      have same := headerWord 8 (by decide)
      change out.mem.read64 (start + 8#64) = header.mem.read64 (start + 8#64) at same
      rw [same, address]
      exact offsetWord
    · have address : start + 16#64 = s.reg 19#5 + 24#64 := by
        change s.reg 19#5 + 8#64 + 16#64 = _
        rw [BitVec.add_assoc]
        rfl
      have same := headerWord 16 (by decide)
      change out.mem.read64 (start + 16#64) = header.mem.read64 (start + 16#64) at same
      rw [same, address, countWord]
      change BitVec.ofNat 64 message.bytes.size + 64#64 = _
      rw [BitVec.ofNat_add]
      exact BitVec.add_comm _ _
  · intro p away
    exact (copyFrame p (by rw [dest]; exact withinWritten 96 message.bytes.size (by decide) (by omega) _ away)).trans
      ((congrArg (fun m : Memory => m.cells p) mc).trans (frameBeforeWritten p away))

def entryInnerEvents (base : Addr) (s : CPU) (message : ByteList) : List (List Access) :=
  let text := routineAddress base entry
  innerHeaderEvents (text + 0x46#64) (s.reg 19#5) (s.reg 18#5) ++
    innerMaskEvents (text + 0x62#64) ++
    padEvents 2 (text + 0x80#64) (s.reg 2#5) (s.reg 19#5 + 32#64) 8 ++
    messageCopySetupEvents (text + 0xd0#64) (s.reg 18#5) ++
    copyPayloadEvents (text + 0xda#64) (s.reg 18#5 + BitVec.ofNat 64 message.offset)
      (s.reg 19#5 + 96#64) message.bytes.size

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4500000 in
/-- Fetch the inner-list construction following the key helper's return.
The scratch header, ipad block and message payload use the caller's
independent message, scratch and key-block grants. -/
theorem entry_inner_list_fetched (base : Addr) (s : CPU) (message : ByteList)
    (k0 : HmacKeyBlock) (capacity extent : Nat)
    (pc : s.pc = routineAddress base entry + 0x46#64)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (codeAligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (value : EncodedByteList s.mem (s.reg 18#5) message)
    (sizeAt : s.mem.read64 (s.reg 19#5) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (size64 : capacity < 2 ^ 64)
    (scratchValid : (⟨s.reg 19#5, capacity⟩ : Region).Valid)
    (messageValid : (⟨s.reg 18#5, extent⟩ : Region).Valid)
    (keyValid : (⟨s.reg 2#5, 64⟩ : Region).Valid)
    (scratchMessage : (⟨s.reg 19#5, capacity⟩ : Region).Disjoint ⟨s.reg 18#5, extent⟩)
    (scratchKey : (⟨s.reg 19#5, capacity⟩ : Region).Disjoint ⟨s.reg 2#5, 64⟩)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 2#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (scratchAligned : (s.reg 19#5).toNat % 8 = 0)
    (messageAligned : (s.reg 18#5).toNat % 8 = 0)
    (keyAligned : (s.reg 2#5).toNat % 8 = 0)
    (scratchRead : s.mem.canRead (s.reg 19#5) capacity = true)
    (scratchWrite : s.mem.canWrite (s.reg 19#5) capacity = true)
    (messageRead : s.mem.canRead (s.reg 18#5) extent = true)
    (keyRead : s.mem.canRead (s.reg 2#5) 64 = true) :
    ∃ out, ProgramExecution base s (entryInnerEvents base s message) out ∧
      (entryInnerEvents base s message).length = 47 + 8 * (message.bytes.size / 8) + 7 * (message.bytes.size % 8) ∧
      out.pc = routineAddress base entry + 0x104#64 ∧ out.reg 2#5 = s.reg 2#5 ∧
      out.reg 19#5 = s.reg 19#5 ∧ out.reg 20#5 = s.reg 20#5 ∧
      EncodedByteList out.mem (s.reg 19#5 + 8#64) (hmacInner message k0 capacity) ∧
      (∀ p, ¬ (regionSlice ⟨s.reg 19#5, capacity⟩ 8 (88 + message.bytes.size)).Contains p →
        out.mem.cells p = s.mem.cells p) := by
  obtain ⟨header, mask, padded, copier, tail, out, writeHeader, maskSetup, writePad,
    copySetup, words, bytes, outPC, outSP, scratch, mac, typed, outside, headerPC, maskPC,
    paddedPC, copierPC, maskSP, maskDst, paddedSrc, src, dst, len⟩ :=
    entry_inner_list s message k0 capacity extent layout accessible value sizeAt room size64
      scratchValid messageValid keyValid scratchMessage scratchKey keyAt
  obtain ⟨_, offsetAlign, offsetFits, bytesFit⟩ := layout
  have belongs : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  have readonly : RoutineReadOnly entry base s.mem := routine_readonly_of_exec exec
  have nextExec {next events} (run : ProgramExecution base s events next) :
      next.mem.canExec (routineAddress base entry) entry.image.size = true :=
    (allPerm_eq_of_perm run.perm _ _ _).trans exec
  have readCapacity : (Access.read (s.reg 19#5) .double).permitted s.mem = true := by
    simpa only [BitVec.add_zero] using
      read_of_grant scratchAligned (by omega) (by decide) scratchRead (off := 0)
  have readCount := read_of_grant messageAligned (by omega : 16 + 8 ≤ extent)
    (by decide) messageRead
  have writeHeaderGrant : s.mem.canWrite (s.reg 19#5) 32 = true :=
    (allPerm_true_iff _ _ _ _).mpr (fun i hi =>
      (allPerm_true_iff _ _ _ _).mp scratchWrite i (by omega))
  obtain ⟨writeHead, na⟩ := run_range_observes belongs writeHeader loaded readonly
    (entry_inner_header_allowed base s pc codeAligned exec readCapacity readCount
      scratchAligned writeHeaderGrant) inner_header_decoded
  obtain ⟨imageA, roA⟩ := writeHead.keeps_routine loaded readonly
  obtain ⟨setupMask, nb⟩ := run_range_observes belongs maskSetup imageA roA
    (entry_ipad_setup_allowed base header
      (by rw [headerPC, pc, BitVec.add_assoc]; rfl) codeAligned (nextExec writeHead)) inner_mask_decoded
  have throughMask := writeHead.append setupMask
  obtain ⟨imageB, roB⟩ := throughMask.keeps_routine loaded readonly
  have padAligned : (mask.reg 29#5).toNat % 8 = 0 := by
    rw [maskDst, BitVec.toNat_add]
    change (((s.reg 19#5).toNat + 32) % 2 ^ 64) % 8 = 0
    omega
  have padWrite : mask.mem.canWrite (mask.reg 29#5) 64 = true := by
    rw [maskDst, (throughMask.permissions _ _).1]
    apply (allPerm_true_iff _ _ _ _).mpr
    intro i hi
    rw [BitVec.add_assoc, ← show BitVec.ofNat 64 32 = 32#64 from rfl, ← BitVec.ofNat_add]
    exact (allPerm_true_iff _ _ _ _).mp scratchWrite (32 + i) (by omega)
  have padRead : mask.mem.canRead (mask.reg 2#5) 64 = true := by
    rw [maskSP]
    exact (throughMask.permissions _ _).2 keyRead
  have padDecode : decodeRange entry 0x80 24 = some (padCode 2#5 2 8) := by decide +kernel
  obtain ⟨writeIpad, nc⟩ := run_range_observes belongs writePad imageB roB
    (pad_range_allowed false base mask (by rw [maskPC, pc, BitVec.add_assoc]; rfl)
      codeAligned (nextExec throughMask) (maskSP.symm ▸ keyAligned) padAligned padRead padWrite) padDecode
  have throughPad := throughMask.append writeIpad
  obtain ⟨imageC, roC⟩ := throughPad.keeps_routine loaded readonly
  have offsetRead : (Access.read (padded.reg 18#5 + 8#64) .double).permitted padded.mem = true := by
    rw [paddedSrc]
    exact read_of_grant messageAligned (by omega) (by decide)
      ((throughPad.permissions _ _).2 messageRead) (off := 8)
  obtain ⟨setupCopy, nd⟩ := run_range_observes belongs copySetup imageC roC
    (entry_message_copy_setup_allowed base padded
      (by rw [paddedPC, pc, BitVec.add_assoc]; rfl) codeAligned (nextExec throughPad) offsetRead) copy_setup_decoded
  have throughSetup := throughPad.append setupCopy
  obtain ⟨imageD, roD⟩ := throughSetup.keeps_routine loaded readonly
  have apart (i : Nat) (visits : i < message.bytes.size) :
      message.bytes.size ≤ (copier.reg 30#5 + BitVec.ofNat 64 i - copier.reg 29#5).toNat := by
    rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add]
    let messageRegion : Region := ⟨s.reg 18#5, extent⟩
    let scratchRegion : Region := ⟨s.reg 19#5, capacity⟩
    let payload := regionSlice scratchRegion 96 message.bytes.size
    have inside := caller_region_contains_offset messageRegion messageValid (message.offset + i) (by
      change message.offset + i < extent
      omega)
    exact caller_outside_delta payload (regionSlice_valid _ _ _ scratchValid room) _
      (fun hit => scratchMessage _ ⟨regionSlice_inside _ _ _ scratchValid room _ hit, inside⟩)
  have copyGrant (w : Bool) (off : Nat) (fits : off + (copyWidth w).bytes ≤ message.bytes.size)
      (align : off % (copyWidth w).bytes = 0) :
      (Access.read (copier.reg 30#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted copier.mem = true ∧
      (Access.write (copier.reg 29#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted copier.mem = true := by
    rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact throughSetup.preserves_copy_accesses _ _ _ (copy_accesses_of_grants
      messageAligned scratchAligned offsetAlign (by decide : 96 % 8 = 0) (by omega) room
      messageRead scratchWrite w off fits align)
  obtain ⟨e, copy, ne, copyTrace⟩ := copy_payload_fetched true base copier tail out message.bytes.size
    (by rw [copierPC, pc, BitVec.add_assoc]; rfl) imageD roD codeAligned (nextExec throughSetup)
    len (by omega) apart copyGrant words bytes
  have headerTrace := inner_header_events s
  have maskTrace := inner_mask_events header
  have copySetupTrace := message_copy_setup_events padded
  simp only [inner_header_decoded, inner_mask_decoded, copy_setup_decoded, Option.getD_some] at headerTrace maskTrace copySetupTrace
  let trace := ((((runOpsEvents ((decodeRange entry 0x46 8).getD []) s ++
    runOpsEvents ((decodeRange entry 0x62 9).getD []) header) ++
    runOpsEvents (padCode 2#5 2 8) mask) ++
    runOpsEvents ((decodeRange entry 0xd0 3).getD []) padded) ++ e)
  have observations : trace = entryInnerEvents base s message := by
    simp only [trace, entryInnerEvents, inner_header_decoded, inner_mask_decoded, copy_setup_decoded,
      Option.getD_some, headerTrace, maskTrace, pad_code_events _ _ _ _ (by decide : (2#5 : Reg) ≠ 31#5),
      copySetupTrace, copyTrace, headerPC, maskPC, paddedPC, copierPC, maskSP, maskDst, paddedSrc,
      src, dst, pc, BitVec.add_assoc, List.append_assoc]
    rfl
  have executed : ProgramExecution base s trace out := throughSetup.append copy
  refine ⟨out, observations ▸ executed, ?_, ?_, outSP, scratch, mac, typed, outside⟩
  · rw [← observations]
    simp only [trace, inner_header_decoded, inner_mask_decoded, copy_setup_decoded, Option.getD_some,
      List.length_append, na, nb, nc, nd, ne]
    omega
  · rw [outPC, pc, BitVec.add_assoc]
    rfl

end Crypto.HMACSHA256.RISCV64
