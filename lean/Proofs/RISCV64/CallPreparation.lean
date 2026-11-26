import Proofs.RISCV64.CallEntry
import Proofs.RISCV64.PaddingMemory
import Proofs.RISCV64.TailCopy
import Proofs.ARM64.ImportedReferenceLayout

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (lengthOffset lengthOffset_bounds paddingBlockCount region_store_delta wordVector)
open SHS.Equiv.SHA256.Padding.Layout (implPaddedBytes)

private theorem marker_keeps (n : Nat) (r : Reg)
    (yes : (markerCode 0).all (fun i => i.op.destination != some r) = true)
    (no : (markerCode 56).all (fun i => i.op.destination != some r) = true) :
    (markerCode n).all (fun i => i.op.destination != some r) = true := by
  by_cases h : n < 56
  · simpa [markerCode, h] using yes
  · simpa [markerCode, h] using no

structure PaddingPrepared (base : Addr) (s start marked out : CPU) (data : ByteArray) : Prop where
  pc : out.pc = base + 0xc8
  markerCount : marked.reg 16 = BitVec.ofNat 64 (paddingBlockCount data)
  markerBase : marked.reg 29 = entryStack s + 288
  blocks : out.reg 16 = BitVec.ofNat 64 (paddingBlockCount data)
  kept : ∀ r ∈ ([1, 2, 11, 12, 13] : List Reg), out.reg r = start.reg r
  bytes : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
    out.mem.read8 (entryStack s + 288 + BitVec.ofNat 64 i.val) =
      ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec
  cells : CellFrame out.mem start.mem (entryStack s + 288) 128

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem prepare_padding (base : Addr) (s start : CPU) (data : ByteArray)
    (entry : CallEntry base s data) (input : InputPrepared base s data start) :
    ∃ copied marked out,
      ImageExecution base start (tailCode (data.size % 64)) copied ∧
      ImageExecution base copied (markerCode (data.size % 64)) marked ∧
      ImageExecution base marked lengthSuffix out ∧ PaddingPrepared base s start marked out data := by
  let rem := data.size % 64
  let dst := entryStack s + 288
  have small : rem < 64 := Nat.mod_lt _ (by decide)
  have index (i : Nat) (hi : i < rem) : data.size / 64 * 64 + i < data.size := by
    dsimp [rem] at hi
    have := Nat.div_add_mod data.size 64
    omega
  have inputAddr (i : Nat) :
      start.reg 28 + BitVec.ofNat 64 i =
        inputPayload s + BitVec.ofNat 64 (data.size / 64 * 64 + i) := by
    rw [input.tail, inputTail, BitVec.add_assoc, ← BitVec.ofNat_add]
  have apart (i : Fin rem) : 128 ≤ (start.reg 28 + BitVec.ofNat 64 i.val - start.reg 29).toNat := by
    rw [inputAddr, input.pad]
    exact region_store_delta (entryStack s) _ 288 480 128 (by decide)
      (entry.inputOutside ⟨_, index i.val i.isLt⟩)
  obtain ⟨copied, copy, copyPc, copiedBytes, copyCells⟩ :=
    tail_copied base start rem small input.pc input.cursor input.rem apart
  have sameRem : copied.reg 7#5 = BitVec.ofNat 64 rem :=
    (copy.register_checked 7 (tail_keeps _ 7 (by decide))).trans input.rem
  have sameCount : copied.reg 6#5 = BitVec.ofNat 64 data.size :=
    (copy.register_checked 6 (tail_keeps _ 6 (by decide))).trans input.count
  have samePad : copied.reg 29#5 = dst :=
    (copy.register_checked 29 (tail_keeps _ 29 (by decide))).trans input.pad
  obtain ⟨marked, marker, markPc, blocks, count, ptr, markMem⟩ :=
    marker_loaded base copied rem small copyPc sameRem
  let out := run lengthSuffix marked
  obtain ⟨len, pos, lenMem⟩ := length_suffix_loaded base marked rem markPc blocks
  have rawMark : marked.mem = copied.mem.write8 (dst + BitVec.ofNat 64 rem) 128 := by
    rw [markMem, samePad]
  have rawLen : out.mem =
      writeLength marked.mem (dst + BitVec.ofNat 64 (lengthOffset rem))
        (BitVec.ofNat 64 data.size <<< (3 : Nat)) := by
    change (run lengthSuffix marked).mem = _
    rw [lenMem, ptr, samePad, count, sameCount]
  have copiedVal (i : Fin rem) : copied.mem.read8 (dst + BitVec.ofNat 64 i.val) =
      (data.get! (data.size / 64 * 64 + i.val)).toBitVec := by
    dsimp only [dst]
    rw [← input.pad]
    rw [copiedBytes _ i.isLt, inputAddr]
    refine (read8_same _ (input.cells _ (entry.inputOutside ⟨_, index i.val i.isLt⟩))).trans ?_
    exact entry.inputBytes ⟨_, index i.val i.isLt⟩
  have zeroVal (i : Fin 128) (le : rem ≤ i.val) :
      copied.mem.read8 (dst + BitVec.ofNat 64 i.val) = 0 := by
    have cell : copied.mem.cells (dst + BitVec.ofNat 64 i.val) =
        start.mem.cells (dst + BitVec.ofNat 64 i.val) := by
      apply copyCells
      rw [input.pad]
      change rem ≤ (dst + BitVec.ofNat 64 i.val - dst).toNat
      rwa [Crypto.ARM64.Imported.address_delta, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    exact (read8_same _ cell).trans (input.zero i)
  have markCount : marked.reg 16 = BitVec.ofNat 64 (paddingBlockCount data) :=
    blocks.trans (by unfold paddingBlockCount; dsimp [rem]; split <;> rfl)
  refine ⟨copied, marked, out, copy, marker, len, ⟨pos, markCount, ptr.trans samePad, ?_, ?_, ?_, ?_⟩⟩
  · have keeps := len.register_checked 16 (by decide)
    exact keeps.trans markCount
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (len.register_checked _ (by decide)).trans
        ((marker.register_checked _ (marker_keeps _ _ (by decide) (by decide))).trans
          (copy.register_checked _ (tail_keeps _ _ (by decide))))
  · intro i
    rw [rawLen, rawMark]
    exact padding_bytes copied.mem dst data entry.bound copiedVal zeroVal i
  · have lenFrame : CellFrame out.mem marked.mem dst 128 := by
      rw [rawLen]
      exact length_frame _ _ _ _ small
    have markFrame : CellFrame marked.mem copied.mem dst 128 := by
      rw [rawMark]
      exact marker_frame _ _ _ (by omega)
    exact lenFrame.trans (markFrame.trans (fun p hp =>
      copyCells p (by rw [input.pad]; exact Nat.le_trans (by omega : rem ≤ 128) hp)))

private theorem loaded_initial_words (base : Addr) (m : Memory) (loaded : ImageLoaded base m) :
    wordVector 8 m (base + BitVec.ofNat 64 initialHashOffset) = SHS.SHA256.H0_256 := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, loaded_word _ _ loaded]
  · have table := congrArg (fun v : Vector Word 8 => v[i]) image_constants.2
    simpa only [Vector.getElem_ofFn] using table
  · have size : image.size = 0x540 := by decide +kernel
    rw [size]
    change 0x520 + 4*i + 4 ≤ 0x540
    omega

structure BodyPrepared (base : Addr) (s body : CPU) (data : ByteArray) : Prop where
  pc : body.pc = base + 0xf2
  phase : body.reg 14 = 0
  count : body.reg 13 = BitVec.ofNat 64 (data.size / 64)
  blocks : body.reg 16 = BitVec.ofNat 64 (paddingBlockCount data)
  sp : body.reg 2 = entryStack s
  input : body.reg 12 = inputPayload s
  output : body.reg 11 = s.reg 11
  ret : body.reg 1 = s.reg 1
  constants : body.reg 10 = base + BitVec.ofNat 64 constantsOffset
  loaded : ImageLoaded base body.mem
  iv : storedHash body = SHS.SHA256.H0_256
  inputBytes : ∀ i : Fin data.size, body.mem.read8 (inputPayload s + BitVec.ofNat 64 i.val) =
    (data.get! i.val).toBitVec
  paddingBytes : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
    body.mem.read8 (entryStack s + 288 + BitVec.ofNat 64 i.val) =
      ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec
  cells : CellFrame body.mem s.mem (entryStack s) 480
  spills : CellFrame body.mem (spilled s (entryStack s)) (entryStack s) 416

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem prepare_body (base : Addr) (s start : CPU) (data : ByteArray)
    (entry : CallEntry base s data) (input : InputPrepared base s data start) :
    ∃ copied marked padded body,
      ImageExecution base start (tailCode (data.size % 64)) copied ∧
      ImageExecution base copied (markerCode (data.size % 64)) marked ∧
      ImageExecution base marked lengthSuffix padded ∧
      ImageExecution base padded initialHashCode body ∧ BodyPrepared base s body data ∧
        PaddingPrepared base s start marked padded data := by
  obtain ⟨copied, marked, padded, copy, marker, len, h⟩ := prepare_padding base s start data entry input
  let body := run initialHashCode padded
  obtain ⟨init, pos, constants, phase, stack, mem⟩ := initial_tables base padded h.pc
  have padSp : padded.reg 2 = entryStack s := (h.kept 2 (by decide)).trans input.sp
  have bodySp : body.reg 2 = entryStack s := stack.trans padSp
  have copiedMem : body.mem =
      copyInitialHash padded.mem (base + BitVec.ofNat 64 initialHashOffset) (entryStack s + 256) := by
    change (run initialHashCode padded).mem = _
    rw [mem, padSp]
  have padFrame : CellFrame padded.mem start.mem (entryStack s) 416 :=
    h.cells.enclose (off := 288) (by decide)
  have initFrame : CellFrame body.mem padded.mem (entryStack s) 288 := by
    rw [copiedMem]
    exact (copyInitialHash_frame _ _ _).enclose (off := 256) (by decide)
  have frame : CellFrame body.mem s.mem (entryStack s) 480 :=
    fun p hp => (initFrame p (by omega)).trans ((padFrame p (by omega)).trans (input.cells p hp))
  have padLoaded : ImageLoaded base padded.mem :=
    entry.loaded.of_cells (fun i hi =>
      (padFrame _ (Nat.le_trans (by decide : 416 ≤ 480) (entry.imageOutside i hi))).trans
        (input.cells _ (entry.imageOutside i hi)))
  have riv (i : Fin 32) : 32 ≤
      (base + BitVec.ofNat 64 initialHashOffset + BitVec.ofNat 64 i.val - (entryStack s + 256)).toNat := by
    rw [BitVec.add_assoc base, ← BitVec.ofNat_add]
    have size : image.size = 0x540 := by decide +kernel
    exact region_store_delta (entryStack s) _ 256 480 32 (by decide)
      (entry.imageOutside _ (by rw [size]; change 0x520 + i.val < 0x540; have := i.isLt; omega))
  have initial : storedHash body = SHS.SHA256.H0_256 := by
    unfold storedHash
    rw [bodySp, copiedMem, copyInitialHash_words _ _ _ riv]
    exact loaded_initial_words base padded.mem padLoaded
  refine ⟨copied, marked, padded, body, copy, marker, len, init,
    ⟨pos, phase, (init.register_checked 13 (by decide)).trans ((h.kept 13 (by decide)).trans input.blocks),
      (init.register_checked 16 (by decide)).trans h.blocks, bodySp,
      (init.register_checked 12 (by decide)).trans ((h.kept 12 (by decide)).trans input.source),
      (init.register_checked 11 (by decide)).trans ((h.kept 11 (by decide)).trans input.output),
      (init.register_checked 1 (by decide)).trans ((h.kept 1 (by decide)).trans input.ret),
      constants, entry.loaded.of_cells (fun i hi => frame _ (entry.imageOutside i hi)),
      initial, ?_, ?_, frame, ?_⟩, h⟩
  · intro i
    exact (read8_same _ (frame _ (entry.inputOutside i))).trans (entry.inputBytes i)
  · intro i
    have bound : i.val < 128 := by
      have := i.isLt
      have := lengthOffset_bounds (data.size % 64) (Nat.mod_lt _ (by decide : 0 < 64))
      omega
    have same := initFrame.offset (off := 288) i.val (by omega) (by omega : 288 + i.val < 2^64)
    exact (read8_same _ same).trans (h.bytes i)
  · intro p hp
    exact (initFrame p (by omega)).trans ((padFrame p hp).trans (input.spills p hp))

end Crypto.RISCV64
