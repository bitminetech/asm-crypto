import Proofs.RISCV64.EntryMemory
import Proofs.RISCV64.Preparation
import Proofs.RISCV64.RegisterFrame

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (address_delta fold_cells_frame region_store_delta write64_cells_outside)

def entryStack (s : CPU) : Addr := s.reg 2 - 480

def inputPayload (s : CPU) : Addr := s.reg 10 + s.mem.read64 (s.reg 10 + 8)

def inputTail (s : CPU) (data : ByteArray) : Addr :=
  inputPayload s + BitVec.ofNat 64 (data.size / 64 * 64)

/-- The memory facts used by the serial instruction proof. A caller's layout
and permission proof establishes these facts about the original call state. -/
structure CallEntry (base : Addr) (s : CPU) (data : ByteArray) : Prop where
  pc : s.pc = base
  bound : data.size < 2^61
  loaded : ImageLoaded base s.mem
  countValue : s.mem.read64 (s.reg 10 + 16) = BitVec.ofNat 64 data.size
  headerOutside : ∀ i : Fin 16, 480 ≤ ((s.reg 10 + 8) + BitVec.ofNat 64 i.val - entryStack s).toNat
  imageOutside : ∀ i, i < image.size → 480 ≤ (base + BitVec.ofNat 64 i - entryStack s).toNat
  inputOutside : ∀ i : Fin data.size, 480 ≤ (inputPayload s + BitVec.ofNat 64 i.val - entryStack s).toNat
  inputBytes : ∀ i : Fin data.size, s.mem.read8 (inputPayload s + BitVec.ofNat 64 i.val) =
    (data.get! i.val).toBitVec

private theorem spilled_frame (s : CPU) : CellFrame (spilled s (entryStack s)) s.mem (entryStack s) 480 := by
  intro p hp
  unfold spilled
  apply fold_cells_frame
  intro m slot hs
  have offsets : ∀ slot ∈ savedSlots, slot.2 + 8 ≤ 480 := by decide
  exact write64_cells_outside _ _ _ _ (region_store_delta _ _ _ _ _ (offsets slot hs) hp)

structure InputPrepared (base : Addr) (s : CPU) (data : ByteArray) (out : CPU) : Prop where
  pc : out.pc = base + 0x52
  sp : out.reg 2 = entryStack s
  count : out.reg 6 = BitVec.ofNat 64 data.size
  rem : out.reg 7 = BitVec.ofNat 64 (data.size % 64)
  blocks : out.reg 13 = BitVec.ofNat 64 (data.size / 64)
  tail : out.reg 28 = inputTail s data
  pad : out.reg 29 = entryStack s + 288
  cursor : out.reg 30 = 0
  source : out.reg 12 = inputPayload s
  output : out.reg 11 = s.reg 11
  ret : out.reg 1 = s.reg 1
  zero : ∀ i : Fin 128, out.mem.read8 (entryStack s + 288 + BitVec.ofNat 64 i.val) = 0
  cells : CellFrame out.mem s.mem (entryStack s) 480
  spills : CellFrame out.mem (spilled s (entryStack s)) (entryStack s) 416

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem input_prepared (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data) :
    ∃ frame head clearedState out,
      ImageExecution base s saveFrame frame ∧
      ImageExecution base frame headerBody head ∧
      ImageExecution base head zeroPadding clearedState ∧
      ImageExecution base clearedState lengthBody out ∧ InputPrepared base s data out := by
  let frame := run saveFrame s
  obtain ⟨enter, fp, fs, fm⟩ := frame_entered base s entry.pc
  have frameCells : CellFrame frame.mem s.mem (entryStack s) 480 := by
    change CellFrame (run saveFrame s).mem s.mem (entryStack s) 480
    rw [fm]
    exact spilled_frame s
  have headerByte (off : Nat) (j : Fin 8) (fit : off + 8 ≤ 16) :
      480 ≤ (s.reg 10 + 8 + BitVec.ofNat 64 off + BitVec.ofNat 64 j.val - entryStack s).toNat := by
    rw [BitVec.add_assoc (s.reg 10 + 8), ← BitVec.ofNat_add]
    exact entry.headerOutside ⟨off+j.val, by have := j.isLt; omega⟩
  have r10 : frame.reg 10 = s.reg 10 := enter.register_checked 10 (by decide)
  have offset : frame.mem.read64 (frame.reg 10 + 8) = s.mem.read64 (s.reg 10 + 8) := by
    rw [r10]
    apply read64_same
    intro i
    apply frameCells
    simpa using headerByte 0 i (by decide)
  have count : frame.mem.read64 (frame.reg 10 + 16) = BitVec.ofNat 64 data.size := by
    rw [r10, ← entry.countValue]
    apply read64_same
    intro i
    apply frameCells
    have pos := headerByte 8 i (by decide)
    rw [BitVec.add_assoc (s.reg 10)] at pos
    exact pos
  let head := run headerBody frame
  obtain ⟨readHead, hc, hm, hn, hp⟩ := header_loaded base frame fp
  have payload : head.reg 12 = inputPayload s := by
    change (run headerBody frame).reg 12 = _
    rw [hp, offset, r10]
    rfl
  have headCount : head.reg 6 = BitVec.ofNat 64 data.size := hn.trans count
  let clear := run zeroPadding head
  obtain ⟨zeroed, zp, zs, zm⟩ := padding_cleared base head hc
  let out := run lengthBody clear
  obtain ⟨lengths, lp, lm, lr, lb, lt, lpad, cursor⟩ := lengths_loaded base clear zp
  have headSp : head.reg 2 = entryStack s := (readHead.register_checked 2 (by decide)).trans fs
  have clearSp : clear.reg 2 = entryStack s := zs.trans headSp
  have clearCount : clear.reg 6 = BitVec.ofNat 64 data.size :=
    (zeroed.register_checked 6 (by decide)).trans headCount
  have lengthVal : (clear.reg 6).toNat = data.size := by
    rw [clearCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := entry.bound; omega)]
  have clearPayload : clear.reg 12 = inputPayload s :=
    (zeroed.register_checked 12 (by decide)).trans payload
  have zeroMem : clear.mem = cleared frame.mem (entryStack s + 288) := by
    change (run zeroPadding head).mem = _
    rw [zm, hm, headSp]
  have output := (lengths.register_checked 11 (by decide)).trans
    ((zeroed.register_checked 11 (by decide)).trans
      ((readHead.register_checked 11 (by decide)).trans (enter.register_checked 11 (by decide))))
  have ret := (lengths.register_checked 1 (by decide)).trans
    ((zeroed.register_checked 1 (by decide)).trans
      ((readHead.register_checked 1 (by decide)).trans (enter.register_checked 1 (by decide))))
  have outMem : out.mem = clear.mem := lm
  have padFrame : CellFrame out.mem frame.mem (entryStack s) 416 := by
    rw [outMem, zeroMem]
    exact (cleared_frame _ _).enclose (off := 288) (by decide)
  refine ⟨frame, head, clear, out, enter, readHead, zeroed, lengths,
    ⟨lp, (lengths.register_checked 2 (by decide)).trans clearSp,
      (lengths.register_checked 6 (by decide)).trans clearCount,
      lr.trans (by rw [lengthVal]), lb.trans (by rw [lengthVal]),
      lt.trans (by rw [lengthVal, clearPayload]; rfl),
      lpad.trans (by rw [clearSp]), cursor,
      (lengths.register_checked 12 (by decide)).trans clearPayload, output, ret, ?_, ?_, ?_⟩⟩
  · intro i
    rw [outMem, zeroMem]
    exact cleared_zero _ _ _
  · exact (fun p hp => (padFrame p (by omega)).trans (frameCells p hp))
  · have spills : frame.mem = spilled s (entryStack s) := fm
    rwa [← spills]

end Crypto.RISCV64
