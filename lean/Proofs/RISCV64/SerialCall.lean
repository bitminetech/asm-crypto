import Proofs.RISCV64.CallPreparation
import Proofs.RISCV64.BlockBytes
import Proofs.RISCV64.HashReturn
import Proofs.RISCV64.SavedFrame

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (address_delta address_reconstruct memoryBytes32 paddingBlockCount)

/-- The decoded call path, with the message and padding loops represented by
their block prefixes. The only return segment is the final epilogue. -/
def CallPath (base : Addr) (s out : CPU) (data : ByteArray) : Prop :=
  ∃ frame head clear start copied marked padded body msgMid msgExit switch padInit padMid padExit digest written,
    ImageExecution base s saveFrame frame ∧
    ImageExecution base frame headerBody head ∧
    ImageExecution base head zeroPadding clear ∧
    ImageExecution base clear lengthBody start ∧
    ImageExecution base start (tailCode (data.size % 64)) copied ∧
    ImageExecution base copied (markerCode (data.size % 64)) marked ∧
    ImageExecution base marked lengthSuffix padded ∧
    ImageExecution base padded initialHashCode body ∧
    BlockPathPrefix base body (data.size / 64) msgMid ∧
    ImageExecution base msgMid [blockGuard] msgExit ∧
    ImageExecution base msgExit [phaseGuard] switch ∧
    ImageExecution base switch paddingPhase padInit ∧
    BlockPathPrefix base padInit (paddingBlockCount data) padMid ∧
    ImageExecution base padMid [blockGuard] padExit ∧
    ImageExecution base padExit [phaseGuard] digest ∧
    ImageExecution base digest digestCode written ∧
    ImageExecution base written returnCode out

private theorem stack_outside_output (s : CPU) (p : Addr)
    (outside : ∀ i : Fin 32, 480 ≤ (s.reg 11 + BitVec.ofNat 64 i.val - entryStack s).toNat)
    (insideStack : (p - entryStack s).toNat < 480) :
    32 ≤ (p - s.reg 11).toNat := by
  by_contra h
  let d : Fin 32 := ⟨(p-s.reg 11).toNat, by omega⟩
  have equal : s.reg 11 + BitVec.ofNat 64 d.val = p := address_reconstruct _ _
  have bad := outside d
  rw [equal] at bad
  omega

private theorem stack_offset (s : CPU) (a b : Nat) (bound : a+b < 480) :
    (entryStack s + BitVec.ofNat 64 a + BitVec.ofNat 64 b - entryStack s).toNat = a+b := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, address_delta, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5500000 in
/-- Functional and serial frame result of the linked routine from its public
entry. The instruction path is available for separate permission and
observation proofs. -/
theorem serial_sha256 (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data)
    (outputOutside : ∀ i : Fin 32, 480 ≤ (s.reg 11 + BitVec.ofNat 64 i.val - entryStack s).toNat) :
    ∃ out, CallPath base s out data ∧ out.pc = s.reg 1 &&& ~~~(1 : Addr) ∧
      out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 ∧ savedRegisters out = savedRegisters s ∧
      memoryBytes32 out.mem (s.reg 11) = (Crypto.Reference.digest data).map UInt8.toBitVec ∧
      (∀ p, 480 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.reg 11).toNat →
        out.mem.cells p = s.mem.cells p) := by
  obtain ⟨frame, head, clear, start, save, header, zero, length, args⟩ :=
    input_prepared base s data entry
  obtain ⟨copied, marked, padded, body, copy, marker, suffix, iv, h, _⟩ :=
    prepare_body base s start data entry args
  have codeSep (i : Nat) (hi : i < image.size) : 288 ≤ (base + BitVec.ofNat 64 i - body.reg 2).toNat := by
    rw [h.sp]
    exact Nat.le_trans (by decide) (entry.imageOutside i hi)
  have inputSep : PhaseInputApart body (data.size / 64) := by
    intro i j k
    rw [h.input, h.sp]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    have idx : 64*i.val + 4*j.val + k.val < data.size := by
      have := i.isLt
      have := j.isLt
      have := k.isLt
      omega
    exact Nat.le_trans (show 288 ≤ 480 by decide) (entry.inputOutside ⟨_, idx⟩)
  have outputSep (i : Fin 8) (d : Fin 4) :
      32 ≤ (body.reg 2 + BitVec.ofNat 64 (256+4*i.val) + BitVec.ofNat 64 d.val - body.reg 11).toNat := by
    rw [h.sp, h.output]
    apply stack_outside_output s _ outputOutside
    rw [stack_offset]
    all_goals have := i.isLt; have := d.isLt; omega
  have messageWords (i : Fin (data.size / 64)) :
      blockWords body.mem (body.reg 12 + BitVec.ofNat 64 (64*i.val)) =
        Crypto.ARM64.Imported.paddedSpecBlock data i.val := by
    rw [h.input]
    exact complete_block_bytes _ _ data h.inputBytes i
  have paddingWords (i : Fin (paddingBlockCount data)) :
      blockWords body.mem (body.reg 2 + 288 + BitVec.ofNat 64 (64*i.val)) =
        Crypto.ARM64.Imported.paddedSpecBlock data (data.size / 64 + i.val) := by
    rw [h.sp]
    exact padding_block_bytes _ _ data h.paddingBytes i
  obtain ⟨msgMid, msgExit, switch, padInit, padMid, padExit, digest, written, out,
    message, endedMessage, choosePad, beginPad, padding, endedPad, chooseDigest, write, ret,
    pos, status, sp, bytes, saved, writtenSp, writtenMem, cells⟩ :=
      hash_to_return base body data entry.bound h.pc h.phase h.count h.blocks h.loaded h.constants
        codeSep inputSep outputSep h.iv messageWords paddingWords
  have restoredSp : out.reg 2 = s.reg 2 := by
    rw [sp, h.sp]
    exact BitVec.sub_add_cancel _ _
  have savedBytes (i : Fin 8) (d : Fin 8) :
      written.mem.cells (entryStack s + BitVec.ofNat 64 (416+8*i.val) + BitVec.ofNat 64 d.val) =
        (spilled s (entryStack s)).cells (entryStack s + BitVec.ofNat 64 (416+8*i.val) + BitVec.ofNat 64 d.val) := by
    let p := entryStack s + BitVec.ofNat 64 (416+8*i.val) + BitVec.ofNat 64 d.val
    have range : 416+8*i.val+d.val < 480 := by have := i.isLt; have := d.isLt; omega
    have whereSlot : (p - entryStack s).toNat = 416+8*i.val+d.val := stack_offset s _ _ range
    have apart := stack_outside_output s p outputOutside (by rw [whereSlot]; exact range)
    have forHash : 288 ≤ (p - body.reg 2).toNat := by rw [h.sp, whereSlot]; omega
    have kept := (cells p forHash (by rw [h.output]; exact apart)).trans
      (h.spills p (by rw [whereSlot]; omega))
    rw [writtenMem]
    exact kept
  have restored : savedRegisters out = savedRegisters s := by
    rw [saved, savedStack, writtenSp, h.sp]
    exact (savedStack_of_cells written.mem _ (entryStack s) savedBytes).trans (spilled_registers s _)
  refine ⟨out, ⟨frame, head, clear, start, copied, marked, padded, body, msgMid, msgExit, switch,
    padInit, padMid, padExit, digest, written, save, header, zero, length, copy, marker, suffix, iv,
    message, endedMessage, choosePad, beginPad, padding, endedPad, chooseDigest, write, ret⟩,
    by rw [pos, h.ret], status, restoredSp, restored, ?_, ?_⟩
  · simpa only [h.output] using bytes
  · intro p hp hd
    exact (cells p (by rw [h.sp]; omega) (by rw [h.output]; exact hd)).trans (h.cells p hp)

end Crypto.RISCV64
