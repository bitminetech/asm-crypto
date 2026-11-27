import Proofs.HMACSHA256.X86Pad
import Proofs.HMACSHA256.EncodedByteList
import X86.Theorems

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.Reference EthLib.Cryptography.Hash
open Crypto.X86_64 (byteView byteView_read byteView_write64)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells writeWords writeWords_outside writeWords_word)

private def headerWord (i : Nat) : Val := if i = 0 then 120#64 else if i = 1 then 24#64 else 96#64

private theorem header_memory (s : Cpu) :
    byteView (finishHeader s) = writeWords (byteView s.mem) (s.regs.get .rsp) headerWord 3 := by
  simp [finishHeader, byteView_write64, writeWords, headerWord]

theorem opad_mask_decoded :
    decodeRange finish 0x3b 1 = some [⟨.mov .q (.reg .r8) (.imm 0x5c5c5c5c5c5c5c5c#64), 10⟩] := by
  decide +kernel

def outerMaskState (s : Cpu) : Cpu := {
  s with regs := s.regs.set .r8 0x5c5c5c5c5c5c5c5c#64, rip := s.rip + 10#64 }

theorem mov_mask (s : Cpu) (v : Val) (live : s.ms = none) :
    X86.step ⟨.mov .q (.reg .r8) (.imm v), 10⟩ s =
      { s with regs := s.regs.set .r8 v, rip := s.rip + 10#64 } := by
  rw [X86.step_mov_reg_imm .q .r8 v live, Value.writeView_q, q_trunc]

private theorem opad_mask (s : Cpu) (live : s.ms = none) :
    runRange finish 0x3b 1 s = some (outerMaskState s) := by
  unfold runRange
  rw [opad_mask_decoded]
  change some (X86.step ⟨.mov .q (.reg .r8) (.imm 0x5c5c5c5c5c5c5c5c#64), 10⟩ s) = _
  rw [mov_mask _ _ live]
  rfl

set_option maxHeartbeats 1700000 in
/-- The finishing helper writes the outer hash's typed input using the
linked x86-64 header, mask and pad instructions. The inner digest written
by the first hash stays in the final 32 bytes of that input. -/
theorem finish_outer_list (s : Cpu) (k0 : HmacKeyBlock) (inner : Digest) (live : s.ms = none)
    (keyOffHeader : ∀ i : Fin 64, 24 ≤ (s.regs.get .rbx + BitVec.ofNat 64 i.val - s.regs.get .rsp).toNat)
    (keyOffPad : ∀ i : Fin 64, 64 ≤
      (s.regs.get .rbx + BitVec.ofNat 64 i.val - (s.regs.get .rsp + 24#64)).toNat)
    (keyAt : ∀ i : Fin 64, s.mem.read (s.regs.get .rbx + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (innerAt : ∀ i : Fin 32, s.mem.read (s.regs.get .rsp + 88#64 + BitVec.ofNat 64 i.val) =
      inner[i.val].toBitVec) :
    ∃ header masked out,
      runRange finish 0x21 3 s = some header ∧
      runRange finish 0x3b 1 header = some masked ∧ runRange finish 0x45 24 masked = some out ∧
      out.ms = none ∧ out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rbp = s.regs.get .rbp ∧
      out.rip = s.rip + 131#64 ∧
      EncodedByteList (byteView out.mem) (s.regs.get .rsp) (hmacOuter k0 inner) ∧
      (∀ p, 88 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p) := by
  let stack := s.regs.get .rsp
  let header : Cpu := { s with mem := finishHeader s, rip := s.rip + 26#64 }
  let masked := outerMaskState header
  have maskMem : masked.mem = finishHeader s := rfl
  have maskLive : masked.ms = none := live
  have rb (r : GPR) (keep : r ≠ .r8) : masked.regs.get r = s.regs.get r := by
    exact Regs.get_set_ne _ _ _ _ (Ne.symm keep)
  have dst : padDestination masked true = stack + 24#64 := by
    change masked.regs.get .rsp + 24#64 = _
    rw [rb _ (by decide)]
  have maskReg : masked.regs.get .r8 = 0x5c5c5c5c5c5c5c5c#64 := by
    simp only [masked, outerMaskState, Regs.get_set_same]
  have separate : ∀ i : Fin 64, 64 ≤
      (masked.regs.get .rbx + BitVec.ofNat 64 i.val - padDestination masked true).toNat := by
    intro i
    rw [dst, rb .rbx (by decide)]
    exact keyOffPad i
  obtain ⟨out, run, bytes, frame, outLive, regs, pc⟩ := pad_run masked true maskLive separate
  change runRange finish 0x45 24 masked = some out at run
  have word (i : Nat) (within : i < 3) :
      (byteView out.mem).read64 (stack + BitVec.ofNat 64 (8 * i)) = headerWord i := by
    calc
      _ = (byteView masked.mem).read64 (stack + BitVec.ofNat 64 (8 * i)) := by
        apply read64_eq_of_cells
        intro j
        let address := stack + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j.val
        have away : 64 ≤ (address - padDestination masked true).toNat := by
          change 64 ≤ (stack + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j.val -
            padDestination masked true).toNat
          rw [dst, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact outside_span_of_offset _ _ 24 64 (.inl (by have := j.isLt; omega)) (by decide)
            (by have := j.isLt; omega)
        exact congrArg (fun byte => some (none, byte)) (frame address away)
      _ = _ := by
        rw [maskMem, header_memory]
        exact writeWords_word _ _ _ 3 i within (by decide)
  have outPC : out.rip = s.rip + 131#64 := by
    rw [pc]
    change s.rip + 26#64 + 10#64 + 95#64 = _
    simp only [BitVec.add_assoc] <;> rfl
  refine ⟨header, masked, out, finish_header s live, opad_mask header live, run,
    outLive, (regs _ (by decide)).trans (rb _ (by decide)), (regs _ (by decide)).trans (rb _ (by decide)), outPC,
    encoded_hmac_outer _ _ _ _ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · simpa [headerWord] using word 0 (by decide)
  · exact word 1 (by decide)
  · exact word 2 (by decide)
  · intro i
    have b := bytes i
    change _ = masked.mem.read (masked.regs.get .rbx + BitVec.ofNat 64 i.val) ^^^ _ at b
    have keyUnchanged : (byteView (finishHeader s)).read8 (s.regs.get .rbx + BitVec.ofNat 64 i.val) =
        (byteView s.mem).read8 (s.regs.get .rbx + BitVec.ofNat 64 i.val) := by
      rw [header_memory]
      unfold Arm64.Memory.read8
      rw [writeWords_outside _ _ _ 3 _ (keyOffHeader i)]
    rw [dst, rb .rbx (by decide), maskReg, maskMem, ← byteView_read (finishHeader s), keyUnchanged,
      byteView_read, keyAt, opad_lane] at b
    rw [byteView_read, b]
    have fit : i.val < (EthLib.Base.packBytes k0).size := by
      change i.val < k0.toArray.size
      rw [k0.size_toArray]
      exact i.isLt
    rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact fit), Hmac.xorPad_getElem fit]
    rfl
  · intro i
    have padOutside : 64 ≤ (stack + 88#64 + BitVec.ofNat 64 i.val - padDestination masked true).toNat := by
      rw [dst, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact outside_span_of_offset _ (88 + i.val) 24 64 (.inr (by omega)) (by decide)
        (by have := i.isLt; omega)
    have headerOutside : 24 ≤ (stack + 88#64 + BitVec.ofNat 64 i.val - stack).toNat := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Crypto.ARM64.Imported.address_delta,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    rw [byteView_read, frame _ padOutside, maskMem, ← byteView_read (finishHeader s), header_memory]
    unfold Arm64.Memory.read8
    rw [writeWords_outside _ _ _ 3 _ headerOutside]
    exact innerAt i

  · intro p outside
    have outsidePad : 64 ≤ (p - padDestination masked true).toNat := by
      rw [dst, ← BitVec.sub_sub, BitVec.toNat_sub]
      have bound := (p - stack).isLt
      change 88 ≤ (p - stack).toNat at outside
      change 64 ≤ ((2 ^ 64 - 24 + (p - stack).toNat) % 2 ^ 64)
      omega
    rw [frame p outsidePad, maskMem, ← byteView_read (finishHeader s), header_memory]
    unfold Arm64.Memory.read8
    have headerOutside : 24 ≤ (p - stack).toNat := Nat.le_trans (by decide : 24 ≤ 88) outside
    rw [writeWords_outside _ _ _ 3 _ headerOutside]
    rfl

end Crypto.HMACSHA256.X86_64
