import Proofs.HMACSHA256.RISCV64OuterSetup
import Proofs.HMACSHA256.EncodedByteList

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells writeWords_perm writeWords_canRead)
open EthLib.Cryptography.Hash

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4500000 in
/-- From the state returned by the inner hash, the decoded finishing helper
constructs the typed ByteList for the outer hash. The register frame keeps
the MAC pointer and the stack base for the second call. -/
theorem finish_outer_list (s : CPU) (k0 : HmacKeyBlock) (inner : Digest)
    (keyOutsideHeader : ∀ i : Fin 64,
      24 ≤ (s.reg 9#5 + BitVec.ofNat 64 i.val - s.reg 2#5).toNat)
    (keyOutsidePad : ∀ i : Fin 64,
      64 ≤ (s.reg 9#5 + BitVec.ofNat 64 i.val - (s.reg 2#5 + 24#64)).toNat)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 9#5 + BitVec.ofNat 64 i.val) = (k0[i.val]).toBitVec)
    (innerAt : ∀ i : Fin 32, s.mem.read8 (s.reg 2#5 + 88#64 + BitVec.ofNat 64 i.val) =
      (inner[i.val]).toBitVec) :
    ∃ header masked out,
      runRange finish 0x26 6 s = some header ∧
      runRange finish 0x36 9 header = some masked ∧
      runRange finish 0x54 24 masked = some out ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.reg 18#5 = s.reg 18#5 ∧
      out.pc = s.pc + 142#64 ∧ EncodedByteList out.mem (s.reg 2#5) (hmacOuter k0 inner) ∧
      (∀ p, 88 ≤ (p - s.reg 2#5).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ p, out.mem.perm p = s.mem.perm p) ∧
      (∀ p n, s.mem.canRead p n = true → out.mem.canRead p n = true) := by
  let header : CPU := { s.put 5#5 96#64 with pc := s.pc + 16#64, mem := finishHeader s }
  let masked := outerMaskState header
  have memory : masked.mem = finishHeader s := rfl
  have hreg (r : Reg) (nz : r ≠ 0) (preserve : r ≠ 5#5) : header.reg r = s.reg r := by
    change (s.put 5#5 96#64).reg r = _
    rw [reg_put, if_neg nz, if_neg preserve]
  have mreg (r : Reg) (nz : r ≠ 0) (a : r ≠ 29#5) (b : r ≠ 28#5) (c : r ≠ 5#5) :
      masked.reg r = s.reg r := by
    unfold masked outerMaskState
    rw [reg_advance, reg_put, if_neg nz, if_neg a, reg_put, if_neg nz, if_neg b]
    exact hreg r nz c
  have src : masked.reg 9#5 = s.reg 9#5 := mreg _ (by decide) (by decide) (by decide) (by decide)
  have sp : masked.reg 2#5 = s.reg 2#5 := mreg _ (by decide) (by decide) (by decide) (by decide)
  have mac : masked.reg 18#5 = s.reg 18#5 := mreg _ (by decide) (by decide) (by decide) (by decide)
  have dest : masked.reg 29#5 = s.reg 2#5 + 24#64 := by
    unfold masked outerMaskState
    rw [reg_advance, reg_put, if_neg (by decide : (29#5 : Reg) ≠ 0), if_pos rfl,
      hreg _ (by decide) (by decide)]
  have mask : masked.reg 28#5 = 0x5c5c5c5c5c5c5c5c#64 := by
    unfold masked outerMaskState
    rw [reg_advance, reg_put, if_neg (by decide : (28#5 : Reg) ≠ 0),
      if_neg (by decide : 28#5 ≠ 29#5), reg_put, if_neg (by decide : (28#5 : Reg) ≠ 0), if_pos rfl]
  have sep : ∀ i : Fin 64, 64 ≤ (masked.reg 9#5 + BitVec.ofNat 64 i.val - masked.reg 29#5).toNat := by
    intro i
    rw [src, dest]
    exact keyOutsidePad i
  obtain ⟨out, built, bytes, frame, regs, pc, perm, readable⟩ := pad_run masked true sep
  refine ⟨header, masked, out, finish_header s, outer_mask header, built,
    (regs _ (by decide)).trans sp, (regs _ (by decide)).trans mac, ?_, ?_, ?_, ?_, ?_⟩
  · have atMask : masked.pc = s.pc + 46#64 := by
      simp [masked, outerMaskState, header, BitVec.add_assoc]
    rw [pc, atMask, BitVec.add_assoc]
    rfl
  · have hword (off : Nat) (before : off + 8 ≤ 24) :
        out.mem.read64 (s.reg 2#5 + BitVec.ofNat 64 off) =
          (finishHeader s).read64 (s.reg 2#5 + BitVec.ofNat 64 off) := by
      rw [← memory]
      apply read64_eq_of_cells
      intro i
      apply frame
      rw [dest, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact outside_span_of_offset _ _ 24 64 (Or.inl (by have := i.isLt; omega))
        (by decide) (by have := i.isLt; omega)
    have ⟨size, offset, count⟩ := finish_header_values s
    have bytePad (i : Fin 64) :
        out.mem.read8 (s.reg 2#5 + 24#64 + BitVec.ofNat 64 i.val) =
          (Hmac.xorPad (EthLib.Base.packBytes k0) Hmac.OPAD)[i.val]!.toBitVec := by
      have b := bytes i
      simp only [if_true, src, dest, mask, memory] at b
      have same : (finishHeader s).read8 (s.reg 9#5 + BitVec.ofNat 64 i.val) =
          s.mem.read8 (s.reg 9#5 + BitVec.ofNat 64 i.val) := by
        unfold Arm64.Memory.read8
        rw [finish_header_outside _ _ (keyOutsideHeader i)]
      rw [b, same, keyAt i, opad_lane]
      have fit : i.val < (EthLib.Base.packBytes k0).size := by
        change i.val < k0.toArray.size
        rw [k0.size_toArray]
        exact i.isLt
      rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact fit), Hmac.xorPad_getElem fit]
      rfl
    have byteInner (i : Fin 32) :
        out.mem.read8 (s.reg 2#5 + 88#64 + BitVec.ofNat 64 i.val) = (inner[i.val]).toBitVec := by
      have opad : 64 ≤ (s.reg 2#5 + 88#64 + BitVec.ofNat 64 i.val - masked.reg 29#5).toNat := by
        rw [dest, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact outside_span_of_offset _ (88 + i.val) 24 64 (Or.inr (by omega)) (by decide)
          (by have := i.isLt; omega)
      have ohdr : 24 ≤ (s.reg 2#5 + 88#64 + BitVec.ofNat 64 i.val - s.reg 2#5).toNat := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Crypto.ARM64.Imported.address_delta,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
        omega
      unfold Arm64.Memory.read8
      rw [frame _ opad, memory, finish_header_outside _ _ ohdr]
      exact innerAt i
    have h0 := hword 0 (by decide)
    have addr0 : s.reg 2#5 + BitVec.ofNat 64 0 = s.reg 2#5 := BitVec.add_zero _
    rw [addr0] at h0
    exact encoded_hmac_outer out.mem (s.reg 2#5) k0 inner
      (h0.trans size) ((hword 8 (by decide)).trans offset)
      ((hword 16 (by decide)).trans count) bytePad byteInner
  · intro p outside
    have bound : 64 ≤ (p - masked.reg 29#5).toNat := by
      rw [dest, ← BitVec.sub_sub, BitVec.toNat_sub]
      have within := (p - s.reg 2#5).isLt
      change 64 ≤ (2 ^ 64 - 24 + (p - s.reg 2#5).toNat) % 2 ^ 64
      omega
    rw [frame _ bound, memory, finish_header_outside _ _ (by omega)]
  · intro p
    rw [perm, memory, finish_header_memory, writeWords_perm]
  · intro p n read
    apply readable
    rw [memory, finish_header_memory]
    exact writeWords_canRead _ _ _ _ _ _ read

end Crypto.HMACSHA256.RISCV64
