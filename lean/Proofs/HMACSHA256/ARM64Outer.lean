import Proofs.HMACSHA256.ARM64Pad
import Proofs.HMACSHA256.EncodedByteList

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference
open Crypto.ARM64.Imported (address_delta bv_add_sub_add_left)
open EthLib.Cryptography.Hash

private theorem local_frame (base : Addr) (start size addr : Nat) (i : Fin 8)
    (away : addr + 8 ≤ start ∨ start + size ≤ addr)
    (bounded : start + size < 2 ^ 64) (addrBounded : addr + 8 < 2 ^ 64) :
    size ≤ (base + BitVec.ofNat 64 addr + BitVec.ofNat 64 i.val -
      (base + BitVec.ofNat 64 start)).toNat := by
  have hi := i.isLt
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have same : base + BitVec.ofNat 64 (addr + i.val) - (base + BitVec.ofNat 64 start) =
      BitVec.ofNat 64 (addr + i.val) - BitVec.ofNat 64 start :=
    bv_add_sub_add_left _ _ _
  rw [same, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : addr + i.val < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : start < 2 ^ 64)]
  rcases away with earlier | later <;> omega

private theorem stack_header_memory (s : Arm64.State) :
    finishHeader s = writeWords s.mem (s.sp + 96#64)
      (fun i => if i = 0 then 120#64 else if i = 1 then 24#64 else 96#64) 3 := by
  simp [finishHeader, writeWords, BitVec.add_assoc]

/-- After the inner SHA-256 call, the finishing helper constructs the exact
96-byte SHA-256 input for the outer call, including its existing inner digest. -/
theorem finish_outer_bytes (s : Arm64.State) (keyBlock : HmacKeyBlock) (inner : Digest)
    (align : s.spAligned = true)
    (headerWrite : ∀ i : Fin 3,
      s.mem.canWrite (s.sp + 96#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (padWrite : ∀ i : Fin 8,
      s.mem.canWrite (s.sp + 120#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (keyRead : ∀ i : Fin 8,
      s.mem.canRead (s.readReg64 .x19 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (keyOutsideHeader : ∀ i : Fin 64,
      24 ≤ (s.readReg64 .x19 + BitVec.ofNat 64 i.val - (s.sp + 96#64)).toNat)
    (keyOutsidePad : ∀ i : Fin 64,
      64 ≤ (s.readReg64 .x19 + BitVec.ofNat 64 i.val - (s.sp + 120#64)).toNat)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.readReg64 .x19 + BitVec.ofNat 64 i.val) =
      (keyBlock[i.val]).toBitVec)
    (innerAt : ∀ i : Fin 32, s.mem.read8 (s.sp + 184#64 + BitVec.ofNat 64 i.val) =
      (inner[i.val]).toBitVec) :
    ∃ header prepared out,
      runRange finish 0x2c 6 s = some header ∧
      runRange finish 0x44 4 header = some prepared ∧
      runRange finish 0x54 16 prepared = some out ∧
      out.mem.read64 (s.sp + 96#64) = 120#64 ∧
      out.mem.read64 (s.sp + 104#64) = 24#64 ∧
      out.mem.read64 (s.sp + 112#64) = 96#64 ∧
      (∀ i : Fin 64, out.mem.read8 (s.sp + 120#64 + BitVec.ofNat 64 i.val) =
        (Hmac.xorPad (EthLib.Base.packBytes keyBlock) Hmac.OPAD)[i.val]!.toBitVec) ∧
      (∀ i : Fin 32, out.mem.read8 (s.sp + 184#64 + BitVec.ofNat 64 i.val) =
        (inner[i.val]).toBitVec) ∧
      out.sp = s.sp ∧ out.status = s.status ∧ out.pc = s.pc + 104#64 ∧ out.readReg64 .x20 = s.readReg64 .x20 ∧
      (∀ p, 24 ≤ (p - (s.sp + 96#64)).toNat → 64 ≤ (p - (s.sp + 120#64)).toNat →
        out.mem.cells p = s.mem.cells p) := by
  let header := ((s.setMem (finishHeader s)).writeReg64 .x9 96#64).setPC (s.pc + 24#64)
  let prepared := opadStart header
  have built : runRange finish 0x2c 6 s = some header := finish_header s align
    (by simpa using headerWrite ⟨0, by decide⟩)
    (by simpa [BitVec.add_assoc] using headerWrite ⟨1, by decide⟩)
    (by simpa [BitVec.add_assoc] using headerWrite ⟨2, by decide⟩)
  have mem : prepared.mem = finishHeader s := rfl
  have dest : prepared.readReg64 .x8 = s.sp + 120#64 := by
    simp [prepared, opadStart, Arm64.Reg.x8]
    rfl
  have src : prepared.readReg64 .x19 = s.readReg64 .x19 := by
    simp (config := { decide := true }) [prepared, header, opadStart, Arm64.Reg.x19,
      Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x11]
  have mask : prepared.readReg64 .x11 = 0x5c5c5c5c5c5c5c5c#64 := by
    simp (config := { decide := true }) [prepared, opadStart, Arm64.Reg.x8, Arm64.Reg.x11]
  have readAfter (i : Fin 8) :
      prepared.mem.canRead (prepared.readReg64 .x19 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [mem, src, stack_header_memory]
    exact writeWords_canRead _ _ _ _ _ _ (keyRead i)
  have writeAfter (i : Fin 8) :
      prepared.mem.canWrite (prepared.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [mem, dest, stack_header_memory, writeWords_canWrite]
    exact padWrite i
  have disjoint (i : Fin 64) : 64 ≤
      (prepared.readReg64 .x19 + BitVec.ofNat 64 i.val - prepared.readReg64 .x8).toNat := by
    rw [src, dest]
    exact keyOutsidePad i
  obtain ⟨out, exec, bytes, frame, sp, status, pc, mac⟩ := pad_bytes prepared .x19 (Or.inr rfl) readAfter writeAfter disjoint
  have padded : runRange finish 0x54 16 prepared = some out := by
    rw [if_neg (by decide : Arm64.Reg.x19 ≠ Arm64.Reg.x12)] at exec
    exact exec
  have frameHeader (off : Nat) (below : off + 8 ≤ 120) :
      out.mem.read64 (s.sp + BitVec.ofNat 64 off) =
        (finishHeader s).read64 (s.sp + BitVec.ofNat 64 off) := by
    rw [← mem]
    apply read64_eq_of_cells
    intro i
    apply frame
    rw [dest]
    exact local_frame s.sp 120 64 off i (Or.inl below) (by decide) (by omega)
  obtain ⟨hsize, hoff, hcount⟩ := finish_header_values s
  have progress : out.pc = s.pc + 104#64 := by
    rw [pc]
    change s.pc + 24#64 + 16#64 + 64#64 = _
    simp only [BitVec.add_assoc] <;> rfl
  have keepMac : out.readReg64 .x20 = s.readReg64 .x20 := by
    rw [mac]
    simp (config := { decide := true }) [prepared, header, opadStart, Arm64.Reg.x8, Arm64.Reg.x9,
      Arm64.Reg.x11, Arm64.Reg.x20]
  refine ⟨header, prepared, out, built, opad_setup _, padded, ?_, ?_, ?_, ?_, ?_,
    sp.trans rfl, status.trans rfl, progress, keepMac, ?_⟩
  · exact (frameHeader 96 (by decide)).trans hsize
  · exact (frameHeader 104 (by decide)).trans hoff
  · exact (frameHeader 112 (by decide)).trans hcount
  · intro i
    have padByte := bytes i
    rw [src, dest, mask, mem] at padByte
    have before : (finishHeader s).read8 (s.readReg64 .x19 + BitVec.ofNat 64 i.val) =
        s.mem.read8 (s.readReg64 .x19 + BitVec.ofNat 64 i.val) := by
      unfold Arm64.Memory.read8
      rw [stack_header_memory, writeWords_outside _ _ _ 3 _ (keyOutsideHeader i)]
    have lane : (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * (i.val % 8)) 8 = Hmac.OPAD.toBitVec := by
      let k : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
      have all : ∀ j : Fin 8, (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * j.val) 8 =
          Hmac.OPAD.toBitVec := by decide +kernel
      exact all k
    rw [padByte, before, keyAt i, lane]
    have keyFits : i.val < (EthLib.Base.packBytes keyBlock).size := by
      change i.val < keyBlock.toArray.size
      rw [keyBlock.size_toArray]
      exact i.isLt
    rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact keyFits), Hmac.xorPad_getElem keyFits]
    rfl
  · intro i
    have outsidePad : 64 ≤ (s.sp + 184#64 + BitVec.ofNat 64 i.val - (s.sp + 120#64)).toNat := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have e : s.sp + BitVec.ofNat 64 (184 + i.val) - (s.sp + 120#64) =
          BitVec.ofNat 64 (64 + i.val) := by
        rw [show (184 + i.val) = 120 + (64 + i.val) from by omega, BitVec.ofNat_add,
          ← BitVec.add_assoc, address_delta]
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    have outsideHeader : 24 ≤ (s.sp + 184#64 + BitVec.ofNat 64 i.val - (s.sp + 96#64)).toNat := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have e : s.sp + BitVec.ofNat 64 (184 + i.val) - (s.sp + 96#64) =
          BitVec.ofNat 64 (88 + i.val) := by
        rw [show (184 + i.val) = 96 + (88 + i.val) from by omega, BitVec.ofNat_add,
          ← BitVec.add_assoc, address_delta]
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    have preserve := frame _ (by rw [dest]; exact outsidePad)
    simp only [Arm64.Memory.read8] at *
    rw [preserve, mem, stack_header_memory, writeWords_outside _ _ _ 3 _ outsideHeader]
    exact innerAt i
  · intro p offHeader offPad
    have unchanged := frame p (by rw [dest]; exact offPad)
    rw [mem, stack_header_memory] at unchanged
    exact unchanged.trans (writeWords_outside _ _ _ 3 _ offHeader)

/-- Interpret the finishing helper's decoded outer buffer as the same
ByteList used by the verified SHA-256 caller. -/
theorem finish_outer_list (s : Arm64.State) (keyBlock : HmacKeyBlock) (inner : Digest)
    (align : s.spAligned = true)
    (headerWrite : ∀ i : Fin 3,
      s.mem.canWrite (s.sp + 96#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (padWrite : ∀ i : Fin 8,
      s.mem.canWrite (s.sp + 120#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (keyRead : ∀ i : Fin 8,
      s.mem.canRead (s.readReg64 .x19 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (keyOutsideHeader : ∀ i : Fin 64,
      24 ≤ (s.readReg64 .x19 + BitVec.ofNat 64 i.val - (s.sp + 96#64)).toNat)
    (keyOutsidePad : ∀ i : Fin 64,
      64 ≤ (s.readReg64 .x19 + BitVec.ofNat 64 i.val - (s.sp + 120#64)).toNat)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.readReg64 .x19 + BitVec.ofNat 64 i.val) =
      (keyBlock[i.val]).toBitVec)
    (innerAt : ∀ i : Fin 32, s.mem.read8 (s.sp + 184#64 + BitVec.ofNat 64 i.val) =
      (inner[i.val]).toBitVec) :
    ∃ header prepared out,
      runRange finish 0x2c 6 s = some header ∧
      runRange finish 0x44 4 header = some prepared ∧
      runRange finish 0x54 16 prepared = some out ∧
      out.sp = s.sp ∧ out.status = s.status ∧ out.pc = s.pc + 104#64 ∧ out.readReg64 .x20 = s.readReg64 .x20 ∧
      EncodedByteList out.mem (s.sp + 96#64) (hmacOuter keyBlock inner) ∧
      (∀ p, 24 ≤ (p - (s.sp + 96#64)).toNat → 64 ≤ (p - (s.sp + 120#64)).toNat →
        out.mem.cells p = s.mem.cells p) := by
  obtain ⟨header, prepared, out, head, prep, pad, size, offset, count, bytes, digest, sp, status, pc, mac, frame⟩ :=
    finish_outer_bytes s keyBlock inner align headerWrite padWrite keyRead keyOutsideHeader
      keyOutsidePad keyAt innerAt
  refine ⟨header, prepared, out, head, prep, pad, sp, status, pc, mac, encoded_hmac_outer _ _ _ _ size ?_ ?_ ?_ ?_, frame⟩
  · rw [BitVec.add_assoc]
    exact offset
  · rw [BitVec.add_assoc]
    exact count
  · intro i
    rw [BitVec.add_assoc s.sp]
    exact bytes i
  · intro i
    rw [BitVec.add_assoc s.sp]
    exact digest i

end Crypto.HMACSHA256.ARM64
