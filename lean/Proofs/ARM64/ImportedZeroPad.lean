import Proofs.ARM64.ImportedTailCopy

/-!
The nine recorded padding-zeroing instructions write all 128 bytes to zero.
The exact memory transition, cells outside the padding area, permissions and
modeled state/register frame are proved without constraining old stack bytes.
-/
namespace Crypto.ARM64.Imported

@[simp] theorem canWrite_write64 (m : Arm64.Memory) (base : BitVec 64) (v : BitVec 64)
    (p : BitVec 64) (n : Nat) : (m.write64 base v).canWrite p n = m.canWrite p n := by
  simp [Arm64.Memory.canWrite, Arm64.Memory.write64]

def zeroRegisters (s : Arm64.State) : BitVec 5 → BitVec 64 :=
  fun j => if j = 16#5 then 0 else s.readReg64 (.gpr j)

@[simp] theorem zeroRegs_advance (s : Arm64.State) : zeroRegisters s.advancePC = zeroRegisters s := by funext j; simp [zeroRegisters]
@[simp] theorem zeroRegs_mem (s : Arm64.State) (m : Arm64.Memory) : zeroRegisters (s.setMem m) = zeroRegisters s := by funext j; simp [zeroRegisters]
@[simp] theorem zeroRegs_write16 (s : Arm64.State) (v : BitVec 64) : zeroRegisters (s.writeReg64 .x16 v) = zeroRegisters s := by
  funext j
  by_cases h31 : j = 31#5
  · subst j; simp [zeroRegisters, Arm64.State.readReg64]
  · by_cases h16 : j = 16#5 <;> simp [zeroRegisters, h31, h16]

def zeroPadCode : List (BitVec 32) := (imageWords.toList.drop 4).take 9
private theorem zero_pad_decoded : zeroPadCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x16 .sp 288#12 false,
  .stp .W64 .xzr .xzr (.Offset .x16 0#64),
  .stp .W64 .xzr .xzr (.Offset .x16 16#64),
  .stp .W64 .xzr .xzr (.Offset .x16 32#64),
  .stp .W64 .xzr .xzr (.Offset .x16 48#64),
  .stp .W64 .xzr .xzr (.Offset .x16 64#64),
  .stp .W64 .xzr .xzr (.Offset .x16 80#64),
  .stp .W64 .xzr .xzr (.Offset .x16 96#64),
  .stp .W64 .xzr .xzr (.Offset .x16 112#64)] := by decide +kernel

def zeroPadMemory (s : Arm64.State) : Arm64.Memory :=
  (List.range 16).foldl (fun m i => m.write64 (s.sp + BitVec.ofNat 64 (288 + 8 * i)) 0#64) s.mem

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem zero_padding (s : Arm64.State)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    (runWords zeroPadCode s).map (fun out =>
      (stable out, zeroRegisters out, out.mem, out.pc, nonvolatile out, out.readReg64 .x16)) =
      some ({ stable s with mem := zeroPadMemory s }, zeroRegisters s, zeroPadMemory s,
        s.pc + 36#64, nonvolatile s, s.sp + 288#64) := by
  have w0 := hw ⟨0, by decide⟩
  simp only [BitVec.add_assoc] at w0
  change s.mem.canWrite (s.sp + 288#64) 8 = true at w0
  have w1 := hw ⟨1, by decide⟩
  simp only [BitVec.add_assoc] at w1
  change s.mem.canWrite (s.sp + 296#64) 8 = true at w1
  have w2 := hw ⟨2, by decide⟩
  simp only [BitVec.add_assoc] at w2
  change s.mem.canWrite (s.sp + 304#64) 8 = true at w2
  have w3 := hw ⟨3, by decide⟩
  simp only [BitVec.add_assoc] at w3
  change s.mem.canWrite (s.sp + 312#64) 8 = true at w3
  have w4 := hw ⟨4, by decide⟩
  simp only [BitVec.add_assoc] at w4
  change s.mem.canWrite (s.sp + 320#64) 8 = true at w4
  have w5 := hw ⟨5, by decide⟩
  simp only [BitVec.add_assoc] at w5
  change s.mem.canWrite (s.sp + 328#64) 8 = true at w5
  have w6 := hw ⟨6, by decide⟩
  simp only [BitVec.add_assoc] at w6
  change s.mem.canWrite (s.sp + 336#64) 8 = true at w6
  have w7 := hw ⟨7, by decide⟩
  simp only [BitVec.add_assoc] at w7
  change s.mem.canWrite (s.sp + 344#64) 8 = true at w7
  have w8 := hw ⟨8, by decide⟩
  simp only [BitVec.add_assoc] at w8
  change s.mem.canWrite (s.sp + 352#64) 8 = true at w8
  have w9 := hw ⟨9, by decide⟩
  simp only [BitVec.add_assoc] at w9
  change s.mem.canWrite (s.sp + 360#64) 8 = true at w9
  have w10 := hw ⟨10, by decide⟩
  simp only [BitVec.add_assoc] at w10
  change s.mem.canWrite (s.sp + 368#64) 8 = true at w10
  have w11 := hw ⟨11, by decide⟩
  simp only [BitVec.add_assoc] at w11
  change s.mem.canWrite (s.sp + 376#64) 8 = true at w11
  have w12 := hw ⟨12, by decide⟩
  simp only [BitVec.add_assoc] at w12
  change s.mem.canWrite (s.sp + 384#64) 8 = true at w12
  have w13 := hw ⟨13, by decide⟩
  simp only [BitVec.add_assoc] at w13
  change s.mem.canWrite (s.sp + 392#64) 8 = true at w13
  have w14 := hw ⟨14, by decide⟩
  simp only [BitVec.add_assoc] at w14
  change s.mem.canWrite (s.sp + 400#64) 8 = true at w14
  have w15 := hw ⟨15, by decide⟩
  simp only [BitVec.add_assoc] at w15
  change s.mem.canWrite (s.sp + 408#64) 8 = true at w15
  rw [runWords_decode, zero_pad_decoded]
  simp (config := { decide := true, maxDischargeDepth := 64 }) [runDecoded,
    Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execStp, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.writeSized,
    addWithCarry64_add, BitVec.truncate_eq_setWidth, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    BitVec.add_assoc, zeroPadMemory, List.range_succ]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem zeroPadMemory_byte (s : Arm64.State) (i : Fin 128) :
    (zeroPadMemory s).read8 ((s.sp + 288#64) + BitVec.ofNat 64 i.val) = 0#8 := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    simp (config := { decide := true }) [zeroPadMemory, List.range_succ,
      Arm64.Memory.write64, read8_write8, BitVec.add_assoc]

theorem write64_cells_outside (m : Arm64.Memory) (base p : BitVec 64) (v : BitVec 64)
    (h : 8 ≤ (p - base).toNat) : (m.write64 base v).cells p = m.cells p := by
  have outside (i : Fin 8) : p ≠ base + BitVec.ofNat 64 i.val := by
    intro he
    rw [he, address_delta] at h
    have hi := i.isLt
    have bound : i.val < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at h
    omega
  have h0 : p ≠ base := by simpa using outside ⟨0, by decide⟩
  have h1 : p ≠ base + 1#64 := by simpa using outside ⟨1, by decide⟩
  have h2 : p ≠ base + 2#64 := by simpa using outside ⟨2, by decide⟩
  have h3 : p ≠ base + 3#64 := by simpa using outside ⟨3, by decide⟩
  have h4 : p ≠ base + 4#64 := by simpa using outside ⟨4, by decide⟩
  have h5 : p ≠ base + 5#64 := by simpa using outside ⟨5, by decide⟩
  have h6 : p ≠ base + 6#64 := by simpa using outside ⟨6, by decide⟩
  have h7 : p ≠ base + 7#64 := by simpa using outside ⟨7, by decide⟩
  simp [Arm64.Memory.write64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem byte128_word_delta (base p : BitVec 64) (t : Fin 16)
    (h : 128 ≤ (p - base).toNat) :
    8 ≤ (p - (base + BitVec.ofNat 64 (8 * t.val))).toNat := by
  by_contra hn
  let d := (p - (base + BitVec.ofNat 64 (8 * t.val))).toNat
  have hd : d < 8 := Nat.lt_of_not_ge hn
  have small : 8 * t.val + d < 128 := by have := t.isLt; omega
  have bound : 8 * t.val + d < 2 ^ 64 := by omega
  have address : base + BitVec.ofNat 64 (8 * t.val + d) = p := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact address_reconstruct (base + BitVec.ofNat 64 (8 * t.val)) p
  have dist : (p - base).toNat = 8 * t.val + d := by
    rw [← address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem fold_cells_frame {α : Type} (f : Arm64.Memory → α → Arm64.Memory)
    (xs : List α) (p : BitVec 64)
    (h : ∀ m x, x ∈ xs → (f m x).cells p = m.cells p) (m : Arm64.Memory) :
    (xs.foldl f m).cells p = m.cells p := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    have tail (m : Arm64.Memory) (y : α) (hy : y ∈ xs) : (f m y).cells p = m.cells p :=
      h m y (by simp [hy])
    change (xs.foldl f (f m x)).cells p = m.cells p
    exact (ih tail (f m x)).trans (h m x (by simp))

theorem zeroPadMemory_outside (s : Arm64.State) (p : BitVec 64)
    (h : 128 ≤ (p - (s.sp + 288#64)).toNat) : (zeroPadMemory s).cells p = s.mem.cells p := by
  apply fold_cells_frame
  intro m i hi
  have small : i < 16 := List.mem_range.mp hi
  have dist := byte128_word_delta (s.sp + 288#64) p ⟨i, small⟩ h
  have address : (s.sp + 288#64) + BitVec.ofNat 64 (8 * i) =
      s.sp + BitVec.ofNat 64 (288 + 8 * i) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  rw [address] at dist
  exact write64_cells_outside m _ p 0#64 dist

theorem canRead_write64 (m : Arm64.Memory) (base : BitVec 64) (v : BitVec 64)
    (p : BitVec 64) (n : Nat) (h : m.canRead p n = true) :
    (m.write64 base v).canRead p n = true := by
  unfold Arm64.Memory.write64
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  apply canRead_write8
  exact h

theorem zeroPadMemory_writable (s : Arm64.State) (p : BitVec 64) (n : Nat) :
    (zeroPadMemory s).canWrite p n = s.mem.canWrite p n := by
  simp [zeroPadMemory, List.range_succ]

theorem zeroPadMemory_readable (s : Arm64.State) (p : BitVec 64) (n : Nat)
    (h : s.mem.canRead p n = true) : (zeroPadMemory s).canRead p n = true := by
  simp (config := { maxDischargeDepth := 64 }) [zeroPadMemory, List.range_succ, canRead_write64, h]

end Crypto.ARM64.Imported
