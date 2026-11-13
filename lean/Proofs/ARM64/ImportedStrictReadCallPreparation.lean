import Proofs.ARM64.ImportedStrictReadCallInputs

/-!
Native prologue/preparation with explicit pinned IV/K pool memory values.
The recorded header, padding and hash initialization instructions execute under
RawSHAInputs without full-image data-read or strict CodeLoaded assumptions.
initialize_hash_from_iv uses the existing exact word-copy theorem. The
prepared block guards and imported-reference byte layout are otherwise the
same as the original native SHA-256 proof.
-/
namespace Crypto.ARM64.Imported

theorem initialize_hash_from_iv (base : BitVec 64) (s : Arm64.State)
    (pc : s.pc = base + 132#64)
    (hr : ∀ i : Fin 4, s.mem.canRead ((s.pc + 732#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hw : ∀ i : Fin 4, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (iv : wordVector 8 s.mem (s.pc + 732#64) = SHS.SHA256.H0_256) :
    ∃ out, runWords hashInitCode s = some out ∧
      savedHash out = SHS.SHA256.H0_256 ∧ nonMemory out = nonMemory s ∧
      nonvolatile out = nonvolatile s ∧ out.pc = s.pc + 32#64 ∧
      out.readReg64 .x0 = base + 608#64 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = s.readReg64 .x2 ∧ out.readReg64 .x3 = s.readReg64 .x3 ∧
      out.readReg64 .x4 = 0#64 ∧ out.readReg64 .x6 = s.readReg64 .x6 ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  obtain ⟨out, he, post⟩ := exists_of_map_some _ _ _ (initialize_hash s hr hw)
  simp only [Prod.mk.injEq] at post
  obtain ⟨st, mem, opc, nv, x0, x1, x2, x3, x4, x6⟩ := post
  have sp := congrArg Arm64.State.sp st
  change out.sp = s.sp at sp
  have nm := congrArg nonMemory st
  have state : nonMemory out = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem] using nm
  refine ⟨out, he, ?_, state, nv, opc, ?_, x1, x2, x3, x4, x6, ?_, ?_, ?_⟩
  · unfold savedHash
    rw [mem, sp]
    exact (initialHashMemory_words s).trans iv
  · rw [x0, pc, BitVec.add_assoc]
    rfl
  · intro p hp
    rw [mem]
    exact initialHashMemory_outside s p hp
  · intro a n h
    rw [mem]
    exact initialHashMemory_readable s a n h
  · intro a n
    rw [mem, initialHashMemory_writable]


structure RawPreparedBody (base : BitVec 64) (s : Arm64.State) (data : ByteArray) (body : Arm64.State) : Prop where
  executed : runWords (prologueCode (BitVec.ofNat 64 data.size)) s = some body
  state : returnStable body = returnStable s
  nonvolatile : Crypto.ARM64.Imported.nonvolatile body = Crypto.ARM64.Imported.nonvolatile s
  stack : body.sp = entryStack s
  pc : body.pc = base + 164#64
  output : body.readReg64 .x1 = s.readReg64 .x1
  ready : BlockReady body
  count : body.readReg64 .x3 = BitVec.ofNat 64 (data.size / 64)
  phase : body.readReg64 .x4 = 0#64
  padCount : body.readReg64 .x6 = BitVec.ofNat 64 (paddingBlockCount data)
  fullReads : ∀ (i : Fin (data.size / 64)) (j : Fin 16), body.mem.canRead
    (body.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true
  fullSep : ∀ (i : Fin (data.size / 64)) (j : Fin 16) (b : Fin 4),
    288 ≤ (body.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - body.sp).toNat
  padRead : ∀ i : Fin 32, body.mem.canRead (body.sp + 288#64 + BitVec.ofNat 64 (4 * i.val)) 4 = true
  outWrite : ∀ i : Fin 8, body.mem.canWrite (body.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true
  outSep : ∀ (i : Fin 8) (b : Fin 4),
    288 ≤ (body.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - body.sp).toNat
  initial : savedHash body = SHS.SHA256.H0_256
  input : ∀ i : Fin data.size, body.mem.read8 (body.readReg64 .x2 + BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec
  padding : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
    body.mem.read8 (body.sp + 288#64 + BitVec.ofNat 64 i.val) =
      ((SHS.Equiv.SHA256.Padding.Layout.implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec
  outside : ∀ p, 416 ≤ (p - entryStack s).toNat → body.mem.cells p = s.mem.cells p


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem prepare_raw_call (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : RawSHAInputs base s data) : ∃ body, RawPreparedBody base s data body := by
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  have tailIndex (i : Fin (data.size % 64)) : data.size / 64 * 64 + i.val < data.size := by
    have ih := i.isLt
    omega
  have chunks (i : Fin 16) : s.mem.canWrite (entryStack s + 288#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (288 + 8 * i.val) 8 (by have := i.isLt; omega)
  have padBytes (i : Fin 128) : s.mem.canWrite (entryStack s + 288#64 + BitVec.ofNat 64 i.val) 1 = true := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (288 + i.val) 1 (by have := i.isLt; omega)
  have tailReads (i : Fin (data.size % 64)) : s.mem.canRead (entryTail s data + BitVec.ofNat 64 i.val) 1 = true := by
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using
      entry.inputRead (data.size / 64 * 64 + i.val) 1 (by have := tailIndex i; omega)
  have tailSep (i : Fin (data.size % 64)) :
      128 ≤ (entryTail s data + BitVec.ofNat 64 i.val - (entryStack s + 288#64)).toNat := by
    have outside := entry.inputOutside ⟨data.size / 64 * 64 + i.val, tailIndex i⟩
    have dist := region_store_delta (entryStack s) _ 288 416 128 (by decide) outside
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using dist
  have tailValues (i : Fin (data.size % 64)) : s.mem.read8 (entryTail s data + BitVec.ofNat 64 i.val) =
      (data.get! (data.size / 64 * 64 + i.val)).toBitVec := by
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using
      entry.inputBytes ⟨data.size / 64 * 64 + i.val, tailIndex i⟩
  obtain ⟨padded, hp, pstate, pnv, psp, ppc, _, p1, p2, p3, p6, _, _, _, padding, pframe, pread, pwrite⟩ :=
    header_padding s data entry.bound entry.offsetRead entry.countRead entry.countValue chunks padBytes tailReads tailSep tailValues
  have pcPadded : padded.pc = base + 132#64 := by rw [ppc, entry.pc]
  have ivRead (i : Fin 4) : padded.mem.canRead (padded.pc + 732#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    have address : padded.pc + 732#64 + BitVec.ofNat 64 (8 * i.val) = base + BitVec.ofNat 64 (864 + 8 * i.val) := by
      rw [pcPadded]
      simp (config := { decide := true }) [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    exact pread _ _ (entry.poolRead (864 + 8 * i.val) 8 (by omega) (by have := i.isLt; omega))
  have ivWrite (i : Fin 4) : padded.mem.canWrite (padded.sp + 256#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [psp, pwrite]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (256 + 8 * i.val) 8 (by have := i.isLt; omega)
  have paddedImage (i : Fin 896) : padded.mem.cells (base + BitVec.ofNat 64 i.val) =
      s.mem.cells (base + BitVec.ofNat 64 i.val) :=
    pframe _ (region_store_delta (entryStack s) _ 288 416 128 (by decide) (entry.imageOutside i))
  have ivValues : wordVector 8 padded.mem (padded.pc + 732#64) = SHS.SHA256.H0_256 := by
    have samePool : wordVector 8 padded.mem (base + 864#64) = wordVector 8 s.mem (base + 864#64) := by
      apply Vector.ext
      intro i hi
      simp only [wordVector, Vector.getElem_ofFn]
      apply read32_of_cells
      intro b
      have cell := paddedImage ⟨864 + 4 * i + b.val, by have := b.isLt; omega⟩
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using cell
    have address : padded.pc + 732#64 = base + 864#64 := by rw [pcPadded, BitVec.add_assoc]; rfl
    rw [address]
    exact samePool.trans entry.initialPool
  obtain ⟨body, hi, initial, inm, inv, ipc, i0, i1, i2, i3, i4, i6, iframe, iread, iwrite⟩ :=
    initialize_hash_from_iv base padded pcPadded ivRead ivWrite ivValues
  have isp := congrArg Arm64.State.sp inm
  change body.sp = padded.sp at isp
  have stack : body.sp = entryStack s := isp.trans psp
  have output : body.readReg64 .x1 = s.readReg64 .x1 := i1.trans p1
  have payload : body.readReg64 .x2 = inputPayload s := i2.trans p2
  have readable (a : BitVec 64) (n : Nat) (h : s.mem.canRead a n = true) : body.mem.canRead a n = true :=
    iread a n (pread a n h)
  have writable (a : BitVec 64) (n : Nat) : body.mem.canWrite a n = s.mem.canWrite a n :=
    (iwrite a n).trans (pwrite a n)
  have frame (a : BitVec 64) (h : 416 ≤ (a - entryStack s).toNat) : body.mem.cells a = s.mem.cells a := by
    have dist : 288 ≤ (a - padded.sp).toNat := by rw [psp]; omega
    exact (iframe a dist).trans (pframe a (region_store_delta _ _ 288 416 128 (by decide) h))
  have constants (i : Fin 64) : body.mem.read32 (body.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]! := by
    rw [i0]
    have preserved : body.mem.read32 (base + 608#64 + BitVec.ofNat 64 (4 * i.val)) =
        s.mem.read32 (base + 608#64 + BitVec.ofNat 64 (4 * i.val)) := by
      apply read32_of_cells
      intro b
      have cell := frame _ (entry.imageOutside ⟨608 + 4 * i.val + b.val, by have := i.isLt; have := b.isLt; omega⟩)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using cell
    have words := congrArg (fun W : Vector (BitVec 32) 64 => W[i.val]!) entry.roundPool
    have expected : s.mem.read32 (base + 608#64 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]! := by
      simpa [wordVector, i.isLt] using words
    exact preserved.trans expected
  have constantsOutside (i : Fin 64) (b : Fin 4) :
      288 ≤ (body.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - body.sp).toNat := by
    rw [i0, stack]
    have ih := i.isLt
    have bh := b.isLt
    have dist := entry.imageOutside ⟨608 + 4 * i.val + b.val, by omega⟩
    have same : base + 608#64 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val =
        base + BitVec.ofNat 64 (608 + 4 * i.val + b.val) := by simp only [BitVec.ofNat_add, BitVec.add_assoc]
    change 416 ≤ (base + BitVec.ofNat 64 (608 + 4 * i.val + b.val) - entryStack s).toNat at dist
    rw [same]
    exact Nat.le_trans (by decide : 288 ≤ 416) dist
  have ready : BlockReady body := by
    constructor
    · change ((body.sp &&& 15#64) == 0#64) = true
      rw [stack]
      exact entry.aligned
    · intro i
      rw [stack]
      exact readable _ _ (entry.stackRead (4 * i.val) 4 (by have := i.isLt; omega))
    · intro i
      rw [stack, writable]
      exact entry.stackWrite (4 * i.val) 4 (by have := i.isLt; omega)
    · intro i
      rw [stack]
      apply readable
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackRead (256 + 4 * i.val) 4 (by have := i.isLt; omega)
    · intro i
      rw [stack, writable]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (256 + 4 * i.val) 4 (by have := i.isLt; omega)
    · intro i
      rw [i0]
      apply readable
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.poolRead (608 + 4 * i.val) 4 (by omega) (by have := i.isLt; omega)
    · exact constants
    · exact constantsOutside
  have fullReads (i : Fin (data.size / 64)) (j : Fin 16) : body.mem.canRead
      (body.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true := by
    rw [payload]
    apply readable
    exact entry.inputRead _ _ (by have := i.isLt; have := j.isLt; omega)
  have fullSep (i : Fin (data.size / 64)) (j : Fin 16) (b : Fin 4) :
      288 ≤ (body.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - body.sp).toNat := by
    rw [payload, stack]
    have ih := i.isLt
    have jh := j.isLt
    have bh := b.isLt
    have enough : 64 * i.val + 4 * j.val + b.val < data.size := by omega
    have dist := entry.inputOutside ⟨64 * i.val + 4 * j.val + b.val, enough⟩
    change 416 ≤ (inputPayload s + BitVec.ofNat 64 (64 * i.val + 4 * j.val + b.val) - entryStack s).toNat at dist
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using (Nat.le_trans (by decide : 288 ≤ 416) dist)
  have padRead (i : Fin 32) : body.mem.canRead (body.sp + 288#64 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [stack]
    apply readable
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackRead (288 + 4 * i.val) 4 (by have := i.isLt; omega)
  have outWrite (i : Fin 8) : body.mem.canWrite (body.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [output, writable]
    exact entry.outputWrite _ _ (by have := i.isLt; omega)
  have outSep (i : Fin 8) (b : Fin 4) :
      288 ≤ (body.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - body.sp).toNat := by
    rw [output, stack]
    have ih := i.isLt
    have bh := b.isLt
    have dist := entry.outputOutside ⟨4 * i.val + b.val, by omega⟩
    change 416 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val + b.val) - entryStack s).toNat at dist
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using (Nat.le_trans (by decide : 288 ≤ 416) dist)
  have input (i : Fin data.size) : body.mem.read8 (body.readReg64 .x2 + BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec := by
    rw [payload]
    exact (read8_of_cell _ (frame _ (entry.inputOutside i))).trans (entry.inputBytes i)
  have padValues (i : Fin (lengthOffset (data.size % 64) + 8)) :
      body.mem.read8 (body.sp + 288#64 + BitVec.ofNat 64 i.val) =
        ((SHS.Equiv.SHA256.Padding.Layout.implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec := by
    rw [stack]
    have limits := lengthOffset_bounds (data.size % 64) (Nat.mod_lt _ (by decide))
    have ih := i.isLt
    have dist : 288 ≤ (entryStack s + 288#64 + BitVec.ofNat 64 i.val - padded.sp).toNat := by
      rw [psp]
      exact padding_byte_outside _ ⟨i.val, by omega⟩
    exact (read8_of_cell _ (iframe _ dist)).trans (padding i)
  have count : body.readReg64 .x3 = BitVec.ofNat 64 (data.size / 64) := i3.trans p3
  have padCount : body.readReg64 .x6 = BitVec.ofNat 64 (paddingBlockCount data) := by
    rw [i6, p6]
    unfold paddingBlockCount
    split <;> rfl
  have erase := congrArg (fun st : Arm64.State => { st with sp := 0#64 }) inm
  change returnStable body = returnStable padded at erase
  have prologue := @runWords_append_success (headerPaddingCode (BitVec.ofNat 64 data.size)) hashInitCode s padded body hp hi
  refine ⟨body, ?_, erase.trans pstate, inv.trans pnv, stack, ?_, output,
    ready, count, i4, padCount, fullReads, fullSep, padRead, outWrite, outSep, initial, input, padValues, frame⟩
  · simpa only [prologueCode] using prologue
  · rw [ipc, pcPadded, BitVec.add_assoc]
    rfl


end Crypto.ARM64.Imported
