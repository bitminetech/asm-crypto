import Proofs.ARM64.ImportedHeaderPadding
import Proofs.ARM64.ImportedHashInitFrame
import Proofs.ARM64.ImportedReferenceLayout
import Proofs.ARM64.ImportedCallBounds

/-!
Complete recorded-word SHA-256 call, from header decoding through RET, under
operational initial-memory, loading, permission, separation and register facts.
No execution result or digest conclusion is assumed by CallInputs. The proof
composes header/padding, actual loaded FIPS initialization, both block phases
and output/return, producing exactly the pinned reference digest.

This remains a word-list theorem. CallInputs is a lower-level sufficient
condition, not the architecture's independently reviewed typed caller-entry or
full equal baseline. Whole-path memory-fetch correspondence, full resource/
concurrency/confidentiality guarantees, ABI/profile coverage and runtime build
binding remain separate obligations. Do not mark equal checked from this file.
-/
namespace Crypto.ARM64.Imported

structure CallInputs (base : BitVec 64) (s : Arm64.State) (data : ByteArray) : Prop where
  bound : data.size < 2 ^ 61
  pc : s.pc = base
  running : s.status = .Running
  loaded : (program base).CodeLoaded s.mem
  aligned : ((entryStack s &&& 15#64) == 0#64) = true
  offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true
  countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true
  countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 data.size
  stackRead : ∀ off n, off + n ≤ 416 → s.mem.canRead (entryStack s + BitVec.ofNat 64 off) n = true
  stackWrite : ∀ off n, off + n ≤ 416 → s.mem.canWrite (entryStack s + BitVec.ofNat 64 off) n = true
  inputRead : ∀ off n, off + n ≤ data.size → s.mem.canRead (inputPayload s + BitVec.ofNat 64 off) n = true
  outputWrite : ∀ off n, off + n ≤ 32 → s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 off) n = true
  codeRead : ∀ off n, off + n ≤ 896 → s.mem.canRead (base + BitVec.ofNat 64 off) n = true
  imageOutside : ∀ i : Fin 896, 416 ≤ (base + BitVec.ofNat 64 i.val - entryStack s).toNat
  inputOutside : ∀ i : Fin data.size, 416 ≤ (inputPayload s + BitVec.ofNat 64 i.val - entryStack s).toNat
  outputOutside : ∀ i : Fin 32, 416 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack s).toNat
  inputBytes : ∀ i : Fin data.size, s.mem.read8 (inputPayload s + BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec

set_option maxRecDepth 16384 in
theorem program_code_length (base : BitVec 64) : (program base).code.length = 896 := by
  change (program 0#64).code.length = 896
  decide +kernel

theorem read8_of_cell {m before : Arm64.Memory} (p : BitVec 64)
    (cell : m.cells p = before.cells p) : m.read8 p = before.read8 p := by
  unfold Arm64.Memory.read8
  rw [cell]

theorem codeLoaded_of_cells {prog : Arm64.Program} {m before : Arm64.Memory}
    (loaded : prog.CodeLoaded before)
    (cells : ∀ i, i < prog.code.length → m.cells (prog.base + BitVec.ofNat 64 i) = before.cells (prog.base + BitVec.ofNat 64 i)) :
    prog.CodeLoaded m := by
  rw [codeLoaded_iff] at loaded ⊢
  refine ⟨loaded.1, loaded.2.1, ?_⟩
  intro i hi
  have cell := cells i hi
  have old := loaded.2.2 i hi
  simpa only [Arm64.Memory.read8, Arm64.Memory.perm, Arm64.Memory.isLazyFree, cell] using old

theorem padding_byte_outside (sp : BitVec 64) (i : Fin 128) :
    288 ≤ (sp + 288#64 + BitVec.ofNat 64 i.val - sp).toNat := by
  have ih := i.isLt
  have bound : 288 + i.val < 2 ^ 64 := by omega
  have address : sp + 288#64 + BitVec.ofNat 64 i.val = sp + BitVec.ofNat 64 (288 + i.val) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  rw [address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem whole_call_sha256 (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) :
    ∃ out, runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧ memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
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
  have codePadded : (program base).CodeLoaded padded.mem := by
    apply codeLoaded_of_cells entry.loaded
    intro i hi
    rw [program_code_length] at hi
    have dist := region_store_delta (entryStack s) (base + BitVec.ofNat 64 i) 288 416 128 (by decide) (entry.imageOutside ⟨i, hi⟩)
    exact pframe _ dist
  have pcPadded : padded.pc = base + 132#64 := by rw [ppc, entry.pc]
  have ivRead (i : Fin 4) : padded.mem.canRead (padded.pc + 732#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    have address : padded.pc + 732#64 + BitVec.ofNat 64 (8 * i.val) = base + BitVec.ofNat 64 (864 + 8 * i.val) := by
      rw [pcPadded]
      simp (config := { decide := true }) [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    exact pread _ _ (entry.codeRead (864 + 8 * i.val) 8 (by have := i.isLt; omega))
  have ivWrite (i : Fin 4) : padded.mem.canWrite (padded.sp + 256#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [psp, pwrite]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (256 + 8 * i.val) 8 (by have := i.isLt; omega)
  obtain ⟨body, hi, initial, inm, inv, _, i0, i1, i2, i3, i4, i6, iframe, iread, iwrite⟩ :=
    initialize_hash_fips base padded codePadded pcPadded ivRead ivWrite
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
  have codeBody : (program base).CodeLoaded body.mem := by
    apply codeLoaded_of_cells entry.loaded
    intro i hi
    rw [program_code_length] at hi
    exact frame _ (entry.imageOutside ⟨i, hi⟩)
  have constants (i : Fin 64) : body.mem.read32 (body.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]! := by
    rw [i0]
    have words := congrArg (fun W : Vector (BitVec 32) 64 => W[i.val]!) (loaded_round_pool base body.mem codeBody)
    simpa [wordVector, i.isLt] using words
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
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.codeRead (608 + 4 * i.val) 4 (by have := i.isLt; omega)
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
  obtain ⟨out, ho, ostate, onv, osp, opc, status, _, bytes⟩ :=
    hash_body_sha256 body data ready entry.bound count i4 padCount fullReads fullSep padRead outWrite outSep initial input padValues
  have erase := congrArg (fun st : Arm64.State => { st with sp := 0#64 }) inm
  change returnStable body = returnStable padded at erase
  have nv := inv.trans pnv
  have lr := congrFun nv ⟨12, by decide⟩
  change body.readReg64 .x30 = s.readReg64 .x30 at lr
  have suffix := runWords_append_success hi ho
  have whole := runWords_append_success hp suffix
  have state := ostate.trans (erase.trans pstate)
  have running := congrArg Arm64.State.status state
  change out.status = s.status at running
  refine ⟨out, ?_, state, onv.trans nv, ?_, opc.trans lr, status, running.trans entry.running, ?_⟩
  · simpa only [wholeCallCode, headerPaddingCode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      paddingBlockCount, List.append_assoc] using whole
  · rw [osp, stack]
    exact BitVec.sub_add_cancel _ _
  · simpa only [output] using bytes

end Crypto.ARM64.Imported
