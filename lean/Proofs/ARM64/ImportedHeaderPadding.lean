import Proofs.ARM64.ImportedHeader
import Proofs.ARM64.ImportedPaddingReference

/-!
The recorded header decoder and complete padding path compose from actual
entry memory. The output padding is the pinned FIPS padded-byte tail and all
needed registers, frame and permissions are retained for whole-call composition.
-/
namespace Crypto.ARM64.Imported

theorem ofNat_full_blocks (n : Nat) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
  have hd : n / 64 < 2 ^ 64 := by omega
  apply BitVec.toNat_inj.mp
  simp only [full_blocks_shift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hd]

theorem ofNat_tail_offset (n : Nat) (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> 6) <<< 6 = BitVec.ofNat 64 (n / 64 * 64) := by
  have mul := Nat.div_mul_le_self n 64
  have hm : n / 64 * 64 < 2 ^ 64 := by omega
  apply BitVec.toNat_inj.mp
  simp only [tail_offset_shift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hm]

def inputPayload (s : Arm64.State) := s.readReg64 .x0 + s.mem.read64 (s.readReg64 .x0 + 8#64)
def entryStack (s : Arm64.State) := s.sp - 416#64
def entryTail (s : Arm64.State) (data : ByteArray) :=
  inputPayload s + BitVec.ofNat 64 (data.size / 64 * 64)
def headerPaddingCode (count : BitVec 64) := headerCode ++ preparePaddingCode count

theorem header_padding (s : Arm64.State) (data : ByteArray) (bound : data.size < 2 ^ 61)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true)
    (countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 data.size)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((entryStack s + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((entryStack s + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin (data.size % 64), s.mem.canRead (entryTail s data + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin (data.size % 64),
      128 ≤ (entryTail s data + BitVec.ofNat 64 i.val - (entryStack s + 288#64)).toNat)
    (tail : ∀ i : Fin (data.size % 64), s.mem.read8 (entryTail s data + BitVec.ofNat 64 i.val) =
      (data.get! (data.size / 64 * 64 + i.val)).toBitVec) :
    ∃ out, runWords (headerPaddingCode (BitVec.ofNat 64 data.size)) s = some out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = entryStack s ∧ out.pc = s.pc + 132#64 ∧
      out.readReg64 .x0 = s.readReg64 .x0 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = inputPayload s ∧ out.readReg64 .x3 = BitVec.ofNat 64 (data.size / 64) ∧
      out.readReg64 .x6 = (if data.size % 64 < 56 then 1#64 else 2#64) ∧
      out.readReg64 .x15 = BitVec.ofNat 64 data.size ∧ out.readReg64 .x16 = entryStack s + 288#64 ∧
      out.readReg64 .x17 = BitVec.ofNat 64 (data.size % 64) ∧
      (∀ i : Fin (lengthOffset (data.size % 64) + 8),
        out.mem.read8 (entryStack s + 288#64 + BitVec.ofNat 64 i.val) =
          ((SHS.Equiv.SHA256.Padding.Layout.implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec) ∧
      (∀ p, 128 ≤ (p - (entryStack s + 288#64)).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  have hn : data.size < 2 ^ 64 := by omega
  obtain ⟨header, he, post⟩ := exists_of_map_some _ _ _ (decode_header s offsetRead countRead)
  simp only [Prod.mk.injEq] at post
  obtain ⟨hst, hm, hsp, hpc, hnv, h0, h1, h2, _, h15⟩ := post
  have hcount : header.readReg64 .x15 = BitVec.ofNat 64 data.size := h15.trans countValue
  have countNat : (header.readReg64 .x15).toNat = data.size := by
    rw [hcount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have target : header.sp + 288#64 = entryStack s + 288#64 := by rw [hsp]; rfl
  have pointer : tailPointer header = entryTail s data := by
    unfold tailPointer entryTail inputPayload
    rw [h2, hcount, ofNat_tail_offset data.size hn]
  have writes (i : Fin 16) : header.mem.canWrite
      (header.sp + 288#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [hm, target]; exact hw i
  have byteWrites (i : Fin 128) : header.mem.canWrite
      (header.sp + 288#64 + BitVec.ofNat 64 i.val) 1 = true := by rw [hm, target]; exact hb i
  have reads : ∀ i : Fin ((header.readReg64 .x15).toNat % 64),
      header.mem.canRead (tailPointer header + BitVec.ofNat 64 i.val) 1 = true := by
    rw [countNat]
    intro i
    rw [hm, pointer]; exact hr i
  have outside : ∀ i : Fin ((header.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer header + BitVec.ofNat 64 i.val - (header.sp + 288#64)).toNat := by
    rw [countNat]
    intro i
    rw [pointer, target]; exact sep i
  have tailBytes (i : Fin (data.size % 64)) :
      header.mem.read8 (tailPointer header + BitVec.ofNat 64 i.val) =
        (data.get! (data.size / 64 * 64 + i.val)).toBitVec := by
    rw [hm, pointer]; exact tail i
  obtain ⟨out, hp, nm, nv, pc, p0, p1, p2, p3, p6, p15, p16, p17, bytes, frame, readable, writable⟩ :=
    prepare_padding header writes byteWrites reads outside
  rw [hcount] at hp
  have whole := runWords_append_success he hp
  have erase := congrArg (fun st : Arm64.State => { st with sp := 0#64 }) nm
  change returnStable out = returnStable header at erase
  have sp := congrArg Arm64.State.sp nm
  change out.sp = header.sp at sp
  refine ⟨out, whole, erase.trans hst, nv.trans hnv, sp.trans hsp, ?_, p0.trans h0, p1.trans h1,
    p2.trans h2, ?_, ?_, p15.trans hcount, p16.trans target, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc, hpc, BitVec.add_assoc]
    rfl
  · rw [p3, hcount, ofNat_full_blocks data.size hn]
  · simpa only [countNat] using p6
  · simpa only [countNat] using p17
  · intro i
    have limits := lengthOffset_bounds (data.size % 64) (Nat.mod_lt _ (by decide))
    have hi := i.isLt
    have byte := bytes ⟨i.val, by omega⟩
    rw [target] at byte
    exact byte.trans (paddingByte_matches_reference header data countNat tailBytes i.val hi)
  · intro p hp
    have keep := frame p (by rw [target]; exact hp)
    rw [hm] at keep
    exact keep
  · intro a n read
    exact readable a n (by rw [hm]; exact read)
  · intro a n
    rw [writable, hm]

end Crypto.ARM64.Imported
