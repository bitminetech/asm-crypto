import Proofs.HMACSHA256.X86InnerSetup
import Proofs.HMACSHA256.X86FetchedCopy
import Proofs.HMACSHA256.EncodedByteList
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.Reference EthLib.Cryptography.Hash
open Crypto.X86_64 (byteView byteView_read byteView_read64 byteView_write64)
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset)
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_outside writeWords_word read64_eq_of_cells)
open Crypto.Baseline (Region)

private theorem same_read_cell (a b : Mem) (p : Val) (eq : a.read p = b.read p) :
    (byteView a).cells p = (byteView b).cells p := by
  simp only [byteView, Arm64.Memory.ofFn, eq]

private theorem read_eq_cell (a b : Mem) (p : Val) (eq : (byteView a).cells p = (byteView b).cells p) :
    a.read p = b.read p := by
  exact Crypto.ARM64.Imported.read8_of_cell p eq

private theorem header_memory (s : Cpu) (count : Val)
    (metadata : s.mem.readSize .q (s.regs.get .rbp + 16#64) = count)
    (away : ∀ i : Fin 8, 16 ≤ (s.regs.get .rbp + 16#64 + BitVec.ofNat 64 i.val -
      (s.regs.get .r12 + 8#64)).toNat) :
    byteView (innerHeaderState s).mem = writeWords (byteView s.mem) (s.regs.get .r12 + 8#64)
      (fun i => if i = 0 then s.mem.readSize .q (s.regs.get .r12) - 8#64
       else if i = 1 then 24#64 else count + 64#64) 3 := by
  let fields (i : Nat) := if i = 0 then s.mem.readSize .q (s.regs.get .r12) - 8#64
    else if i = 1 then 24#64 else count + 64#64
  let m := (s.mem.writeSize .q (s.regs.get .r12 + 8#64)
    (s.mem.readSize .q (s.regs.get .r12) - 8#64)).writeSize .q (s.regs.get .r12 + 16#64) 24#64
  have headerStart : byteView m = writeWords (byteView s.mem) (s.regs.get .r12 + 8#64) fields 2 := by
    unfold m
    rw [byteView_write64, byteView_write64]
    change _ = (((byteView s.mem).write64 _ _).write64
      ((s.regs.get .r12 + 8#64) + 8#64) 24#64)
    simp only [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero, BitVec.add_assoc]
    rfl
  have countHere : m.readSize .q (s.regs.get .rbp + 16#64) = count := by
    rw [← metadata, byteView_read64, byteView_read64]
    apply read64_eq_of_cells
    intro i
    rw [headerStart]
    exact writeWords_outside _ _ _ 2 _ (away i)
  change byteView (m.writeSize .q (s.regs.get .r12 + 24#64) _) = _
  rw [countHere, byteView_write64, headerStart]
  change _ = (writeWords (byteView s.mem) (s.regs.get .r12 + 8#64) fields 2).write64
    ((s.regs.get .r12 + 8#64) + 16#64) (count + 64#64)
  rw [BitVec.add_assoc]
  rfl

structure InnerExecutionFacts (base : Val) (s header padded copier out : Cpu) (message : ByteList) : Prop where
  headerPC : header.rip = base + 0x72#64
  headerLive : header.ms = none
  headerDF : header.flags.df = false
  padKey : header.regs.get .rsp = s.regs.get .rsp
  padDest : padDestination header false = s.regs.get .r12 + 32#64
  padApart : ∀ i : Fin 64, 64 ≤
    (header.regs.get .rsp + BitVec.ofNat 64 i.val - padDestination header false).toNat
  paddedPC : padded.rip = base + 0xd9#64
  paddedLive : padded.ms = none
  paddedDF : padded.flags.df = false
  paddedMessage : padded.regs.get .rbp = s.regs.get .rbp
  copyPC : copier.rip = base + 0xe9#64
  copyLive : copier.ms = none
  copyDF : copier.flags.df = false
  copySource : copier.regs.get .rsi = s.regs.get .rbp + BitVec.ofNat 64 message.offset
  copyDest : copier.regs.get .rdi = s.regs.get .r12 + 96#64
  copyCount : copier.regs.get .rcx = BitVec.ofNat 64 message.bytes.size
  copyApart : ∀ i < message.bytes.size, message.bytes.size ≤
    (copier.regs.get .rsi + BitVec.ofNat 64 i - copier.regs.get .rdi).toNat
  copyResult : copySteps copier (message.bytes.size + 1) = out

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5500000 in
/-- Construct the inner list from K0 and the portable message, then execute
every iteration of REP MOVSB from the loaded instruction at 0xe9. -/
theorem entry_inner_list (base : Val) (s : Cpu) (message : ByteList) (keyBlock : HmacKeyBlock)
    (capacity extent : Nat) (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (encoded : EncodedByteList (byteView s.mem) (s.regs.get .rbp) message)
    (size : s.mem.readSize .q (s.regs.get .r12) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (sizeBound : capacity < 2 ^ 64)
    (scratchValid : (⟨s.regs.get .r12, capacity⟩ : Region).Valid)
    (messageValid : (⟨s.regs.get .rbp, extent⟩ : Region).Valid)
    (keyValid : (⟨s.regs.get .rsp, 64⟩ : Region).Valid)
    (codeValid : (⟨base, entry.image.size⟩ : Region).Valid)
    (scratchMessage : (⟨s.regs.get .r12, capacity⟩ : Region).Disjoint ⟨s.regs.get .rbp, extent⟩)
    (scratchKey : (⟨s.regs.get .r12, capacity⟩ : Region).Disjoint ⟨s.regs.get .rsp, 64⟩)
    (scratchCode : (⟨s.regs.get .r12, capacity⟩ : Region).Disjoint ⟨base, entry.image.size⟩)
    (keyAt : ∀ i : Fin 64, s.mem.read (s.regs.get .rsp + BitVec.ofNat 64 i.val) = keyBlock[i.val].toBitVec)
    (code : entry.Loaded base s.mem.read) (pc : s.rip = base + 0x45#64)
    (validPC : canonical (base + 0xe9#64) = true) (live : s.ms = none) (direction : s.flags.df = false) :
    ∃ header padded copier out,
      runRange entry 0x45 8 s = some header ∧ runRange entry 0x72 24 header = some padded ∧
      runRange entry 0xd9 4 padded = some copier ∧ loadedSteps entry base copier (message.bytes.size + 1) = some out ∧
      out.rip = base + 0xeb#64 ∧ out.ms = none ∧ out.flags.df = false ∧
      out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .r12 = s.regs.get .r12 ∧ out.regs.get .r13 = s.regs.get .r13 ∧
      EncodedByteList (byteView out.mem) (s.regs.get .r12 + 8#64) (hmacInner message keyBlock capacity) ∧
      (∀ p, ¬ (⟨s.regs.get .r12 + 8#64, 88 + message.bytes.size⟩ : Region).Contains p → out.mem.read p = s.mem.read p) ∧
      InnerExecutionFacts base s header padded copier out message := by
  let scratch : Region := ⟨s.regs.get .r12, capacity⟩
  let written := regionSlice scratch 8 (88 + message.bytes.size)
  let msg : Region := ⟨s.regs.get .rbp, extent⟩
  let kr : Region := ⟨s.regs.get .rsp, 64⟩
  let codeRegion : Region := ⟨base, entry.image.size⟩
  let count := BitVec.ofNat 64 message.bytes.size
  let header := innerHeaderState s
  let field := fun i => if i = 0 then s.mem.readSize .q scratch.base - 8#64
    else if i = 1 then 24#64 else count + 64#64
  have headerFit : 24 ≤ extent := by have low := layout.1; have high := layout.2.2.1; omega
  have payloadFit : message.offset + message.bytes.size ≤ extent := by
    have low := layout.2.2.1
    have high := layout.2.2.2
    omega
  have spanFits : 8 + (88 + message.bytes.size) ≤ capacity := by omega
  have writtenValid : written.Valid := regionSlice_valid _ _ _ scratchValid spanFits
  have inScratch (p : Val) (h : written.Contains p) : scratch.Contains p :=
    regionSlice_inside _ _ _ scratchValid spanFits p h
  have away (offset n : Nat) (first : 8 ≤ offset) (fit : offset + n ≤ 96 + message.bytes.size)
      (p : Val) (off : ¬ written.Contains p) :
      n ≤ (p - (scratch.base + BitVec.ofNat 64 offset)).toNat := by
    let slice := regionSlice written (offset - 8) n
    have small : offset - 8 + n ≤ written.bytes := by change _ ≤ 88 + _; omega
    have address : slice.base = scratch.base + BitVec.ofNat 64 offset := by
      change (scratch.base + 8#64) + BitVec.ofNat 64 (offset - 8) = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le first]
    rw [← address]
    exact caller_outside_delta slice (regionSlice_valid _ _ _ writtenValid small) p
      (fun h => off (regionSlice_inside _ _ _ writtenValid small p h))
  have msgAway (i : Nat) (fit : i < extent) : ¬ written.Contains (msg.base + BitVec.ofNat 64 i) :=
    fun hit => scratchMessage _ ⟨inScratch _ hit, caller_region_contains_offset msg messageValid i fit⟩
  have keyAway (i : Fin 64) : ¬ written.Contains (kr.base + BitVec.ofNat 64 i.val) :=
    fun hit => scratchKey _ ⟨inScratch _ hit, caller_region_contains_offset kr keyValid i.val i.isLt⟩
  have imageAway (i : Nat) (fit : i < entry.image.size) : ¬ written.Contains (base + BitVec.ofNat 64 i) :=
    fun hit => scratchCode _ ⟨inScratch _ hit, caller_region_contains_offset codeRegion codeValid i fit⟩
  have hdr : byteView header.mem = writeWords (byteView s.mem) (scratch.base + 8#64) field 3 :=
    header_memory s count (by rw [byteView_read64]; exact encoded.count) (by
      intro i
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact away 8 16 (by decide) (by omega) _ (msgAway _ (by have := i.isLt; omega)))
  have headerFrame (p : Val) (off : ¬ written.Contains p) :
      (byteView header.mem).cells p = (byteView s.mem).cells p := by
    rw [hdr]
    exact writeWords_outside _ _ _ 3 p (away 8 24 (by decide) (by omega) p off)
  have keepHeader (r : GPR) (rax : r ≠ .rax) (r8 : r ≠ .r8) : header.regs.get r = s.regs.get r := by
    simp only [header, innerHeaderState, Regs.get_set_ne _ _ _ _ r8.symm, Regs.get_set_ne _ _ _ _ rax.symm]
  have padDest : padDestination header false = scratch.base + 32#64 := by
    change header.regs.get .r12 + 32#64 = _
    rw [keepHeader _ (by decide) (by decide)]
  have padKey : header.regs.get .rsp = kr.base := keepHeader _ (by decide) (by decide)
  have ipad : header.regs.get .r8 = 0x3636363636363636#64 := by
    simp only [header, innerHeaderState, Regs.get_set_same]
  have apart (i : Fin 64) : 64 ≤ (header.regs.get .rsp + BitVec.ofNat 64 i.val - padDestination header false).toNat := by
    rw [padDest, padKey]
    exact away 32 64 (by decide) (by omega) _ (keyAway i)
  obtain ⟨padded, pad, padBytes, padFrame, padLive, padKeep, padPC⟩ := pad_run header false live apart
  have padRun : runRange entry 0x72 24 header = some padded := pad
  have padDirection : padded.flags.df = false := by
    exact (pad_preserves_direction (s := header) false (show header.ms = none from live) apart pad).trans direction
  have frame (p : Val) (off : ¬ written.Contains p) : padded.mem.read p = s.mem.read p := by
    rw [padFrame p (by rw [padDest]; exact away 32 64 (by decide) (by omega) _ off)]
    exact read_eq_cell _ _ p (headerFrame p off)
  have reg (r : GPR) (rax : r ≠ .rax) (r8 : r ≠ .r8) : padded.regs.get r = s.regs.get r :=
    (padKeep _ rax).trans (keepHeader _ rax r8)
  have metadataRead (offset : Nat) (within : offset + 8 ≤ extent) :
      padded.mem.readSize .q (padded.regs.get .rbp + BitVec.ofNat 64 offset) =
        s.mem.readSize .q (s.regs.get .rbp + BitVec.ofNat 64 offset) := by
    rw [reg _ (by decide) (by decide), byteView_read64, byteView_read64]
    apply read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact same_read_cell _ _ _ (frame _ (msgAway _ (by have := i.isLt; omega)))
  let copier := messageCopyState padded
  have copySrc : copier.regs.get .rsi = msg.base + BitVec.ofNat 64 message.offset := by
    have offset : padded.mem.readSize .q (padded.regs.get .rbp + 8#64) = BitVec.ofNat 64 message.offset := by
      rw [metadataRead 8 (by omega), byteView_read64]
      exact encoded.offset
    have value : copier.regs.get .rsi =
        padded.mem.readSize .q (padded.regs.get .rbp + 8#64) + padded.regs.get .rbp := by
      simp (config := {decide := true}) only [copier, messageCopyState, Regs.get_set_ne, Regs.get_set_same]
    rw [value, offset, reg _ (by decide : GPR.rbp ≠ .rax) (by decide : GPR.rbp ≠ .r8)]
    exact BitVec.add_comm _ _
  have copyDst : copier.regs.get .rdi = scratch.base + 96#64 := by
    simp (config := {decide := true}) only [copier, messageCopyState, Regs.get_set_ne, Regs.get_set_same,
      reg _ (by decide : GPR.r12 ≠ .rax) (by decide : GPR.r12 ≠ .r8), scratch]
  have copyCount : copier.regs.get .rcx = count := by
    simp only [copier, messageCopyState, Regs.get_set_same, metadataRead 16 headerFit, byteView_read64]
    exact encoded.count
  have copyPC : copier.rip = base + 0xe9#64 := by
    change padded.rip + 16#64 = _
    rw [padPC, show header.rip = s.rip + 45#64 from rfl, pc]
    simp only [if_false, BitVec.add_assoc]
    rfl
  have copyCode : entry.Loaded base copier.mem.read := fun i hi =>
    (frame _ (imageAway i hi)).trans (code i hi)
  have copyAway (i : Nat) (hi : i < message.bytes.size) : message.bytes.size ≤
      (copier.regs.get .rsi + BitVec.ofNat 64 i - copier.regs.get .rdi).toNat := by
    rw [copySrc, copyDst, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact away 96 _ (by decide) (by omega) _ (msgAway _ (by omega))
  have running : copier.ms = none := padLive
  have df : copier.flags.df = false := padDirection
  have copy := entry_message_copy_loaded base copier message.bytes.size copyCode copyPC
    (by rw [copyPC]; exact validPC) running df copyCount (by omega) copyAway
    (by intro i hi; rw [copyDst]; exact away 96 _ (by decide) (by omega) _ (imageAway i hi))
  let out := copySteps copier (message.bytes.size + 1)
  obtain ⟨outPC, outLive, flags, copied, preserved⟩ :=
    copy_done copier message.bytes.size running df copyCount (by omega) copyAway
  have keepFront (off : Nat) (before : off < 96) :
      out.mem.read (scratch.base + BitVec.ofNat 64 off) = padded.mem.read (scratch.base + BitVec.ofNat 64 off) := by
    apply preserved
    rw [copyDst]
    exact outside_span_of_offset _ _ 96 _ (.inl before) (by omega) (by omega)
  let start := scratch.base + 8#64
  have headerWord (off : Nat) (fit : off + 8 ≤ 24) :
      (byteView out.mem).read64 (start + BitVec.ofNat 64 off) =
        (byteView header.mem).read64 (start + BitVec.ofNat 64 off) := by
    apply read64_eq_of_cells
    intro j
    have addr : start + BitVec.ofNat 64 off + BitVec.ofNat 64 j.val =
        scratch.base + BitVec.ofNat 64 (8 + off + j.val) := by
      simp only [start, BitVec.ofNat_add, BitVec.add_assoc]
    rw [addr]
    apply same_read_cell
    rw [keepFront _ (by have := j.isLt; omega)]
    apply padFrame
    rw [padDest]
    exact outside_span_of_offset _ _ 32 64 (.inl (by have := j.isLt; omega)) (by decide)
      (by have := j.isLt; omega)
  have padAt (i : Fin 64) : (byteView out.mem).read8 (start + 24#64 + BitVec.ofNat 64 i.val) =
      (Hmac.xorPad (EthLib.Base.packBytes keyBlock) Hmac.IPAD)[i.val]!.toBitVec := by
    have lane : (0x3636363636363636#64).extractLsb' (8 * (i.val % 8)) 8 = Hmac.IPAD.toBitVec := by
      have all : ∀ j : Fin 8, (0x3636363636363636#64).extractLsb' (8 * j.val) 8 = Hmac.IPAD.toBitVec := by decide +kernel
      exact all ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have b := padBytes i
    change padded.mem.read (padDestination header false + BitVec.ofNat 64 i.val) =
      header.mem.read (header.regs.get .rsp + BitVec.ofNat 64 i.val) ^^^ _ at b
    rw [padDest, padKey, ipad, lane, read_eq_cell _ _ _ (headerFrame _ (keyAway i)), keyAt] at b
    have hold : out.mem.read (scratch.base + 32#64 + BitVec.ofNat 64 i.val) =
        padded.mem.read (scratch.base + 32#64 + BitVec.ofNat 64 i.val) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact keepFront _ (by have := i.isLt; omega)
    rw [byteView_read]
    have addr : start + 24#64 = scratch.base + 32#64 := by dsimp only [start]; rw [BitVec.add_assoc]; rfl
    rw [addr, hold, b]
    have fit : i.val < (EthLib.Base.packBytes keyBlock).size := by
      change i.val < keyBlock.toArray.size
      rw [keyBlock.size_toArray]
      exact i.isLt
    rw [getElem!_pos _ _ (by rw [Hmac.xorPad_size]; exact fit), Hmac.xorPad_getElem fit]
    rfl
  have payloadAt (i : Fin message.bytes.size) : (byteView out.mem).read8
      (start + 88#64 + BitVec.ofNat 64 i.val) = message.bytes[i.val]!.toBitVec := by
    rw [byteView_read]
    have addr : start + 88#64 = scratch.base + 96#64 := by dsimp only [start]; rw [BitVec.add_assoc]; rfl
    rw [addr, ← copyDst, copied _ i.isLt, copySrc, BitVec.add_assoc, ← BitVec.ofNat_add]
    change padded.mem.read _ = _
    rw [frame _ (msgAway _ (by have := i.isLt; omega)), ← byteView_read]
    exact encoded.bytes i
  have regs (r : GPR) (rsi : r ≠ .rsi) (rdi : r ≠ .rdi) (rcx : r ≠ .rcx)
      (rax : r ≠ .rax) (r8 : r ≠ .r8) : out.regs.get r = s.regs.get r := by
    have register := copy_done_register copier message.bytes.size running df copyCount (by omega) copyAway r rsi rdi rcx
    rw [register]
    simp only [copier, messageCopyState, Regs.get_set_ne _ _ _ _ rsi.symm, Regs.get_set_ne _ _ _ _ rdi.symm,
      Regs.get_set_ne _ _ _ _ rcx.symm]
    exact reg r rax r8
  refine ⟨header, padded, copier, out, entry_inner_header s live, padRun, entry_copy_setup padded padLive, copy,
    ?_, outLive, by rw [flags]; exact df,
    regs _ (by decide) (by decide) (by decide) (by decide) (by decide),
    regs _ (by decide) (by decide) (by decide) (by decide) (by decide),
    regs _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [outPC, copyPC, BitVec.add_assoc]
    rfl
  · have sizeReal : BitVec.ofNat 64 capacity - 8#64 = BitVec.ofNat 64 (capacity - 8) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeBound,
        Nat.mod_eq_of_lt (by omega : capacity - 8 < 2 ^ 64)]
      change (2 ^ 64 - 8 + capacity) % 2 ^ 64 = capacity - 8
      omega
    refine encoded_hmac_inner _ start message keyBlock capacity ?_ ?_ ?_ padAt payloadAt
    · have eq : (byteView out.mem).read64 start = (byteView header.mem).read64 start := by simpa using headerWord 0 (by decide)
      rw [eq, hdr, show start = (scratch.base + 8#64) + BitVec.ofNat 64 (8 * 0) from (BitVec.add_zero _).symm,
        writeWords_word _ _ _ 3 0 (by decide) (by decide)]
      exact congrArg (· - 8#64) size |>.trans sizeReal
    · rw [headerWord 8 (by decide), hdr]
      exact writeWords_word _ _ _ 3 1 (by decide) (by decide)
    · rw [headerWord 16 (by decide), hdr, writeWords_word _ _ _ 3 2 (by decide) (by decide)]
      change count + 64#64 = _
      rw [BitVec.ofNat_add]
      exact BitVec.add_comm _ _
  · intro p off
    exact (preserved p (by rw [copyDst]; exact away 96 _ (by decide) (by omega) _ off)).trans (frame p off)

  · have headerPC : header.rip = base + 0x72#64 := by
      change s.rip + 45#64 = _
      rw [pc, BitVec.add_assoc]
      rfl
    have paddedPC : padded.rip = base + 0xd9#64 := by
      rw [padPC, headerPC, BitVec.add_assoc]
      rfl
    have headerDF : header.flags.df = false := by
      simp only [header, innerHeaderState, Flags.add, Flags.sub, Flags.fromResult, direction]
    exact ⟨headerPC, live, headerDF, padKey, padDest, apart, paddedPC, padLive, padDirection,
      reg .rbp (by decide) (by decide), copyPC, running, df, copySrc, copyDst, copyCount, copyAway, rfl⟩

end Crypto.HMACSHA256.X86_64
