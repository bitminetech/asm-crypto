import Proofs.ARM64.ImportedCycleCompose
import Proofs.ARM64.ImportedCycleFetch
import Proofs.ARM64.ImportedHeaderPadding
import Proofs.ARM64.ImportedHashInitFrame

/-!
Fetched-image paths for the recorded header, tail copy, one/two-block padding
and hash initialization. Existing native prefix/PC proofs determine each
branch path; every recorded instruction retains imported ISA semantics.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem padding_runWords_code_cast (s out : Arm64.State) (left right : List (BitVec 32))
    (equal : left = right) (executed : runWords left s = some out) : runWords right s = some out := by
  cases equal
  exact executed

theorem padding_runWords_suffix (left right : List (BitVec 32)) (s mid out : Arm64.State)
    (prefixExec : runWords left s = some mid) (executed : runWords (left ++ right) s = some out) :
    runWords right mid = some out := by
  rw [runWords_append, prefixExec, Option.bind_some] at executed
  exact executed

theorem padding_runCycles_from_words (code : List (BitVec 32)) (n : Nat) (s out : Arm64.State)
    (executed : runWords (List.replicate n code).flatten s = some out) : runCycles code n s = some out :=
  (runCycles_words code n s).trans executed

theorem padding_runCycles_succ (code : List (BitVec 32)) (n : Nat) (s before after : Arm64.State)
    (prefixExec : runCycles code n s = some before) (body : runWords code before = some after) :
    runCycles code (n + 1) s = some after := by
  change (runCycles code n s).bind (runWords code) = some after
  rw [prefixExec]
  exact body

theorem staticPath_code_cast (base : BitVec 64) (s : Arm64.State)
    (left right : List (BitVec 32)) (equal : left = right) (path : StaticPath base right s) :
    StaticPath base left s := by
  cases equal
  exact path

theorem header_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 0#64) (executed : runWords headerCode s = some out)
    (running : out.status = .Running) : StaticPath base headerCode s ∧ out.pc = s.pc + 16#64 := by
  have shape : headerCode = imageSlice 0 4 := by decide +kernel
  have sequential : SequentialWords (imageSlice 0 4) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 0 4 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem zero_pad_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 16#64) (executed : runWords zeroPadCode s = some out)
    (running : out.status = .Running) : StaticPath base zeroPadCode s ∧ out.pc = s.pc + 36#64 := by
  have shape : zeroPadCode = imageSlice 4 9 := by decide +kernel
  have sequential : SequentialWords (imageSlice 4 9) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 4 9 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem padding_setup_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 52#64) (executed : runWords paddingSetupCode s = some out)
    (running : out.status = .Running) : StaticPath base paddingSetupCode s ∧ out.pc = s.pc + 16#64 := by
  have shape : paddingSetupCode = imageSlice 13 4 := by decide +kernel
  have sequential : SequentialWords (imageSlice 13 4) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 13 4 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem marker_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 92#64) (executed : runWords markerCode s = some out)
    (running : out.status = .Running) : StaticPath base markerCode s ∧ out.pc = s.pc + 8#64 := by
  have shape : markerCode = imageSlice 23 2 := by decide +kernel
  have sequential : SequentialWords (imageSlice 23 2) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 23 2 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem length_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 116#64) (executed : runWords lengthCode s = some out)
    (running : out.status = .Running) : StaticPath base lengthCode s ∧ out.pc = s.pc + 16#64 := by
  have shape : lengthCode = imageSlice 29 4 := by decide +kernel
  have sequential : SequentialWords (imageSlice 29 4) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 29 4 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem hash_init_linear_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 132#64) (executed : runWords hashInitCode s = some out)
    (running : out.status = .Running) : StaticPath base hashInitCode s ∧ out.pc = s.pc + 32#64 := by
  have shape : hashInitCode = imageSlice 33 8 := by decide +kernel
  have sequential : SequentialWords (imageSlice 33 8) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  obtain ⟨path, finalPC⟩ := sequential_slice_path base 33 8 s out (by decide) sequential pc executed running
  refine ⟨path, ?_⟩
  rw [pc]
  simpa only [BitVec.add_assoc] using finalPC

theorem tail_cycle_words_permitted : PermittedWords tailCopyCycleCode := permittedWords_of_all _ (by decide +kernel)

theorem tail_end_words_permitted : PermittedWords tailCopyEndCode := permittedWords_of_all _ (by decide +kernel)

theorem marker_words_permitted : PermittedWords markerCode := permittedWords_of_all _ (by decide +kernel)

theorem length_words_permitted : PermittedWords lengthCode := permittedWords_of_all _ (by decide +kernel)

theorem zero_pad_words_permitted : PermittedWords zeroPadCode := permittedWords_of_all _ (by decide +kernel)

theorem padding_setup_words_permitted : PermittedWords paddingSetupCode := permittedWords_of_all _ (by decide +kernel)

theorem header_words_permitted : PermittedWords headerCode := permittedWords_of_all _ (by decide +kernel)

theorem hash_init_words_permitted : PermittedWords hashInitCode := permittedWords_of_all _ (by decide +kernel)

theorem padding_count_words_permitted (small : Bool) : PermittedWords (paddingCountCode small) := by
  cases small <;> exact permittedWords_of_all _ (by decide +kernel)

theorem tail_copy_words_permitted (rem : Nat) : PermittedWords (tailCopyCode rem) :=
  (tail_cycle_words_permitted.repeated rem).append tail_end_words_permitted

theorem prepare_tail_words_permitted (rem : Nat) : PermittedWords (prepareTailCode rem) :=
  zero_pad_words_permitted.append (padding_setup_words_permitted.append (tail_copy_words_permitted rem))

theorem padding_suffix_words_permitted (rem : Nat) : PermittedWords (paddingSuffixCode rem) :=
  marker_words_permitted.append ((padding_count_words_permitted _).append length_words_permitted)

theorem prepare_padding_words_permitted (count : BitVec 64) : PermittedWords (preparePaddingCode count) :=
  (prepare_tail_words_permitted _).append (padding_suffix_words_permitted _)

theorem tail_copy_staticPath (base : BitVec 64) (s : Arm64.State) (rem : Nat)
    (hrem : rem < 64) (hc : s.readReg64 .x6 = 0#64)
    (hrm : s.readReg64 .x17 = BitVec.ofNat 64 rem)
    (hr : ∀ i : Fin rem, s.mem.canRead (s.readReg64 .x5 + BitVec.ofNat 64 i.val) 1 = true)
    (hw : ∀ i : Fin 128, s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 i.val) 1 = true)
    (hout : ∀ i : Fin rem, 128 ≤ (s.readReg64 .x5 + BitVec.ofNat 64 i.val - s.readReg64 .x16).toNat)
    (out : Arm64.State) (pc : s.pc = base + 68#64)
    (executed : runWords (tailCopyCode rem) s = some out) (running : out.status = .Running) :
    StaticPath base (tailCopyCode rem) s := by
  have expanded := padding_runWords_code_cast s out (tailCopyCode rem)
    ((List.replicate rem tailCopyCycleCode).flatten ++ tailCopyEndCode) rfl executed
  obtain ⟨mid, loopExec, endExec⟩ := runWords_append_split (List.replicate rem tailCopyCycleCode).flatten tailCopyEndCode s out expanded
  have midRunning := runWords_running_before tailCopyEndCode mid out tail_end_words_permitted endExec running
  have cycleExec := padding_runCycles_from_words tailCopyCycleCode rem s mid loopExec
  have loopPath : StaticPath base (List.replicate rem tailCopyCycleCode).flatten s := by
    apply cycles_path_of_prefixes base tailCopyCycleCode s mid rem tail_cycle_words_permitted ?_ cycleExec midRunning
    intro i hi before after prefixExec bodyExec afterRunning
    obtain ⟨known, native, _, _, _, knownPC, _⟩ := tail_copy_prefix s rem hrem hc hrm hr hw hout i (by omega)
    have beforeEq := Option.some.inj (prefixExec.symm.trans native)
    have nextExec := padding_runCycles_succ tailCopyCycleCode i s before after prefixExec bodyExec
    obtain ⟨next, nextNative, _, _, _, nextPC, _⟩ := tail_copy_prefix s rem hrem hc hrm hr hw hout (i + 1) (by omega)
    have afterEq := Option.some.inj (nextExec.symm.trans nextNative)
    have beforePC : before.pc = s.pc := by rw [beforeEq, knownPC]
    have afterPC : after.pc = before.pc := by rw [afterEq, nextPC, beforePC]
    exact tail_copy_cycle_path base before after (beforePC.trans pc) afterPC bodyExec afterRunning
  obtain ⟨known, native, _, _, _, knownPC, _⟩ := tail_copy_prefix s rem hrem hc hrm hr hw hout rem (by omega)
  have midEq := Option.some.inj (cycleExec.symm.trans native)
  have midPC : mid.pc = base + 68#64 := by rw [midEq, knownPC, pc]
  have endPath := tail_copy_end_path base mid out midPC endExec running
  have combined := @StaticPath.append base (List.replicate rem tailCopyCycleCode).flatten tailCopyEndCode s mid loopExec loopPath endPath
  exact staticPath_code_cast base s (tailCopyCode rem)
    ((List.replicate rem tailCopyCycleCode).flatten ++ tailCopyEndCode) rfl combined


theorem prepare_tail_staticPath (base : BitVec 64) (s : Arm64.State)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      s.mem.canRead (tailPointer s + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer s + BitVec.ofNat 64 i.val - (s.sp + 288#64)).toNat)
    (out : Arm64.State) (pc : s.pc = base + 16#64)
    (executed : runWords (prepareTailCode ((s.readReg64 .x15).toNat % 64)) s = some out)
    (running : out.status = .Running) :
    StaticPath base (prepareTailCode ((s.readReg64 .x15).toNat % 64)) s := by
  let rem := (s.readReg64 .x15).toNat % 64
  have hrem : rem < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨zeroed, hz, postZero⟩ := exists_of_map_some _ _ _ (zero_padding s hw)
  simp only [Prod.mk.injEq] at postZero
  obtain ⟨zstable, zregs, zmem, zpc, znv, z16⟩ := postZero
  have z0 := zeroRegisters_read zregs 0#5 (by decide)
  have z1 := zeroRegisters_read zregs 1#5 (by decide)
  have z2 := zeroRegisters_read zregs 2#5 (by decide)
  have z15 := zeroRegisters_read zregs 15#5 (by decide)
  have zshift := congrArg (fun x : BitVec 64 => x >>> 6) z15
  obtain ⟨setup, hp, postSetup⟩ := exists_of_map_some _ _ _ (padding_setup zeroed)
  simp only [Prod.mk.injEq] at postSetup
  obtain ⟨pstable, ppc, pnv, p0, p1, p2, p3, p5, p6, p15, p16, p17⟩ := postSetup
  have pmem := congrArg Arm64.State.mem pstable
  change setup.mem = zeroed.mem at pmem
  have source : setup.readReg64 .x5 = tailPointer s := by rw [p5, z2, z15]; rfl
  have target : setup.readReg64 .x16 = s.sp + 288#64 := p16.trans z16
  have remainder : setup.readReg64 .x17 = BitVec.ofNat 64 rem := by
    rw [p17, z15]
    apply BitVec.toNat_inj.mp
    rw [remainder_mask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64)]
  have reads (i : Fin rem) : setup.mem.canRead (setup.readReg64 .x5 + BitVec.ofNat 64 i.val) 1 = true := by
    rw [pmem, zmem, source]
    exact zeroPadMemory_readable s _ _ (hr i)
  have writes (i : Fin 128) : setup.mem.canWrite (setup.readReg64 .x16 + BitVec.ofNat 64 i.val) 1 = true := by
    rw [pmem, zmem, target, zeroPadMemory_writable]
    exact hb i
  have outside (i : Fin rem) :
      128 ≤ (setup.readReg64 .x5 + BitVec.ofNat 64 i.val - setup.readReg64 .x16).toNat := by
    rw [source, target]; exact sep i
  have tailExec : runWords (tailCopyCode rem) setup = some out := by
    have expanded := padding_runWords_code_cast s out (prepareTailCode rem) (zeroPadCode ++ (paddingSetupCode ++ tailCopyCode rem)) rfl executed
    have afterZero := padding_runWords_suffix zeroPadCode (paddingSetupCode ++ tailCopyCode rem) s zeroed out hz expanded
    exact padding_runWords_suffix paddingSetupCode (tailCopyCode rem) zeroed setup out hp afterZero
  have setupRunning := runWords_running_before (tailCopyCode rem) setup out (tail_copy_words_permitted rem) tailExec running
  have zeroedRunning := runWords_running_before paddingSetupCode zeroed setup padding_setup_words_permitted hp setupRunning
  have zeroedPC : zeroed.pc = base + 52#64 := by rw [zpc, pc, BitVec.add_assoc]; rfl
  have setupPC : setup.pc = base + 68#64 := by rw [ppc, zeroedPC, BitVec.add_assoc]; rfl
  have zeroPath := (zero_pad_linear_path base s zeroed pc hz zeroedRunning).1
  have setupPath := (padding_setup_linear_path base zeroed setup zeroedPC hp setupRunning).1
  have tailPath := tail_copy_staticPath base setup rem hrem p6 remainder reads writes outside out setupPC tailExec running
  have combined := @StaticPath.append base zeroPadCode (paddingSetupCode ++ tailCopyCode rem) s zeroed hz zeroPath
    (@StaticPath.append base paddingSetupCode (tailCopyCode rem) zeroed setup hp setupPath tailPath)
  exact staticPath_code_cast base s (prepareTailCode rem) (zeroPadCode ++ (paddingSetupCode ++ tailCopyCode rem)) rfl combined

theorem padding_suffix_staticPath (base : BitVec 64) (s : Arm64.State) (rem : Nat)
    (hrem : rem < 64) (remainder : s.readReg64 .x17 = BitVec.ofNat 64 rem)
    (markerWrite : s.mem.canWrite (s.readReg64 .x16 + BitVec.ofNat 64 rem) 1 = true)
    (out : Arm64.State) (pc : s.pc = base + 92#64)
    (executed : runWords (paddingSuffixCode rem) s = some out) (running : out.status = .Running) :
    StaticPath base (paddingSuffixCode rem) s := by
  obtain ⟨marked, hm, postMarker⟩ := exists_of_map_some _ _ _
    (padding_marker s (by rw [remainder]; exact markerWrite))
  simp only [Prod.mk.injEq] at postMarker
  obtain ⟨mst, mr, mmem, mpc, mnv, _⟩ := postMarker
  have m17 := copyRegisters_read mr 17#5 (by decide)
  have rNat : (marked.readReg64 .x17).toNat = rem := by
    rw [m17, remainder, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64)]
  have countExec := padding_count marked
  rw [rNat] at countExec
  obtain ⟨counted, hc, postCount⟩ := exists_of_map_some _ _ _ countExec
  simp only [Prod.mk.injEq] at postCount
  obtain ⟨cst, cr, cmem, cpc, cnv, c6⟩ := postCount
  have lengthExec : runWords lengthCode counted = some out := by
    have expanded := padding_runWords_code_cast s out (paddingSuffixCode rem) (markerCode ++ (paddingCountCode (decide (rem < 56)) ++ lengthCode)) rfl executed
    have afterMarker := padding_runWords_suffix markerCode (paddingCountCode (decide (rem < 56)) ++ lengthCode) s marked out hm expanded
    exact padding_runWords_suffix (paddingCountCode (decide (rem < 56))) lengthCode marked counted out hc afterMarker
  have countedRunning := runWords_running_before lengthCode counted out length_words_permitted lengthExec running
  have markedRunning := runWords_running_before (paddingCountCode (decide (rem < 56))) marked counted
    (padding_count_words_permitted _) hc countedRunning
  have markedPC : marked.pc = base + 100#64 := by rw [mpc, pc, BitVec.add_assoc]; rfl
  have countedPC : counted.pc = base + 116#64 := by rw [cpc, markedPC, BitVec.add_assoc]; rfl
  have markerPath := (marker_linear_path base s marked pc hm markedRunning).1
  have countPath : StaticPath base (paddingCountCode (decide (rem < 56))) marked := by
    by_cases small : rem < 56
    · simpa only [small, decide_true] using padding_count_small_path base marked counted markedPC
        (by simpa only [small, decide_true] using hc) countedRunning
    · simpa only [small, decide_false] using padding_count_large_path base marked counted markedPC cpc
        (by simpa only [small, decide_false] using hc) countedRunning
  have lengthPath := (length_linear_path base counted out countedPC lengthExec running).1
  have combined := @StaticPath.append base markerCode (paddingCountCode (decide (rem < 56)) ++ lengthCode) s marked hm markerPath
    (@StaticPath.append base (paddingCountCode (decide (rem < 56))) lengthCode marked counted hc countPath lengthPath)
  exact staticPath_code_cast base s (paddingSuffixCode rem) (markerCode ++ (paddingCountCode (decide (rem < 56)) ++ lengthCode)) rfl combined

theorem prepare_padding_staticPath (base : BitVec 64) (s : Arm64.State)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      s.mem.canRead (tailPointer s + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer s + BitVec.ofNat 64 i.val - (s.sp + 288#64)).toNat)
    (out : Arm64.State) (pc : s.pc = base + 16#64)
    (executed : runWords (preparePaddingCode (s.readReg64 .x15)) s = some out)
    (running : out.status = .Running) : StaticPath base (preparePaddingCode (s.readReg64 .x15)) s := by
  let rem := (s.readReg64 .x15).toNat % 64
  have hrem : rem < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨copied, hc, cnm, cnv, cp, c0, c1, c2, c3, _, c15, c16, c17, bytes, frame, readable, writable⟩ :=
    prepare_tail s hw hb hr sep
  have suffixExec : runWords (paddingSuffixCode rem) copied = some out := by
    have expanded := padding_runWords_code_cast s out (preparePaddingCode (s.readReg64 .x15)) (prepareTailCode rem ++ paddingSuffixCode rem) rfl executed
    exact padding_runWords_suffix (prepareTailCode rem) (paddingSuffixCode rem) s copied out hc expanded
  have copiedRunning := runWords_running_before (paddingSuffixCode rem) copied out
    (padding_suffix_words_permitted rem) suffixExec running
  have copiedPC : copied.pc = base + 92#64 := by rw [cp, pc, BitVec.add_assoc]; rfl
  have markerWrite : copied.mem.canWrite (copied.readReg64 .x16 + BitVec.ofNat 64 rem) 1 = true := by
    rw [c16, writable]
    exact hb ⟨rem, by omega⟩
  have tailPath := prepare_tail_staticPath base s hw hb hr sep copied pc hc copiedRunning
  have suffixPath := padding_suffix_staticPath base copied rem hrem c17 markerWrite out copiedPC suffixExec running
  have combined := @StaticPath.append base (prepareTailCode rem) (paddingSuffixCode rem) s copied hc tailPath suffixPath
  exact staticPath_code_cast base s (preparePaddingCode (s.readReg64 .x15)) (prepareTailCode rem ++ paddingSuffixCode rem) rfl combined

theorem header_padding_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (bound : data.size < 2 ^ 61)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true)
    (countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 data.size)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((entryStack s + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((entryStack s + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin (data.size % 64), s.mem.canRead (entryTail s data + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin (data.size % 64),
      128 ≤ (entryTail s data + BitVec.ofNat 64 i.val - (entryStack s + 288#64)).toNat)
    (out : Arm64.State) (pc : s.pc = base)
    (executed : runWords (headerPaddingCode (BitVec.ofNat 64 data.size)) s = some out)
    (running : out.status = .Running) : StaticPath base (headerPaddingCode (BitVec.ofNat 64 data.size)) s := by
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
  have paddingExec : runWords (preparePaddingCode (header.readReg64 .x15)) header = some out := by
    rw [hcount]
    have expanded := padding_runWords_code_cast s out (headerPaddingCode (BitVec.ofNat 64 data.size)) (headerCode ++ preparePaddingCode (BitVec.ofNat 64 data.size)) rfl executed
    exact padding_runWords_suffix headerCode (preparePaddingCode (BitVec.ofNat 64 data.size)) s header out he expanded
  have headerRunning := runWords_running_before (preparePaddingCode (header.readReg64 .x15)) header out
    (prepare_padding_words_permitted _) paddingExec running
  have headerPC : header.pc = base + 16#64 := by rw [hpc, pc]
  have headerPath := (header_linear_path base s header (by simpa only [BitVec.add_zero] using pc) he headerRunning).1
  have paddingPath := prepare_padding_staticPath base header writes byteWrites reads outside out headerPC paddingExec running
  rw [hcount] at paddingPath
  have combined := @StaticPath.append base headerCode (preparePaddingCode (BitVec.ofNat 64 data.size)) s header he headerPath paddingPath
  exact staticPath_code_cast base s (headerPaddingCode (BitVec.ofNat 64 data.size)) (headerCode ++ preparePaddingCode (BitVec.ofNat 64 data.size)) rfl combined

end Crypto.ARM64.Imported
