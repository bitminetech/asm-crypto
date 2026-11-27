import Proofs.HMACSHA256.X86FinishTrace
import Proofs.HMACSHA256.X86Finish
import Proofs.HMACSHA256.X86FrameMemory
import Proofs.HMACSHA256.X86ShaResources
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.Baseline (Authority Region)
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset memoryBytes32)

def finishInput (s : Cpu) (extent : Nat) : Region := ⟨s.regs.get .rdi, extent⟩
def finishKey (s : Cpu) : Region := ⟨s.regs.get .rsi, 64⟩
def finishMac (s : Cpu) : Region := ⟨s.regs.get .rdx, 32⟩
def finishWorkspace (s : Cpu) : Region := ⟨s.regs.get .rsp - 696#64, 696⟩
def finishReturn (s : Cpu) : Region := ⟨s.regs.get .rsp, 8⟩

structure FinishResources (base : Val) (s : Cpu) (extent : Nat) (authority : Authority) : Prop where
  available : 696 ≤ (s.regs.get .rsp).toNat
  aligned : (s.regs.get .rsp).toNat % 16 = 8
  inputAligned : (s.regs.get .rdi).toNat % 8 = 0
  inputValid : (finishInput s extent).Valid
  keyValid : (finishKey s).Valid
  macValid : (finishMac s).Valid
  imageValid : (imageRegion (shaAddress base)).Valid
  returnValid : (finishReturn s).Valid
  stackInput : (finishWorkspace s).Disjoint (finishInput s extent)
  stackKey : (finishWorkspace s).Disjoint (finishKey s)
  stackMac : (finishWorkspace s).Disjoint (finishMac s)
  stackImage : (finishWorkspace s).Disjoint (imageRegion (shaAddress base))
  returnMac : (finishReturn s).Disjoint (finishMac s)
  macInput : (finishMac s).Disjoint (finishInput s extent)
  macKey : (finishMac s).Disjoint (finishKey s)
  macImage : (finishMac s).Disjoint (imageRegion (shaAddress base))
  inputCanonical : ∀ p, (finishInput s extent).Contains p → canonical p = true
  keyCanonical : ∀ p, (finishKey s).Contains p → canonical p = true
  macCanonical : ∀ p, (finishMac s).Contains p → canonical p = true
  stackCanonical : ∀ p, (finishWorkspace s).Contains p → canonical p = true
  codeCanonical : ∀ p, (imageRegion (shaAddress base)).Contains p → canonical p = true
  returnCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true
  innerLinkCanonical : canonical (routineAddress base finish + 0x21#64) = true
  outerLinkCanonical : canonical (routineAddress base finish + 0xaf#64) = true
  inputRead : ∀ p, (finishInput s extent).Contains p → authority.readable p
  keyRead : ∀ p, (finishKey s).Contains p → authority.readable p
  macWrite : ∀ p, (finishMac s).Contains p → authority.writable p
  stackRead : ∀ p, (finishWorkspace s).Contains p → authority.readable p
  stackWrite : ∀ p, (finishWorkspace s).Contains p → authority.writable p
  imageRead : ∀ p, (imageRegion (shaAddress base)).Contains p → authority.readable p
  shaExecutable : ∀ i < codeEnd, authority.executable (shaAddress base + BitVec.ofNat 64 i)

structure FinishFetchAuthority (base : Val) (s : Cpu) (authority : Authority) : Prop where
  loaded : finish.Loaded (routineAddress base finish) s.mem.read
  text : FinishCodeRights base authority
  immutableText : ∀ i < finish.image.size, ¬ authority.writable (routineAddress base finish + BitVec.ofNat 64 i)
  direction : s.flags.df = false
  returnRead : ∀ j < 8, canonical (s.regs.get .rsp + BitVec.ofNat 64 j) = true ∧
    authority.readable (s.regs.get .rsp + BitVec.ofNat 64 j)

def finishNativeEvents (base : Val) (s : Cpu) (inner : ByteList) (keyBlock : HmacKeyBlock) : List Event :=
  let sp := s.regs.get .rsp - 184#64
  let innerSHA := shaTraceContext s (sp - 8#64) (s.regs.get .rdi) (sp + 88#64)
  let outerSHA := shaTraceContext s (sp - 8#64) sp (s.regs.get .rdx)
  frameEnterEvents .finish (routineAddress base finish) (s.regs.get .rsp) ++
  finishInnerSetupEvents base sp ++ callEvents (shaAddress base) innerSHA inner ++
  finishHeaderEvents base sp ++ finishMaskEvents base ++
  x86PadEvents true (routineAddress base finish + 0x45#64) (s.regs.get .rsi) sp 8 ++
  finishOuterSetupEvents base sp ++ callEvents (shaAddress base) outerSHA (hmacOuter keyBlock (sha256 inner).2) ++
  frameReturnEvents .finish (routineAddress base finish + 0xaf#64) sp

structure Finished (base : Val) (s out : Cpu) (inner : ByteList) (k0 : HmacKeyBlock)
    (extent : Nat) (authority : Authority) where
  beforeReturn : Cpu
  prologue : runRange finish 0 7 s = some (enteredFrame .finish s)
  body : FinishBody base (enteredFrame .finish s) beforeReturn inner k0 extent authority
  epilogue : runRange finish 0xaf 8 beforeReturn = some out
  native : FinishFetchAuthority base s authority →
    LinkedExecution base authority s (finishNativeEvents base s inner k0) out ∧ out.flags.df = false
  live : out.ms = none
  sp : out.regs.get .rsp = s.regs.get .rsp + 8#64
  link : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  digest : memoryBytes32 (byteView out.mem) (s.regs.get .rdx) = (hmacFinish inner k0).map UInt8.toBitVec
  frame : ∀ p, ¬ (finishWorkspace s).Contains p → ¬ (finishMac s).Contains p →
    out.mem.read p = s.mem.read p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3500000 in
theorem finish_execution_from_caller (base : Val) (s : Cpu) (inner : ByteList) (k0 : HmacKeyBlock)
    (extent : Nat) (authority : Authority)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (typed : EncodedByteList (byteView s.mem) (s.regs.get .rdi) inner)
    (keyAt : ∀ i : Fin 64, s.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (g : FinishResources base s extent authority) (pc : s.rip = routineAddress base finish)
    (live : s.ms = none) (shaCanon : canonical (shaAddress base) = true)
    (shaLoaded : ImageLoaded (shaAddress base) s.mem) :
    ∃ out, Nonempty (Finished base s out inner k0 extent authority) := by
  let sp := s.regs.get .rsp
  let whole := finishWorkspace s
  let start := enteredFrame .finish s
  let saves := regionSlice whole 648 48
  let nested := regionSlice whole 0 512
  let push := regionSlice whole 504 8
  let outer := regionSlice whole 512 120
  let localPrefix := regionSlice whole 512 88
  let innerOut := regionSlice whole 600 32
  let first := innerCallState start
  have available : 696 ≤ sp.toNat := g.available
  have valid : whole.Valid := stackRegion_valid sp 696 g.available
  have fits (off n : Nat) (ok : off + n ≤ 696) : off + n ≤ whole.bytes := ok
  have regionValid (off n : Nat) (ok : off + n ≤ 696) : (regionSlice whole off n).Valid :=
    regionSlice_valid _ _ _ valid (fits _ _ ok)
  have inside (off n : Nat) (ok : off + n ≤ 696) (p : Val) (h : (regionSlice whole off n).Contains p) :
      whole.Contains p := regionSlice_inside _ _ _ valid (fits _ _ ok) p h
  have delta (off n : Nat) (ok : off + n ≤ 696) (p : Val) (h : ¬ (regionSlice whole off n).Contains p) :
      n ≤ (p - (regionSlice whole off n).base).toNat :=
    caller_outside_delta _ (regionValid off n ok) p h
  have area (off n : Nat) (ok : off ≤ 696) :
      regionSlice whole off n = ⟨sp - BitVec.ofNat 64 (696 - off), n⟩ :=
    stackRegion_slice sp 696 off n ok
  have savedBaseAt : saves.base = savedBase s := congrArg Region.base (area 648 48 (by decide))
  have startSP : start.regs.get .rsp = sp - 184#64 := by
    rw [entered_frame_stack, HmacRoutine.locals, BitVec.sub_sub]
    rfl
  have startPC : start.rip = routineAddress base finish + 0x11#64 := by rw [entered_frame_pc, pc]; rfl
  have startLive := (entered_frame_live .finish s).trans live
  have startIn := entered_frame_register .finish s .rdi (by decide)
  have startKey := entered_frame_register .finish s .rsi (by decide)
  have startDest : start.regs.get .rdx = s.regs.get .rdx := entered_frame_register .finish s .rdx (by decide)
  obtain ⟨firstIn, firstOut, _, _, firstSP, firstMem⟩ := inner_call_registers start
  have firstArg : first.regs.get .rdi = s.regs.get .rdi := firstIn.trans startIn
  have firstDest : outputRegion first = innerOut := by
    change (⟨first.regs.get .rsi, 32⟩ : Region) = _
    rw [firstOut, startSP, show innerOut = ⟨sp - 96#64, 32⟩ from area 600 32 (by decide)]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have firstSrc : inputRegion first extent = finishInput s extent := by simp [inputRegion, finishInput, firstArg]
  have firstStack : Crypto.X86_64.stackRegion first = nested := by
    change (⟨first.regs.get .rsp - 504#64, 512⟩ : Region) = _
    rw [firstSP, startSP, BitVec.sub_sub, BitVec.sub_sub, show nested = _ from area 0 512 (by decide)]
    rfl
  have slot : first.regs.get .rsp = push.base := by
    rw [firstSP, startSP, BitVec.sub_sub, show push = _ from area 504 8 (by decide)]
    rfl
  have selection (current : Cpu) (same : current.regs.get .rsp = start.regs.get .rsp) :
      current.regs.get .rsp - 8#64 = push.base := by rw [same, ← firstSP, slot]
  have callStackAlignment : (push.base).toNat % 16 = 8 := by
    rw [show push = _ from area 504 8 (by decide)]
    change (sp - BitVec.ofNat 64 192).toNat % 16 = 8
    have bound := frame_base_end sp 192 (by omega)
    have align := g.aligned
    change sp.toNat % 16 = 8 at align
    omega
  have prefixBase : localPrefix.base = start.regs.get .rsp := by
    rw [show localPrefix = _ from area 512 88 (by decide), startSP]
  have atSaves (p : Val) (noSaves : ¬ saves.Contains p) : start.mem.read p = s.mem.read p := by
    have d := delta 648 48 (by decide) p noSaves
    change 48 ≤ (p - saves.base).toNat at d
    rw [savedBaseAt] at d
    exact frame_saved_outside .finish s p d
  have atPush (p : Val) (noPush : ¬ push.Contains p) : first.mem.read p = start.mem.read p := by
    rw [firstMem, selection start rfl]
    exact store64_outside _ _ _ _ (delta 504 8 (by decide) p noPush)
  have imageElsewhere (p : Val) (image : (imageRegion (shaAddress base)).Contains p) :
      ¬ whole.Contains p := fun h => g.stackImage p ⟨h, image⟩
  have firstLoaded : ImageLoaded (shaAddress base) first.mem := by
    intro i hi
    let p := shaAddress base + BitVec.ofNat 64 i
    have off : ¬ whole.Contains p := imageElsewhere p (caller_region_contains_offset _ g.imageValid i hi)
    exact (atPush p (fun h => off (inside 504 8 (by decide) p h))).trans
      ((atSaves p (fun h => off (inside 648 48 (by decide) p h))).trans (shaLoaded i hi))
  have firstEncoding : EncodedByteList (byteView first.mem) (first.regs.get .rdi) inner := by
    rw [firstArg]
    apply typed.preserved layout accessible g.inputValid
    intro p h
    have off : ¬ whole.Contains p := fun q => g.stackInput p ⟨q,h⟩
    have same := (atPush p (fun q => off (inside 504 8 (by decide) p q))).trans
      (atSaves p (fun q => off (inside 648 48 (by decide) p q)))
    exact congrArg (fun byte => some (none, byte)) same
  have entryForFirst : ShaResources (shaAddress base) first inner extent authority := by
    apply ShaResources.of_caller_regions firstLoaded (by rw [slot]; exact callStackAlignment)
      (firstArg.symm ▸ g.inputAligned)
    · rw [firstSrc]; exact g.inputValid
    · rw [firstDest]; exact regionValid 600 32 (by decide)
    · rw [firstStack]; exact regionValid 0 512 (by decide)
    · exact g.imageValid
    · rw [firstSrc, firstStack]; exact fun p h => g.stackInput p ⟨inside 0 512 (by decide) p h.2, h.1⟩
    · rw [firstStack]; exact fun p h => imageElsewhere p h.1 (inside 0 512 (by decide) p h.2)
    · rw [firstStack, firstDest]; exact regionSlices_disjoint whole 0 512 600 32 valid (by decide) (fits _ _ (by decide))
    · rw [firstDest]; exact fun p h => imageElsewhere p h.1 (inside 600 32 (by decide) p h.2)
    · rw [firstSrc, firstDest]; exact fun p h => g.stackInput p ⟨inside 600 32 (by decide) p h.2, h.1⟩
    · exact g.codeCanonical
    · rw [firstSrc]; exact g.inputCanonical
    · rw [firstStack]; exact fun p h => g.stackCanonical p (inside 0 512 (by decide) p h)
    · rw [firstDest]; exact fun p h => g.stackCanonical p (inside 600 32 (by decide) p h)
    · rw [firstSrc]; exact g.inputRead
    · exact g.imageRead
    · rw [firstStack]; exact fun p h => g.stackRead p (inside 0 512 (by decide) p h)
    · rw [firstStack]; exact fun p h => g.stackWrite p (inside 0 512 (by decide) p h)
    · rw [firstDest]; exact fun p h => g.stackWrite p (inside 600 32 (by decide) p h)
    · exact g.shaExecutable
  have readyFirst := establish_sha_entry layout accessible sizeBound lengthBound firstEncoding entryForFirst
    (inner_target base start startPC) startLive (by rw [inner_link base start startPC]; exact g.innerLinkCanonical)
  have keyOutside (i : Fin 64) : ¬ whole.Contains (start.regs.get .rsi + BitVec.ofNat 64 i.val) := by
    rw [startKey]
    exact fun h => g.stackKey _ ⟨h, caller_region_contains_offset _ g.keyValid i.val i.isLt⟩
  have padBase : (regionSlice whole 536 64).base = start.regs.get .rsp + 24#64 := by
    rw [area 536 64 (by decide), startSP, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨after, ⟨body⟩⟩ := finish_body base start inner k0 extent authority startLive startPC shaCanon
    g.outerLinkCanonical readyFirst
    (by intro i; rw [atPush _ (fun h => keyOutside i (inside 504 8 (by decide) _ h)),
      atSaves _ (fun h => keyOutside i (inside 648 48 (by decide) _ h)), startKey]; exact keyAt i)
    (by rw [firstStack]; exact fun i h => keyOutside i (inside 0 512 (by decide) _ h))
    (by rw [firstDest]; exact fun i h => keyOutside i (inside 600 32 (by decide) _ h))
    (by
      intro i
      have h := delta 512 24 (by decide) _ (fun hit => keyOutside i (inside 512 24 (by decide) _ hit))
      have addr : (regionSlice whole 512 24).base = start.regs.get .rsp := prefixBase
      rwa [addr] at h)
    (by
      intro i
      have h := delta 536 64 (by decide) _ (fun hit => keyOutside i (inside 536 64 (by decide) _ hit))
      rwa [padBase] at h)
    (by
      intro mid events header mask outerList serial headerRun maskRun padRun listSP listMac listFrame
      let last := outerCallState outerList
      obtain ⟨arg, out, stk, callMemory⟩ := outer_call_registers outerList
      have main : inputRegion last 120 = outer := by
        change (⟨(outerCallState outerList).regs.get .rdi, 120⟩ : Region) = ⟨outer.base, 120⟩
        rw [arg, listSP, show outer.base = start.regs.get .rsp from prefixBase]
      have target : outputRegion last = finishMac s := by
        change (⟨(outerCallState outerList).regs.get .rsi, 32⟩ : Region) = ⟨s.regs.get .rdx, 32⟩
        rw [out, listMac, startDest]
      have stack : Crypto.X86_64.stackRegion last = nested := by
        change (⟨last.regs.get .rsp - 504#64, 512⟩ : Region) = _
        rw [stk, selection outerList listSP, ← slot]
        exact firstStack
      have lastSlot : last.regs.get .rsp = push.base := stk.trans (selection outerList listSP)
      have code : ImageLoaded (shaAddress base) last.mem := by
        intro i hi
        let p := shaAddress base + BitVec.ofNat 64 i
        have off := imageElsewhere p (caller_region_contains_offset _ g.imageValid i hi)
        rw [callMemory, selection outerList listSP,
          store64_outside _ _ _ _ (delta 504 8 (by decide) p (fun h => off (inside 504 8 (by decide) p h))),
          listFrame p (by rw [← prefixBase]; exact delta 512 88 (by decide) p (fun h => off (inside 512 88 (by decide) p h))),
          serial.result.frame p (by rw [firstDest]; exact fun h => off (inside 600 32 (by decide) p h))
            (by rw [firstStack]; exact fun h => off (inside 0 512 (by decide) p h))]
        exact firstLoaded i hi
      apply ShaResources.of_caller_regions code (by rw [lastSlot]; exact callStackAlignment)
      · rw [arg, listSP, startSP]
        have bound := frame_base_end sp 184 (by omega)
        have align := g.aligned
        change sp.toNat % 16 = 8 at align
        change (sp - 184#64).toNat % 8 = 0
        omega
      · rw [main]; exact regionValid 512 120 (by decide)
      · rw [target]; exact g.macValid
      · rw [stack]; exact regionValid 0 512 (by decide)
      · exact g.imageValid
      · rw [main, stack]; exact fun p h =>
          regionSlices_disjoint whole 0 512 512 120 valid (by decide) (fits _ _ (by decide)) p ⟨h.2, h.1⟩
      · rw [stack]; exact fun p h => imageElsewhere p h.1 (inside 0 512 (by decide) p h.2)
      · rw [stack, target]; exact fun p h => g.stackMac p ⟨inside 0 512 (by decide) p h.1, h.2⟩
      · rw [target]; exact fun p h => g.macImage p ⟨h.2, h.1⟩
      · rw [main, target]; exact fun p h => g.stackMac p ⟨inside 512 120 (by decide) p h.1, h.2⟩
      · exact g.codeCanonical
      · rw [main]; exact fun p h => g.stackCanonical p (inside 512 120 (by decide) p h)
      · rw [stack]; exact fun p h => g.stackCanonical p (inside 0 512 (by decide) p h)
      · rw [target]; exact g.macCanonical
      · rw [main]; exact fun p h => g.stackRead p (inside 512 120 (by decide) p h)
      · exact g.imageRead
      · rw [stack]; exact fun p h => g.stackRead p (inside 0 512 (by decide) p h)
      · rw [stack]; exact fun p h => g.stackWrite p (inside 0 512 (by decide) p h)
      · rw [target]; exact g.macWrite
      · exact g.shaExecutable)
  have writesPreserved (p : Val) (offNested : ¬ nested.Contains p) (offDigest : ¬ innerOut.Contains p)
      (offPrefix : ¬ localPrefix.Contains p) (offMac : ¬ (finishMac s).Contains p) :
      after.mem.read p = start.mem.read p := by
    obtain ⟨_, output, stack, memory⟩ := outer_call_registers body.outerList
    have outputReg : outputRegion (outerCallState body.outerList) = finishMac s := by
      change (⟨(outerCallState body.outerList).regs.get .rsi, 32⟩ : Region) = ⟨s.regs.get .rdx, 32⟩
      rw [output, body.outerListMac, startDest]
    have stackReg : Crypto.X86_64.stackRegion (outerCallState body.outerList) = nested := by
      change (⟨(outerCallState body.outerList).regs.get .rsp - 504#64, 512⟩ : Region) = _
      rw [stack, selection body.outerList body.outerListSP, ← slot]
      exact firstStack
    have offPush (h : push.Contains p) : False := offNested
      (regionSlice_inside (regionSlice whole 0 512) 504 8 (regionValid 0 512 (by decide)) (by change 504 + 8 ≤ 512; decide) p (by
        simpa only [regionSlice, BitVec.add_zero] using h))
    rw [body.outerHash.result.frame p (by rwa [outputReg]) (by rwa [stackReg]), memory,
      selection body.outerList body.outerListSP, store64_outside _ _ _ _ (delta 504 8 (by decide) p offPush),
      body.outerListFrame p (by rw [body.afterInnerSP, ← prefixBase]; exact delta 512 88 (by decide) p offPrefix),
      body.innerHash.result.frame p (by rwa [firstDest]) (by rwa [firstStack])]
    exact atPush p offPush
  have preserveOutside (p : Val) (offStack : ¬ whole.Contains p) (offMac : ¬ (finishMac s).Contains p) :
      after.mem.read p = s.mem.read p :=
    (writesPreserved p (fun h => offStack (inside 0 512 (by decide) p h))
       (fun h => offStack (inside 600 32 (by decide) p h))
       (fun h => offStack (inside 512 88 (by decide) p h)) offMac).trans
       (atSaves p (fun h => offStack (inside 648 48 (by decide) p h)))
  have returnAt : after.regs.get .rsp + 184#64 = sp := by rw [body.sp, startSP, BitVec.sub_add_cancel]
  have returnValue : after.mem.readSize .q (after.regs.get .rsp + 184#64) = s.mem.readSize .q sp := by
    rw [returnAt]
    apply Mem.readN_congr
    intro i hi
    let p := sp + BitVec.ofNat 64 i
    have h := caller_region_contains_offset (finishReturn s) g.returnValid i hi
    have off : ¬ whole.Contains p := by
      have endAt := frame_base_end sp 696 g.available
      intro held
      change (sp - 696#64).toNat ≤ p.toNat ∧ p.toNat < (sp - 696#64).toNat + 696 at held
      change sp.toNat ≤ p.toNat ∧ p.toNat < sp.toNat + 8 at h
      omega
    exact preserveOutside p off (fun mac => g.returnMac p ⟨h, mac⟩)
  have saveAt : after.regs.get .rsp + 136#64 = savedBase s := by
    rw [body.sp, entered_frame_stack, HmacRoutine.locals, BitVec.sub_add_cancel]
    rfl
  have saveValues (i : Fin 6) :
      after.mem.readSize .q (after.regs.get .rsp + 136#64 + BitVec.ofNat 64 (8 * (5 - i.val))) =
        s.regs.get (savedReg i) := by
    rw [saveAt]
    refine (Mem.readN_congr _ _ _ 8 ?_).trans (frame_saved_word .finish s i)
    intro j hj
    let p := savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j
    have inSaves : saves.Contains p := by
      change saves.Contains (savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← savedBaseAt]
      exact caller_region_contains_offset saves (regionValid 648 48 (by decide)) _ (by
        change savedOffset i + j < 48
        have hi := i.isLt
        unfold savedOffset
        omega)
    have noAlias (off n : Nat) (ordered : off + n ≤ 648) (h : (regionSlice whole off n).Contains p) : False :=
      regionSlices_disjoint whole off n 648 48 valid ordered (fits _ _ (by decide)) p ⟨h, inSaves⟩
    exact writesPreserved p (noAlias 0 512 (by decide)) (noAlias 600 32 (by decide))
      (noAlias 512 88 (by decide)) (fun hit => g.stackMac p ⟨inside 648 48 (by decide) p inSaves, hit⟩)
  obtain ⟨out, pro, epilogue, outSP, link, regs, output⟩ :=
    body.returned live returnValue g.returnCanonical saveValues
  have restored : out = restoredState after 136#64 7 := by
    have target : canonical (after.mem.readSize .q (after.regs.get .rsp + 184#64)) = true := by
      rw [returnValue]
      exact g.returnCanonical
    have expected := (returns after body.outerHash.result.live).2.2 target
    have same := Option.some.inj (epilogue.symm.trans expected)
    exact same
  have mem : out.mem = after.mem := by
    rw [restored]
    exact (restored_stack_and_link _ _ _).2.2
  have running : out.ms = none := by
    rw [restored, restored_live]
    exact body.outerHash.result.live
  have fetched (right : FinishFetchAuthority base s authority) :
      LinkedExecution base authority s (finishNativeEvents base s inner k0) out ∧ out.flags.df = false := by
    have atStack (off n : Nat) (fit : off + n ≤ 696) (j : Nat) (hj : j < n) :
        whole.Contains ((regionSlice whole off n).base + BitVec.ofNat 64 j) :=
      inside off n fit _ (caller_region_contains_offset _ (regionValid _ _ fit) j hj)
    have saveWrite (j : Nat) (hj : j < 48) :
        canonical (savedBase s + BitVec.ofNat 64 j) = true ∧
        authority.writable (savedBase s + BitVec.ofNat 64 j) := by
      rw [← savedBaseAt]
      have hit := atStack 648 48 (by decide) j hj
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have startDF := (entered_frame_direction .finish s).trans right.direction
    have outerSaved := run_range_observes (.inr (.inr rfl)) right.loaded right.immutableText
      (prologue_decoded .finish) pro (frame_prologue_ready .finish base authority s pc live right.direction right.text saveWrite)
    have callWrite (t : Cpu) (same : t.regs.get .rsp = start.regs.get .rsp) (j : Nat) (hj : j < 8) :
        canonical (t.regs.get .rsp - 8#64 + BitVec.ofNat 64 j) = true ∧
        authority.writable (t.regs.get .rsp - 8#64 + BitVec.ofNat 64 j) := by
      rw [same, ← firstSP, slot]
      have hit := atStack 504 8 (by decide) j hj
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have invokeInner := run_range_observes (.inr (.inr rfl))
      (outerSaved.keeps_routine finish right.loaded right.immutableText) right.immutableText
      finish_inner_call_decoded body.innerCall (by
        have allowed := finish_inner_setup_ready start startPC startLive startDF right.text (callWrite start rfl)
        simpa only [finish_inner_call_decoded, Option.getD_some] using allowed)
    have hashed := outerSaved.append (invokeInner.append (.shaCall body.innerHash (.nil _)))
    have afterInnerLive := body.innerHash.result.live
    have afterInnerDF : body.afterInner.flags.df = false := by
      have stable := congrArg (fun p => p.2.2.2.2.2) body.innerHash.platform
      exact stable.trans startDF
    have headerWrite (j : Nat) (hj : j < 24) :
        canonical (body.afterInner.regs.get .rsp + BitVec.ofNat 64 j) = true ∧
        authority.writable (body.afterInner.regs.get .rsp + BitVec.ofNat 64 j) := by
      rw [body.afterInnerSP, ← prefixBase]
      have hit := atStack 512 88 (by decide) j (by omega)
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have header := run_range_observes (.inr (.inr rfl))
      (hashed.keeps_routine finish right.loaded right.immutableText) right.immutableText
      finish_header_decoded body.writeHeader (by
        have allowed := finish_header_ready body.afterInner body.innerReturn afterInnerLive afterInnerDF right.text headerWrite
        simpa only [finish_header_decoded, Option.getD_some] using allowed)
    have headerEq := Option.some.inj (body.writeHeader.symm.trans (finish_header _ afterInnerLive))
    have headerPC : body.header.rip = routineAddress base finish + 0x3b#64 := by
      rw [headerEq]
      change body.afterInner.rip + 26#64 = _
      rw [body.innerReturn, BitVec.add_assoc]
      rfl
    have headerLive : body.header.ms = none := by rw [headerEq]; exact afterInnerLive
    have headerDF : body.header.flags.df = false := by rw [headerEq]; exact afterInnerDF
    have built := hashed.append header
    have loadMask := run_range_observes (.inr (.inr rfl))
      (built.keeps_routine finish right.loaded right.immutableText) right.immutableText
      opad_mask_decoded body.preparePad (by
        have allowed := finish_mask_ready body.header headerPC headerLive headerDF right.text
        simpa only [opad_mask_decoded, Option.getD_some] using allowed)
    have exactMask : runRange finish 0x3b 1 body.header = some (outerMaskState body.header) := by
      simp only [runRange, opad_mask_decoded, Option.map_some, X86.run, List.foldl_cons, List.foldl_nil,
        mov_mask _ _ headerLive, outerMaskState]
    have maskEq := Option.some.inj (body.preparePad.symm.trans exactMask)
    have maskPC : body.mask.rip = routineAddress base finish + 0x45#64 := by
      rw [maskEq]
      change body.header.rip + 10#64 = _
      rw [headerPC, BitVec.add_assoc]
      rfl
    have maskLive : body.mask.ms = none := by rw [maskEq]; exact headerLive
    have maskDF : body.mask.flags.df = false := by rw [maskEq]; exact headerDF
    have maskRSP : body.mask.regs.get .rsp = start.regs.get .rsp := by
      rw [maskEq, headerEq]
      simp (config := {decide := true}) only [outerMaskState, Regs.get_set_ne, body.afterInnerSP]
    have maskKey : body.mask.regs.get .rbx = start.regs.get .rsi := by
      rw [maskEq, headerEq]
      simp (config := {decide := true}) only [outerMaskState, Regs.get_set_ne]
      exact (body.innerHash.result.saved ⟨0, by decide⟩).trans (inner_call_registers start).2.2.1
    have maskDst : padDestination body.mask true = (regionSlice whole 536 64).base := by
      change body.mask.regs.get .rsp + 24#64 = _
      rw [maskRSP, padBase]
    have apart (j : Fin 64) : 64 ≤
        (body.mask.regs.get (sourceReg true) + BitVec.ofNat 64 j.val - padDestination body.mask true).toNat := by
      change 64 ≤ (body.mask.regs.get .rbx + BitVec.ofNat 64 j.val - padDestination body.mask true).toNat
      rw [maskKey, maskDst]
      exact delta 536 64 (by decide) _ (fun h => keyOutside j (inside 536 64 (by decide) _ h))
    have padRead (j : Nat) (hj : j < 64) :
        canonical (body.mask.regs.get (sourceReg true) + BitVec.ofNat 64 j) = true ∧
        authority.readable (body.mask.regs.get (sourceReg true) + BitVec.ofNat 64 j) := by
      change canonical (body.mask.regs.get .rbx + BitVec.ofNat 64 j) = true ∧
        authority.readable (body.mask.regs.get .rbx + BitVec.ofNat 64 j)
      rw [maskKey, startKey]
      have hit := caller_region_contains_offset _ g.keyValid j hj
      exact ⟨g.keyCanonical _ hit, g.keyRead _ hit⟩
    have padWrite (j : Nat) (hj : j < 64) :
        canonical (padDestination body.mask true + BitVec.ofNat 64 j) = true ∧
        authority.writable (padDestination body.mask true + BitVec.ofNat 64 j) := by
      rw [maskDst]
      have hit := atStack 536 64 (by decide) j hj
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have throughMask := built.append loadMask
    have padded := run_range_observes (.inr (.inr rfl))
      (throughMask.keeps_routine finish right.loaded right.immutableText) right.immutableText
      finish_pad_decoded body.writePad (pad_range_ready true base body.mask authority maskLive maskDF apart
        maskPC right.text padRead padWrite)
    have padResult : X86.run (padCode true 8) body.mask = body.outerList := by
      simpa only [runRange, finish_pad_decoded, Option.map_some, Option.some.injEq] using body.writePad
    have result := pad_run_prefix body.mask true 8 maskLive (by decide) apart
    rw [padResult] at result
    have outerPC : body.outerList.rip = routineAddress base finish + 0xa4#64 := by
      rw [result.pc, maskPC, BitVec.add_assoc]
      rfl
    have outerDF := result.direction.trans maskDF
    have throughPad := throughMask.append padded
    have invokeOuter := run_range_observes (.inr (.inr rfl))
      (throughPad.keeps_routine finish right.loaded right.immutableText) right.immutableText
      finish_outer_call_decoded body.outerCall (by
        have allowed := finish_outer_setup_ready body.outerList outerPC result.live outerDF right.text
          (callWrite body.outerList body.outerListSP)
        simpa only [finish_outer_call_decoded, Option.getD_some] using allowed)
    have throughOuter := throughPad.append (invokeOuter.append (.shaCall body.outerHash (.nil _)))
    have afterDF : after.flags.df = false := by
      have stable := congrArg (fun p => p.2.2.2.2.2) body.outerHash.platform
      exact stable.trans outerDF
    have returnRead (j : Nat) (hj : j < 56) :
        canonical (after.regs.get .rsp + 136#64 + BitVec.ofNat 64 j) = true ∧
        authority.readable (after.regs.get .rsp + 136#64 + BitVec.ofNat 64 j) := by
      rw [saveAt]
      by_cases inFrame : j < 48
      · rw [← savedBaseAt]
        have hit := atStack 648 48 (by decide) j inFrame
        exact ⟨g.stackCanonical _ hit, g.stackRead _ hit⟩
      · have address : savedBase s + BitVec.ofNat 64 j = sp + BitVec.ofNat 64 (j - 48) := by
          have sum : j = 48 + (j - 48) := by omega
          nth_rw 1 [sum]
          rw [BitVec.ofNat_add, ← BitVec.add_assoc]
          exact congrArg (· + BitVec.ofNat 64 (j - 48)) (BitVec.sub_add_cancel _ _)
        rw [address]
        exact right.returnRead _ (by omega)
    have leave := run_range_observes (.inr (.inr rfl))
      (throughOuter.keeps_routine finish right.loaded right.immutableText) right.immutableText
      finish_return_decoded epilogue (frame_epilogue_ready .finish base authority after body.outerReturn
        body.outerHash.result.live afterDF right.text returnRead)
    have frontEvents : rangeEvents (saveCode .finish) s =
        frameEnterEvents .finish (routineAddress base finish) (s.regs.get .rsp) := by
      rw [frame_prologue_events _ _ live, pc]
    have startEvents := finish_inner_setup_events start startPC startLive
    rw [startSP] at startEvents
    have headerEvents := finish_header_events body.afterInner body.innerReturn afterInnerLive
    rw [body.afterInnerSP, startSP] at headerEvents
    have maskEvents := finish_mask_events body.header headerPC
    have padEvents := (pad_code_facts true 8 body.mask maskLive maskDF (by decide) apart).2.2
    change _ = x86PadEvents true body.mask.rip (body.mask.regs.get .rbx) (body.mask.regs.get .rsp) 8 at padEvents
    rw [maskPC, maskKey, startKey, maskRSP, startSP] at padEvents
    have outerEvents := finish_outer_setup_events body.outerList outerPC result.live
    rw [body.outerListSP, startSP] at outerEvents
    have retEvents := frame_return_events .finish after body.outerHash.result.live
    rw [body.outerReturn, body.sp, startSP] at retEvents
    simp only [finish_inner_call_decoded, finish_header_decoded, opad_mask_decoded,
      finish_outer_call_decoded, Option.getD_some, start, sp] at startEvents headerEvents maskEvents outerEvents
    simp only [HmacRoutine.locals, HmacRoutine.allocLength, sp] at retEvents
    simp only [sp] at padEvents
    let frame := s.regs.get .rsp - 184#64
    let innerSHA := shaTraceContext s (frame - 8#64) (s.regs.get .rdi) (frame + 88#64)
    let outerSHA := shaTraceContext s (frame - 8#64) frame (s.regs.get .rdx)
    obtain ⟨innerSP, innerInput, innerOutput⟩ := sha_trace_context s (frame - 8#64) (s.regs.get .rdi) (frame + 88#64)
    have innerTrace : body.innerEvents = callEvents (shaAddress base) innerSHA inner := by
      rw [body.innerHash.publicTrace]
      exact call_events_same_arguments (firstSP.trans ((congrArg (· - 8#64) startSP).trans innerSP.symm))
        (firstArg.trans innerInput.symm) (firstOut.trans ((congrArg (· + 88#64) startSP).trans innerOutput.symm))
        rfl rfl
    obtain ⟨lastInput, lastOutput, lastSP, _⟩ := outer_call_registers body.outerList
    obtain ⟨outerSP, outerInput, outerOutput⟩ := sha_trace_context s (frame - 8#64) frame (s.regs.get .rdx)
    have stackEq := body.outerListSP.trans startSP
    have outerTrace : body.outerEvents = callEvents (shaAddress base) outerSHA (hmacOuter k0 (sha256 inner).2) := by
      rw [body.outerHash.publicTrace]
      exact call_events_same_arguments (lastSP.trans ((congrArg (· - 8#64) stackEq).trans outerSP.symm))
        ((lastInput.trans stackEq).trans outerInput.symm)
        ((lastOutput.trans (body.outerListMac.trans startDest)).trans outerOutput.symm) rfl rfl
    refine ⟨?_, ?_⟩
    · rw [frontEvents] at outerSaved
      rw [startEvents] at invokeInner
      rw [headerEvents] at header
      rw [maskEvents] at loadMask
      rw [padEvents] at padded
      rw [outerEvents] at invokeOuter
      rw [retEvents] at leave
      have first := LinkedExecution.shaCall body.innerHash (.nil body.afterInner)
      have last := LinkedExecution.shaCall body.outerHash (.nil after)
      rw [List.append_nil, innerTrace] at first
      rw [List.append_nil, outerTrace] at last
      unfold finishNativeEvents
      have startRun := (outerSaved.append invokeInner).append first
      have throughPad := ((startRun.append header).append loadMask).append padded
      exact (((throughPad.append invokeOuter).append last).append leave)
    · rw [restored, restored_direction]
      exact afterDF
  exact ⟨out, ⟨⟨after, pro, body, epilogue, fetched, running, outSP, link, regs, output,
    fun p a b => by rw [mem]; exact preserveOutside p a b⟩⟩⟩

structure FinishPublic (s t : Cpu) (a b : ByteList) : Prop where
  stack : s.regs.get .rsp = t.regs.get .rsp
  input : s.regs.get .rdi = t.regs.get .rdi
  key : s.regs.get .rsi = t.regs.get .rsi
  output : s.regs.get .rdx = t.regs.get .rdx
  offset : a.offset = b.offset
  count : a.bytes.size = b.bytes.size

theorem finish_native_events_equal {base : Val} {s t : Cpu} {a b : ByteList} {k0 k1 : HmacKeyBlock}
    (same : FinishPublic s t a b) :
    finishNativeEvents base s a k0 = finishNativeEvents base t b k1 := by
  let lsp := s.regs.get .rsp - 184#64
  let rsp := t.regs.get .rsp - 184#64
  have sp : lsp = rsp := congrArg (· - 184#64) same.stack
  obtain ⟨lStack, lIn, lOut⟩ := sha_trace_context s (lsp - 8#64) (s.regs.get .rdi) (lsp + 88#64)
  obtain ⟨rStack, rIn, rOut⟩ := sha_trace_context t (rsp - 8#64) (t.regs.get .rdi) (rsp + 88#64)
  have inner := call_events_same_arguments (base := shaAddress base)
    (lStack.trans ((congrArg (· - 8#64) sp).trans rStack.symm))
    (lIn.trans (same.input.trans rIn.symm))
    (lOut.trans ((congrArg (· + 88#64) sp).trans rOut.symm)) same.offset same.count
  obtain ⟨loStack, loIn, loOut⟩ := sha_trace_context s (lsp - 8#64) lsp (s.regs.get .rdx)
  obtain ⟨roStack, roIn, roOut⟩ := sha_trace_context t (rsp - 8#64) rsp (t.regs.get .rdx)
  have outer := call_events_same_arguments (base := shaAddress base)
    (a := hmacOuter k0 (sha256 a).2) (b := hmacOuter k1 (sha256 b).2)
    (loStack.trans ((congrArg (· - 8#64) sp).trans roStack.symm))
    (loIn.trans (sp.trans roIn.symm)) (loOut.trans (same.output.trans roOut.symm))
    (by rfl) (by rw [hmacOuter_length, hmacOuter_length])
  dsimp only [lsp, rsp] at inner outer
  simp only [finishNativeEvents]
  rw [inner, outer, same.stack, same.key]

end Crypto.HMACSHA256.X86_64
