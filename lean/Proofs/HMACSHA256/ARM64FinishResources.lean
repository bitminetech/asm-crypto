import Proofs.HMACSHA256.ARM64Finish
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference
open Crypto.Baseline (Region)

def finishInput (s : Arm64.State) (extent : Nat) : Region := ⟨s.readReg64 .x0, extent⟩
def finishKey (s : Arm64.State) : Region := ⟨s.readReg64 .x1, 64⟩
def finishMac (s : Arm64.State) : Region := ⟨s.readReg64 .x2, 32⟩
def finishWorkspace (s : Arm64.State) : Region := stackRegion s.sp 640

/-- Caller-owned regions for the finishing helper. Both linked hashes share
the lower 416 bytes of the 640-byte stack allocation. -/
structure FinishResources (base : Addr) (s : Arm64.State) (extent : Nat) : Prop where
  available : 640 ≤ s.sp.toNat
  aligned : s.sp.toNat % 16 = 0
  inputAligned : (s.readReg64 .x0).toNat % 8 = 0
  outputAligned : (s.readReg64 .x2).toNat % 8 = 0
  inputValid : (finishInput s extent).Valid
  keyValid : (finishKey s).Valid
  macValid : (finishMac s).Valid
  imageValid : (callerImage (shaAddress base)).Valid
  stackInput : (finishWorkspace s).Disjoint (finishInput s extent)
  stackKey : (finishWorkspace s).Disjoint (finishKey s)
  stackMac : (finishWorkspace s).Disjoint (finishMac s)
  stackImage : (finishWorkspace s).Disjoint (callerImage (shaAddress base))
  macInput : (finishMac s).Disjoint (finishInput s extent)
  macKey : (finishMac s).Disjoint (finishKey s)
  macImage : (finishMac s).Disjoint (callerImage (shaAddress base))
  inputRead : ∀ p, (finishInput s extent).Contains p → s.mem.canRead p 1 = true
  keyRead : ∀ p, (finishKey s).Contains p → s.mem.canRead p 1 = true
  macWrite : ∀ p, (finishMac s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (finishWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (finishWorkspace s).Contains p → s.mem.canWrite p 1 = true

theorem stack_mask (sp : Addr) (aligned : sp.toNat % 16 = 0) : sp &&& 15#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change sp.toNat &&& (2^4 - 1) = 0
  simpa only [Nat.and_two_pow_sub_one_eq_mod] using aligned

set_option maxRecDepth 8192 in
set_option maxHeartbeats 7500000 in
/-- Complete the ARM64 finish helper from independent caller-owned input,
K0, output and stack regions. Establish both SHA-256 call contracts from the
actual serialized input and the matching grants. -/
theorem finish_execution_from_caller (base : Addr) (s : Arm64.State) (inner : ByteList)
    (k0 : HmacKeyBlock) (extent : Nat)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (typed : EncodedByteList s.mem (s.readReg64 .x0) inner)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (g : FinishResources base s extent) (pc : s.pc = routineAddress base finish)
    (live : s.status = .Running)
    (shaLoaded : (program (shaAddress base)).CodeLoaded s.mem)
    (loaded : (programAt finish (routineAddress base finish)).CodeLoaded s.mem) :
    ∃ out events, LinkedExecution base s events out ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, ¬ (finishWorkspace s).Contains p → ¬ (finishMac s).Contains p →
        out.mem.cells p = s.mem.cells p) ∧
      ∃ bodyOut, ∃ body : FinishBody base (enteredState s 224#64) bodyOut inner k0,
        events = body.nativeTrace := by
  let whole := finishWorkspace s
  let start := enteredState s 224#64
  let nested := regionSlice whole 0 416
  let innerOutput := regionSlice whole 600 32
  let outerInput := regionSlice whole 512 120
  let spill := regionSlice whole 416 96
  have wholeValid : whole.Valid := stackRegion_valid _ _ g.available
  have availableSmall : 224 ≤ s.sp.toNat := by have := g.available; omega
  have frameAlign : (s.sp - 224#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 224 g.aligned (by decide) availableSmall
  have startAligned : start.sp.toNat % 16 = 0 := frameAlign
  have aligned : s.spAligned = true := by
    simp [Arm64.State.spAligned, stack_mask _ g.aligned]
  have localAligned : (s.sp - 224#64) &&& 15#64 = 0#64 := stack_mask _ frameAlign
  have startSP : start.sp = s.sp - 224#64 := rfl
  have low : 416 ≤ start.sp.toNat := by
    have left := frame_base_end s.sp 224 availableSmall
    have total := g.available
    change 416 ≤ (s.sp - BitVec.ofNat 64 224).toNat
    omega
  have startPC : start.pc = routineAddress base finish + 0x1c#64 := by
    change s.pc + 28#64 = _
    rw [pc]
  have startRunning : start.status = .Running := live
  have startReg (r : Arm64.Reg) (gpr : ∃ j : BitVec 5, r = .gpr j ∧ j ≠ 29#5) :
      start.readReg64 r = s.readReg64 r := by
    obtain ⟨j, rfl, ne⟩ := gpr
    by_cases zero : j = 31#5
    · subst j
      rfl
    · simp only [start, enteredState, Arm64.State.setPC, Arm64.State.setMem]
      simp [Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.RegFile.read,
        Arm64.RegFile.write, Arm64.Reg.x29, zero, ne]
  have atInput : start.readReg64 .x0 = s.readReg64 .x0 := startReg _ ⟨0, rfl, by decide⟩
  have atKey : start.readReg64 .x1 = s.readReg64 .x1 := startReg _ ⟨1, rfl, by decide⟩
  have atMac : start.readReg64 .x2 = s.readReg64 .x2 := startReg _ ⟨2, rfl, by decide⟩
  have addr (off bytes : Nat) :
      (regionSlice whole (416 + off) bytes).base = start.sp + BitVec.ofNat 64 off := by
    change whole.base + BitVec.ofNat 64 (416 + off) = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    have root := congrArg Region.base (stackRegion_slice s.sp 640 416 bytes (by decide))
    change whole.base + 416#64 = s.sp - 224#64 at root
    rw [root, startSP]
  have span (off bytes : Nat) (fits : 416 + off + bytes ≤ 640) :
      (⟨start.sp + BitVec.ofNat 64 off, bytes⟩ : Region) = regionSlice whole (416 + off) bytes := by
    change (⟨start.sp + BitVec.ofNat 64 off, bytes⟩ : Region) =
      ⟨(regionSlice whole (416 + off) bytes).base, bytes⟩
    rw [addr off bytes]
  have sliceFits (off n : Nat) (fits : off + n ≤ 224) : 416 + off + n ≤ whole.bytes := by
    change _ ≤ 640
    omega
  have stackRead (off n : Nat) (fits : off + n ≤ 224) :
      s.mem.canRead (start.sp + BitVec.ofNat 64 off) n = true := by
    rw [← addr off n]
    exact caller_region_read _ whole wholeValid g.stackRead (416 + off) n (sliceFits off n fits)
  have stackWrite (off n : Nat) (fits : off + n ≤ 224) :
      s.mem.canWrite (start.sp + BitVec.ofNat 64 off) n = true := by
    rw [← addr off n]
    exact caller_region_write _ whole wholeValid g.stackWrite (416 + off) n (sliceFits off n fits)
  have enterWrites (i : Fin 12) :
      s.mem.canWrite (s.sp - 224#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true :=
    stackWrite _ 8 (by have := i.isLt; omega)
  have enter := enter_finish s aligned localAligned enterWrites
  have prog : finish = entry ∨ finish = key ∨ finish = finish := .inr (.inr rfl)
  obtain ⟨_, prologue, _⟩ := run_range_fetched prog (by simpa only [BitVec.add_zero] using pc)
    (by decide) loaded (by decide +kernel) enter startRunning
  have initial := prologue.grants
  have prologueImage := prologue.keeps_code _ shaLoaded
  have codeAt := inner_target base start startPC
  have leavingSp : (innerCallState start).sp = start.sp := (inner_call_registers start).2.2.2.2.2.1
  obtain ⟨inPtr, digestPtr, keySaved, macSaved, _, _, callMem⟩ := inner_call_registers start
  have inputRegion : callerInput (innerCallState start) extent = finishInput s extent := by
    simp only [callerInput, finishInput, inPtr, atInput]
  have nestedStack : callerStack (innerCallState start) = nested := by
    change (⟨(innerCallState start).sp - 416#64, 416⟩ : Region) = _
    rw [leavingSp, startSP, BitVec.sub_sub]
    exact (stackRegion_slice _ 640 0 416 (by decide)).symm
  have localDigest : callerOutput (innerCallState start) = innerOutput := by
    change (⟨(innerCallState start).readReg64 .x1, 32⟩ : Region) = _
    rw [digestPtr]
    exact span 184 32 (by decide)
  have innerFits : 600 + 32 ≤ whole.bytes := by change 600 + 32 ≤ 640; decide
  have nestedFits : 0 + 416 ≤ whole.bytes := by change 0 + 416 ≤ 640; decide
  have outerFits : 512 + 120 ≤ whole.bytes := by change 512 + 120 ≤ 640; decide
  have spillFits : 416 + 96 ≤ whole.bytes := by change 416 + 96 ≤ 640; decide
  have nestedValid : nested.Valid := regionSlice_valid _ _ _ wholeValid nestedFits
  have localValid : innerOutput.Valid := regionSlice_valid _ _ _ wholeValid innerFits
  have outerValid : outerInput.Valid := regionSlice_valid _ _ _ wholeValid outerFits
  have inNested (p : Addr) (h : nested.Contains p) : whole.Contains p :=
    regionSlice_inside _ _ _ wholeValid nestedFits p h
  have inLocal (p : Addr) (h : innerOutput.Contains p) : whole.Contains p :=
    regionSlice_inside _ _ _ wholeValid innerFits p h
  have inOuter (p : Addr) (h : outerInput.Contains p) : whole.Contains p :=
    regionSlice_inside _ _ _ wholeValid outerFits p h
  have startKeep (p : Addr) (outside : ¬ whole.Contains p) : start.mem.cells p = s.mem.cells p := by
    have valid : spill.Valid := regionSlice_valid _ _ _ wholeValid spillFits
    have off : ¬ spill.Contains p := fun h => outside (regionSlice_inside _ _ _ wholeValid spillFits p h)
    have delta := caller_outside_delta spill valid p off
    change 96 ≤ (p - (regionSlice whole (416 + 0) 96).base).toNat at delta
    rw [addr 0 96, BitVec.add_zero, startSP] at delta
    exact writeWords_outside _ _ _ 12 _ delta
  have value : EncodedByteList (innerCallState start).mem ((innerCallState start).readReg64 .x0) inner := by
    rw [callMem, inPtr, atInput]
    exact typed.preserved layout accessible g.inputValid
      (fun p h => startKeep p (fun held => g.stackInput p ⟨held, h⟩))
  have firstSha : ShaResources (shaAddress base) (innerCallState start) extent := {
    loaded := by rw [callMem]; exact prologueImage
    messageAligned := by rw [inPtr, atInput]; exact g.inputAligned
    digestAligned := by
      rw [digestPtr, BitVec.toNat_add]
      change ((start.sp.toNat + 184) % 2 ^ 64) % 8 = 0
      omega
    stackAligned := leavingSp.symm ▸ startAligned
    stackAvailable := leavingSp.symm ▸ low
    inputValid := inputRegion.symm ▸ g.inputValid
    outputValid := localDigest.symm ▸ localValid
    stackValid := nestedStack.symm ▸ nestedValid
    imageValid := g.imageValid
    outputInput := fun p h => g.stackInput p ⟨inLocal p (localDigest ▸ h.1), inputRegion ▸ h.2⟩
    outputStack := by
      rw [localDigest, nestedStack]
      intro p h
      exact regionSlices_disjoint whole 0 416 600 32 wholeValid (by decide) innerFits p ⟨h.2, h.1⟩
    outputImage := fun p h => g.stackImage p ⟨inLocal p (localDigest ▸ h.1), h.2⟩
    stackInput := fun p h => g.stackInput p ⟨inNested p (nestedStack ▸ h.1), inputRegion ▸ h.2⟩
    stackImage := fun p h => g.stackImage p ⟨inNested p (nestedStack ▸ h.1), h.2⟩
    inputRead := fun p h => by rw [callMem]; exact initial.read _ _ (g.inputRead p (inputRegion ▸ h))
    stackRead := fun p h => by rw [callMem]; exact initial.read _ _ (g.stackRead p (inNested p (nestedStack ▸ h)))
    stackWrite := fun p h => by rw [callMem, initial.write]; exact g.stackWrite p (inNested p (nestedStack ▸ h))
    outputWrite := fun p h => by rw [callMem, initial.write]; exact g.stackWrite p (inLocal p (localDigest ▸ h))
  }
  have firstEntry := establish_sha_entry layout accessible sizeBound lengthBound value firstSha codeAt
    (show (innerCallState start).status = .Running from startRunning)
  have actualKey (i : Fin 64) : start.mem.read8 (start.readReg64 .x1 + BitVec.ofNat 64 i.val) =
      k0[i.val].toBitVec := by
    rw [atKey]
    have inside := caller_region_contains_offset _ g.keyValid i.val i.isLt
    exact (read8_of_cell _ (startKeep _ (fun hit => g.stackKey _ ⟨hit, inside⟩))).trans (keyAt i)
  have offKey (i : Fin 64) {off n : Nat} (fit : off + n ≤ 224) :
      n ≤ (start.readReg64 .x1 + BitVec.ofNat 64 i.val - (start.sp + BitVec.ofNat 64 off)).toNat := by
    let slice := regionSlice whole (416 + off) n
    have valid : slice.Valid := regionSlice_valid _ _ _ wholeValid (sliceFits _ _ fit)
    have h := caller_outside_delta slice valid (start.readReg64 .x1 + BitVec.ofNat 64 i.val) (by
      intro hit
      apply g.stackKey _
      refine ⟨regionSlice_inside _ _ _ wholeValid (sliceFits _ _ fit) _ hit, ?_⟩
      rw [atKey]
      exact caller_region_contains_offset _ g.keyValid i.val i.isLt)
    change n ≤ (start.readReg64 .x1 + BitVec.ofNat 64 i.val -
      (regionSlice whole (416 + off) n).base).toNat at h
    rwa [addr] at h
  have keyNested (i : Fin 64) :
      416 ≤ (start.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack (innerCallState start)).toNat := by
    have h := caller_outside_delta nested nestedValid (start.readReg64 .x1 + BitVec.ofNat 64 i.val) (by
      intro hit
      apply g.stackKey _
      refine ⟨inNested _ hit, ?_⟩
      rw [atKey]
      exact caller_region_contains_offset _ g.keyValid i.val i.isLt)
    rw [← nestedStack] at h
    exact h
  have bodyResult := finish_body base start inner k0 extent startPC firstEntry
    (by simp [Arm64.State.spAligned, startSP, localAligned]) actualKey keyNested
    (fun i => offKey i (off := 184) (n := 32) (by decide))
    (fun i => offKey i (off := 96) (n := 24) (by decide))
    (fun i => offKey i (off := 120) (n := 64) (by decide))
  obtain ⟨bodyOut, ⟨body⟩⟩ := bodyResult (by
    intro mid observations call
    have actualSP := call.abi.stack.trans leavingSp
    have savedKey : mid.readReg64 .x19 = s.readReg64 .x1 := by
      have h := congrFun call.abi.nonvolatile (⟨1, by decide⟩ : Fin 13)
      exact h.trans (keySaved.trans atKey)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [actualSP, call.grants.write, callMem, initial.write, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact stackWrite _ _ (by have := i.isLt; omega)
    · intro i
      rw [actualSP, call.grants.write, callMem, initial.write, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact stackWrite _ _ (by have := i.isLt; omega)
    · intro i
      rw [savedKey]
      apply call.grants.read
      rw [callMem]
      apply initial.read
      exact caller_region_read _ _ g.keyValid g.keyRead (8 * i.val) 8 (by have := i.isLt; change _ ≤ 64; omega)) (by
    intro mid observations header mask outer hashed headerRun maskRun padRun outerSP outerMac
    have localA := run_range_grants (by decide +kernel) headerRun
    have localB := run_range_grants (by decide +kernel) maskRun
    have localC := run_range_grants (by decide +kernel) padRun
    have afterSha : GrantsPreserved start.mem mid.mem := by
      have kept := hashed.grants
      rwa [callMem] at kept
    have stage := initial.trans (afterSha.trans (localA.trans (localB.trans localC)))
    obtain ⟨ptr, mac, _, rsp, memory⟩ := outer_call_registers outer
    have iRegion : callerInput (outerCallState outer) 120 = outerInput := by
      change (⟨(outerCallState outer).readReg64 .x0, 120⟩ : Region) = _
      rw [ptr, outerSP]
      exact span 96 120 (by decide)
    have oRegion : callerOutput (outerCallState outer) = finishMac s := by
      simp only [callerOutput, finishMac, mac, outerMac, atMac]
    have sRegion : callerStack (outerCallState outer) = nested := by
      unfold callerStack entryStack
      rw [rsp, outerSP, ← leavingSp]
      exact nestedStack
    have loadedMid : (program (shaAddress base)).CodeLoaded mid.mem :=
      (LinkedExecution.shaCall hashed (.nil mid)).keeps_code _ (by rw [callMem]; exact prologueImage)
    have loadedHeader := run_range_keeps_code (by decide +kernel) headerRun loadedMid
    have loadedMask := run_range_keeps_code (by decide +kernel) maskRun loadedHeader
    have loadedOuter := run_range_keeps_code (by decide +kernel) padRun loadedMask
    exact {
      loaded := by
        rw [memory]
        exact loadedOuter
      messageAligned := by
        rw [ptr, outerSP, BitVec.toNat_add]
        change ((start.sp.toNat + 96) % 2 ^ 64) % 8 = 0
        omega
      digestAligned := by rw [mac, outerMac, atMac]; exact g.outputAligned
      stackAligned := by rw [rsp, outerSP]; exact startAligned
      stackAvailable := by rw [rsp, outerSP]; exact low
      inputValid := iRegion.symm ▸ outerValid
      outputValid := oRegion.symm ▸ g.macValid
      stackValid := sRegion.symm ▸ nestedValid
      imageValid := g.imageValid
      outputInput := fun p h => g.stackMac p ⟨inOuter p (iRegion ▸ h.2), oRegion ▸ h.1⟩
      outputStack := fun p h => g.stackMac p ⟨inNested p (sRegion ▸ h.2), oRegion ▸ h.1⟩
      outputImage := fun p h => g.macImage p ⟨oRegion ▸ h.1, h.2⟩
      stackInput := by
        rw [sRegion, iRegion]
        exact regionSlices_disjoint whole 0 416 512 120 wholeValid (by decide) outerFits
      stackImage := fun p h => g.stackImage p ⟨inNested p (sRegion ▸ h.1), h.2⟩
      inputRead := fun p h => by rw [memory]; exact stage.read _ _ (g.stackRead p (inOuter p (iRegion ▸ h)))
      stackRead := fun p h => by rw [memory]; exact stage.read _ _ (g.stackRead p (inNested p (sRegion ▸ h)))
      stackWrite := fun p h => by rw [memory, stage.write]; exact g.stackWrite p (inNested p (sRegion ▸ h))
      outputWrite := fun p h => by rw [memory, stage.write]; exact g.macWrite p (oRegion ▸ h)
    })
  have spillRead (i : Fin 12) : bodyOut.mem.canRead (bodyOut.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [body.sp]
    have middle := (body.innerHash.grants.trans
      ((run_range_grants (by decide +kernel) body.writeHeader).trans
        ((run_range_grants (by decide +kernel) body.preparePad).trans
          (run_range_grants (by decide +kernel) body.writePad))))
    apply body.outerHash.grants.read
    rw [(outer_call_registers _).2.2.2.2]
    apply middle.read
    rw [callMem]
    exact initial.read _ _ (stackRead _ 8 (by have := i.isLt; omega))
  have macOffSpills (i : Fin 96) :
      32 ≤ (s.sp - 224#64 + BitVec.ofNat 64 i.val - s.readReg64 .x2).toNat := by
    have valid : spill.Valid := regionSlice_valid _ _ _ wholeValid spillFits
    have before : spill.base = s.sp - 224#64 := by
      have addr0 := addr 0 96
      rw [BitVec.add_zero, startSP] at addr0
      exact addr0
    have inside := caller_region_contains_offset spill valid i.val i.isLt
    rw [before] at inside
    exact caller_outside_delta _ g.macValid _ (fun hit =>
      g.stackMac _ ⟨regionSlice_inside _ _ _ wholeValid spillFits _ inside, hit⟩)
  obtain ⟨out, run, _, sp, link, running, saved, digest, memory⟩ :=
    body.execution_fetched pc loaded aligned localAligned enterWrites spillRead macOffSpills
  refine ⟨out, body.nativeTrace, run, sp, link, running, saved, digest, ?_, bodyOut, body, rfl⟩
  intro p offStack offMac
  have away (off n : Nat) (fits : off + n ≤ 224) :
      n ≤ (p - (start.sp + BitVec.ofNat 64 off)).toNat := by
    rw [← addr off n]
    exact caller_outside_delta (regionSlice whole (416 + off) n)
      (regionSlice_valid _ _ _ wholeValid (sliceFits off n fits)) p
      (fun hit => offStack (regionSlice_inside _ _ _ wholeValid (sliceFits off n fits) _ hit))
  have outsideNested : 416 ≤ (p - entryStack start).toNat := by
    have h := caller_outside_delta nested nestedValid p (fun hit => offStack (inNested p hit))
    rw [← nestedStack] at h
    change 416 ≤ (p - entryStack (innerCallState start)).toNat at h
    simpa only [entryStack, leavingSp] using h
  rw [memory]
  exact (body.frame p outsideNested (away 96 24 (by decide)) (away 120 64 (by decide))
    (away 184 32 (by decide)) (by rw [atMac]; exact caller_outside_delta _ g.macValid p offMac)).trans
    (startKeep p offStack)

end Crypto.HMACSHA256.ARM64
