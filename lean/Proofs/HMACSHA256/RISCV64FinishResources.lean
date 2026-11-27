import Proofs.HMACSHA256.RISCV64FinishTrace
import Proofs.HMACSHA256.RISCV64Finish
import Proofs.HMACSHA256.RISCV64FinishPermissions
import Proofs.HMACSHA256.RISCV64FramePermissions
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset allPerm_true_iff memoryBytes32)

def finishWorkspace (s : CPU) : Region := ⟨s.reg 2#5 - 480#64, 720⟩
def finishInput (s : CPU) (extent : Nat) : Region := ⟨s.reg 10#5, extent⟩
def finishKey (s : CPU) : Region := ⟨s.reg 11#5, 64⟩
def finishOutput (s : CPU) : Region := ⟨s.reg 12#5, 32⟩

/-- Borrowed resources at the first instruction after the helper's prologue.
The SHA-256 calls share the lower 480 bytes of the workspace. The helper
itself owns the upper 240 bytes. -/
structure FinishResources (base : Addr) (s : CPU) (extent : Nat) : Prop where
  available : 480 ≤ (s.reg 2#5).toNat
  aligned : (s.reg 2#5).toNat % 16 = 0
  inputAligned : (s.reg 10#5).toNat % 8 = 0
  outputAligned : (s.reg 12#5).toNat % 8 = 0
  stackValid : (finishWorkspace s).Valid
  inputValid : (finishInput s extent).Valid
  keyValid : (finishKey s).Valid
  outputValid : (finishOutput s).Valid
  stackInput : (finishWorkspace s).Disjoint (finishInput s extent)
  stackKey : (finishWorkspace s).Disjoint (finishKey s)
  stackOutput : (finishWorkspace s).Disjoint (finishOutput s)
  stackCode : (finishWorkspace s).Disjoint (callerImage (shaAddress base))
  outputCode : (finishOutput s).Disjoint (callerImage (shaAddress base))
  outputInput : (finishOutput s).Disjoint (finishInput s extent)
  inputRead : ∀ p, (finishInput s extent).Contains p → s.mem.canRead p 1 = true
  stackRead : ∀ p, (finishWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (finishWorkspace s).Contains p → s.mem.canWrite p 1 = true
  outputWrite : ∀ p, (finishOutput s).Contains p → s.mem.canWrite p 1 = true

private theorem finish_slice_base (s : CPU) (offset bytes : Nat) :
    (regionSlice (finishWorkspace s) (480 + offset) bytes).base =
      s.reg 2#5 + BitVec.ofNat 64 offset := by
  change s.reg 2#5 - 480#64 + BitVec.ofNat 64 (480 + offset) = _
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  have cancel : s.reg 2#5 - 480#64 + BitVec.ofNat 64 480 = s.reg 2#5 := BitVec.sub_add_cancel _ _
  rw [cancel]

private theorem slice_zero_base (s : CPU) :
    (regionSlice (finishWorkspace s) 0 480).base = s.reg 2#5 - 480#64 := BitVec.add_zero _

private theorem inner_digest_aligned (s : CPU) (sp : (s.reg 2#5).toNat % 16 = 0) :
    (s.reg 2#5 + 88#64).toNat % 8 = 0 := by
  rw [BitVec.toNat_add]
  change ((s.reg 2#5).toNat + 88) % (2 ^ 64) % 8 = 0
  omega

set_option maxHeartbeats 2600000 in
/-- Establish both SHA-256 call boundaries from disjoint slices of one
bounded workspace and the caller's independent grants. -/
theorem finish_body_from_resources (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock)
    (extent : Nat) (pc : s.pc = routineAddress base finish + 0x1c#64)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (typed : EncodedByteList s.mem (s.reg 10#5) inner)
    (grants : FinishResources base s extent) (code : ShaCode (shaAddress base) s.mem)
    (innerLink : ((routineAddress base finish + 0x26#64 : Addr)).toNat % 2 = 0)
    (outerLink : ((routineAddress base finish + 0xbc#64 : Addr)).toNat % 2 = 0)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec) :
    ∃ out, Nonempty (FinishBody base s out inner k0) := by
  let work := finishWorkspace s
  let stack := regionSlice work 0 480
  let pDigest := regionSlice work (480 + 88) 32
  let pOuter := regionSlice work 480 120
  have digestBase : pDigest.base = s.reg 2#5 + 88#64 := finish_slice_base s 88 32
  have outerBase : pOuter.base = s.reg 2#5 := by
    have same := finish_slice_base s 0 120
    change pOuter.base = s.reg 2#5 + 0#64 at same
    rw [BitVec.add_zero] at same
    exact same
  have stackInside (p : Addr) (inside : stack.Contains p) : work.Contains p :=
    regionSlice_inside work 0 480 grants.stackValid (by change _ ≤ 720; decide) p inside
  have digestInside (p : Addr) (inside : pDigest.Contains p) : work.Contains p :=
    regionSlice_inside work (480 + 88) 32 grants.stackValid (by change _ ≤ 720; decide) p inside
  have outerInside (p : Addr) (inside : pOuter.Contains p) : work.Contains p :=
    regionSlice_inside work 480 120 grants.stackValid (by change _ ≤ 720; decide) p inside
  obtain ⟨input, output, _, _, sp, _, mem⟩ := inner_call_registers s
  have stackA : callerStack (innerCallState s) = stack := by
    change (⟨(innerCallState s).reg 2#5 - (480 : Addr), 480⟩ : Region) = stack
    rw [sp]
    exact congrArg (fun addr => (⟨addr, 480⟩ : Region)) (slice_zero_base s).symm
  have bufferA : callerInput (innerCallState s) extent = finishInput s extent := by
    change (⟨(innerCallState s).reg 10#5, extent⟩ : Region) = ⟨s.reg 10#5, extent⟩
    rw [input]
  have digestA : callerOutput (innerCallState s) = pDigest := by
    change (⟨(innerCallState s).reg 11#5, 32⟩ : Region) = _
    rw [output]
    exact congrArg (fun addr => (⟨addr, 32⟩ : Region)) digestBase.symm
  have first : ShaResources (shaAddress base) (innerCallState s) extent := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ((innerCallState s).reg 10#5).toNat % 8 = 0
      rw [input]
      exact grants.inputAligned
    · change ((innerCallState s).reg 11#5).toNat % 8 = 0
      rw [output]
      exact inner_digest_aligned s grants.aligned
    · change ((innerCallState s).reg 2#5).toNat % 16 = 0
      rw [sp]
      exact grants.aligned
    · change 480 ≤ ((innerCallState s).reg 2#5).toNat
      rw [sp]
      exact grants.available
    · rw [bufferA]
      exact grants.inputValid
    · rw [digestA]
      exact regionSlice_valid _ _ _ grants.stackValid (by change _ ≤ 720; decide)
    · rw [digestA, bufferA]
      exact disjoint_subsets grants.stackInput digestInside (fun _ h => h)
    · rw [digestA, stackA]
      exact fun p hit => regionSlices_disjoint work 0 480 568 32 grants.stackValid (by decide) (by change _ ≤ 720; decide)
        p ⟨hit.2, hit.1⟩
    · rw [digestA]
      exact disjoint_subsets grants.stackCode digestInside (fun _ h => h)
    · rw [stackA, bufferA]
      exact disjoint_subsets grants.stackInput stackInside (fun _ h => h)
    · rw [stackA]
      exact disjoint_subsets grants.stackCode stackInside (fun _ h => h)
    · rw [bufferA, mem]
      exact grants.inputRead
    · rw [digestA, mem]
      exact fun p h => grants.stackWrite p (digestInside p h)
    · rw [stackA, mem]
      exact fun p h => grants.stackRead p (stackInside p h)
    · rw [stackA, mem]
      exact fun p h => grants.stackWrite p (stackInside p h)
  obtain ⟨outIn, outDst, outSp, outMem⟩ := outer_boundary_registers s
  have stackB : callerStack (outerBoundary s) = stack := by
    change (⟨(outerBoundary s).reg 2#5 - (480 : Addr), 480⟩ : Region) = stack
    rw [outSp]
    exact congrArg (fun addr => (⟨addr, 480⟩ : Region)) (slice_zero_base s).symm
  have bufferB : callerInput (outerBoundary s) 120 = pOuter := by
    change (⟨(outerBoundary s).reg 10#5, 120⟩ : Region) = _
    rw [outIn]
    exact congrArg (fun addr => (⟨addr, 120⟩ : Region)) outerBase.symm
  have digestB : callerOutput (outerBoundary s) = finishOutput s := by
    change (⟨(outerBoundary s).reg 11#5, 32⟩ : Region) = ⟨s.reg 12#5, 32⟩
    rw [outDst]
  have second : ShaResources (shaAddress base) (outerBoundary s) 120 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ((outerBoundary s).reg 10#5).toNat % 8 = 0
      rw [outIn]
      have aligned := grants.aligned
      omega
    · change ((outerBoundary s).reg 11#5).toNat % 8 = 0
      rw [outDst]
      exact grants.outputAligned
    · change ((outerBoundary s).reg 2#5).toNat % 16 = 0
      rw [outSp]
      exact grants.aligned
    · change 480 ≤ ((outerBoundary s).reg 2#5).toNat
      rw [outSp]
      exact grants.available
    · rw [bufferB]
      exact regionSlice_valid _ _ _ grants.stackValid (by change _ ≤ 720; decide)
    · rw [digestB]
      exact grants.outputValid
    · rw [digestB, bufferB]
      exact fun p hit => grants.stackOutput p ⟨outerInside p hit.2, hit.1⟩
    · rw [digestB, stackB]
      exact fun p hit => grants.stackOutput p ⟨stackInside p hit.2, hit.1⟩
    · rw [digestB]
      exact grants.outputCode
    · rw [stackB, bufferB]
      exact regionSlices_disjoint work 0 480 480 120 grants.stackValid (by decide) (by change _ ≤ 720; decide)
    · rw [stackB]
      exact disjoint_subsets grants.stackCode stackInside (fun _ h => h)
    · rw [bufferB, outMem]
      exact fun p h => grants.stackRead p (outerInside p h)
    · rw [digestB, outMem]
      exact grants.outputWrite
    · rw [stackB, outMem]
      exact fun p h => grants.stackRead p (stackInside p h)
    · rw [stackB, outMem]
      exact fun p h => grants.stackWrite p (stackInside p h)
  have keyOutside (i : Fin 64) : ¬ work.Contains (s.reg 11#5 + BitVec.ofNat 64 i.val) := by
    intro inside
    exact grants.stackKey _ ⟨inside, caller_region_contains_offset (finishKey s) grants.keyValid i.val i.isLt⟩
  have outside (offset bytes : Nat) (fits : 480 + offset + bytes ≤ 720) (p : Addr)
      (away : ¬ work.Contains p) : bytes ≤ (p - (s.reg 2#5 + BitVec.ofNat 64 offset)).toNat := by
    let slice := regionSlice work (480 + offset) bytes
    have address : slice.base = s.reg 2#5 + BitVec.ofNat 64 offset := finish_slice_base s offset bytes
    rw [← address]
    exact caller_outside_delta slice (regionSlice_valid _ _ _ grants.stackValid fits) p
      (fun hit => away (regionSlice_inside _ _ _ grants.stackValid fits p hit))
  refine finish_body base s inner k0 extent pc layout accessible sizeBound lengthBound typed first code innerLink
    outerLink keyAt ?_ ?_ ?_ ?_ second ?_
  · intro i
    rw [stackA]
    exact fun hit => keyOutside i (stackInside _ hit)
  · intro i
    rw [digestA]
    exact fun hit => keyOutside i (digestInside _ hit)
  · intro i
    simpa only [BitVec.add_zero] using outside 0 24 (by decide) _ (keyOutside i)
  · intro i
    exact outside 24 64 (by decide) _ (keyOutside i)
  · intro p inside
    have away : ¬ work.Contains p := fun h => grants.stackCode _ ⟨h, inside⟩
    simpa only [BitVec.add_zero] using outside 0 88 (by decide) p away

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
private theorem finish_exec_preserved {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out)
    (granted : s.mem.canExec (routineAddress base finish) finish.image.size = true) :
    out.mem.canExec (routineAddress base finish) finish.image.size = true := by
  rwa [show out.mem.canExec (routineAddress base finish) finish.image.size =
    s.mem.canExec (routineAddress base finish) finish.image.size from allPerm_eq_of_perm run.perm _ _ _]

private theorem finish_spill_separate (s : CPU) (sp : 240 ≤ (s.reg 2#5).toNat)
    (separate : (⟨s.reg 2#5 - 240#64, 240⟩ : Region).Disjoint ⟨s.reg 12#5, 32⟩) :
    ∀ i : Fin 104, ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains
      ((enteredFrame .finish s).reg 2#5 + BitVec.ofNat 64 (128 + i.val)) := by
  intro i hit
  rw [enteredFrame_sp] at hit
  let frame : Region := ⟨s.reg 2#5 - 240#64, 240⟩
  have valid : frame.Valid := by
    change (s.reg 2#5 - 240#64).toNat + 240 ≤ 2 ^ 64
    rw [BitVec.toNat_sub]
    change (2 ^ 64 - 240 + (s.reg 2#5).toNat) % 2 ^ 64 + 240 ≤ 2 ^ 64
    have bound := (s.reg 2#5).isLt
    omega
  exact separate _ ⟨Crypto.ARM64.Imported.caller_region_contains_offset frame valid _
    (by have := i.isLt; change 128 + i.val < 240; omega), hit⟩

/-- The HMAC finish helper executes through both actual SHA-256 calls and
returns using its saved ABI registers. Permissions for all its local
instruction ranges follow from grants for code, the stack and the key. -/
theorem FinishBody.execution_from_grants {base : Addr} {s bodyOut : CPU}
    {inner : ByteList} {k0 : HmacKeyBlock}
    (body : FinishBody base (enteredFrame .finish s) bodyOut inner k0)
    (pc : s.pc = routineAddress base finish)
    (loaded : finish.Loaded (routineAddress base finish) s.mem.read8)
    (readonly : RoutineReadOnly finish base s.mem)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true)
    (spAligned : (s.reg 2#5 - 240#64).toNat % 8 = 0)
    (stackAvailable : 720 ≤ (s.reg 2#5).toNat)
    (stackRead : s.mem.canRead (s.reg 2#5 - 240#64) 240 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 240#64) 240 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyRead : s.mem.canRead (s.reg 11#5) 64 = true)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0)
    (separate : (⟨s.reg 2#5 - 240#64, 240⟩ : Region).Disjoint ⟨s.reg 12#5, 32⟩) :
    ∃ out events,
      ProgramExecution base s events out ∧ events.length ≤ 75 + callSteps inner.bytes.size + callSteps 96 ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 720#64, 720⟩ : Region).Contains p →
        ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) ∧
      FinishTrace base s inner k0 events := by
  let start := enteredFrame .finish s
  have routine : finish = entry ∨ finish = key ∨ finish = finish := .inr (.inr rfl)
  have startPC : start.pc = routineAddress base finish + 0x1c#64 := by
    rw [enteredFrame_pc, pc]
  have startSP : start.reg 2#5 = s.reg 2#5 - 240#64 := enteredFrame_sp .finish s
  have prologue := frame_prologue_allowed .finish base s pc codeAligned exec spAligned stackWrite
  obtain ⟨pro, np⟩ := run_range_observes routine (enter_frame .finish s) loaded readonly prologue (entered_decoded .finish)
  obtain ⟨loadA, roA⟩ := pro.keeps_routine loaded readonly
  have innerCall := finish_inner_call_allowed base start startPC codeAligned (finish_exec_preserved pro exec)
  obtain ⟨first, na⟩ := run_range_observes routine body.innerCall loadA roA innerCall finish_first_decoded
  obtain ⟨extent, innerEntry⟩ := body.innerContract
  obtain ⟨firstOut, firstHash, hashA, nb⟩ := sha_execution_observations base _ inner extent innerEntry
  have firstResult := Option.some.inj (firstHash.symm.trans body.innerHash)
  rw [firstResult] at hashA
  have throughInner := pro.append (first.append hashA)
  obtain ⟨loadB, roB⟩ := throughInner.keeps_routine loaded readonly
  have innerSP := body.innerStack.trans startSP
  have frame24 : body.afterInner.mem.canWrite (body.afterInner.reg 2#5) 24 = true := by
    rw [innerSP, (throughInner.permissions _ _).1]
    -- The header occupies the first 24 bytes of the reserved frame.
    apply (allPerm_true_iff _ _ _ _).mpr
    intro i hi
    exact (allPerm_true_iff _ _ _ _).mp stackWrite i (by omega)
  have headerAllowed := finish_header_allowed base body.afterInner body.innerReturn codeAligned
    (finish_exec_preserved throughInner exec) (innerSP.symm ▸ spAligned) frame24
  obtain ⟨writeHeader, nc⟩ := run_range_observes routine body.writeHeader loadB roB headerAllowed finish_header_decoded
  have throughHeader := throughInner.append writeHeader
  obtain ⟨loadC, roC⟩ := throughHeader.keeps_routine loaded readonly
  have headerEq := Option.some.inj (body.writeHeader.symm.trans (finish_header body.afterInner))
  have headerPC : body.header.pc = routineAddress base finish + 0x36#64 := by
    rw [headerEq]
    change body.afterInner.pc + 16#64 = _
    rw [body.innerReturn, BitVec.add_assoc]
    rfl
  have maskAllowed := finish_mask_allowed base body.header headerPC codeAligned
    (finish_exec_preserved throughHeader exec)
  obtain ⟨preparePad, nd⟩ := run_range_observes routine body.preparePad loadC roC maskAllowed outer_mask_decoded
  have throughMask := throughHeader.append preparePad
  obtain ⟨loadD, roD⟩ := throughMask.keeps_routine loaded readonly
  have maskEq := Option.some.inj (body.preparePad.symm.trans (outer_mask body.header))
  have maskPC : body.mask.pc = routineAddress base finish + 0x54#64 := by
    rw [maskEq]
    change body.header.pc + 30#64 = _
    rw [headerPC, BitVec.add_assoc]
    rfl
  have source : body.mask.reg 9#5 = s.reg 11#5 := by
    rw [maskEq, outerMaskState, headerEq]
    change ((((body.afterInner.put 5#5 96#64).put 28#5 0x5c5c5c5c5c5c5c5c#64).put 29#5 _).advance 30).reg 9#5 = _
    simp (config := {decide := true}) only [reg_advance, reg_put, if_false]
    exact body.innerKey.trans (enteredFrame_reg .finish s 11#5 (by decide))
  have dest : body.mask.reg 29#5 = s.reg 2#5 - 240#64 + 24#64 := by
    rw [maskEq, outerMaskState]
    simp (config := {decide := true}) only [reg_advance, reg_put, if_false, if_true]
    rw [headerEq]
    change (body.afterInner.put 5#5 96#64).reg 2#5 + 24#64 = _
    simp (config := {decide := true}) only [reg_put, if_false, innerSP]
  have destAligned : (body.mask.reg 29#5).toNat % 8 = 0 := by
    rw [dest, BitVec.toNat_add]
    change (((s.reg 2#5 - 240#64).toNat + 24) % 2 ^ 64) % 8 = 0
    omega
  have destGrant : body.mask.mem.canWrite (body.mask.reg 29#5) 64 = true := by
    rw [dest, (throughMask.permissions _ _).1]
    apply (allPerm_true_iff _ _ _ _).mpr
    intro i hi
    rw [BitVec.add_assoc, ← show BitVec.ofNat 64 24 = 24#64 from rfl, ← BitVec.ofNat_add]
    exact (allPerm_true_iff _ _ _ _).mp stackWrite (24 + i) (by omega)
  have srcGrant : body.mask.mem.canRead (body.mask.reg 9#5) 64 = true := by
    rw [source]
    exact (throughMask.permissions _ _).2 keyRead
  have padAllowed := pad_range_allowed true base body.mask maskPC codeAligned
    (finish_exec_preserved throughMask exec) (source.symm ▸ keyAligned) destAligned srcGrant destGrant
  obtain ⟨writePad, ne⟩ := run_range_observes routine body.writePad loadD roD padAllowed finish_pad_decoded
  have throughPad := throughMask.append writePad
  obtain ⟨loadE, roE⟩ := throughPad.keeps_routine loaded readonly
  have outerAllowed := finish_outer_call_allowed base body.outerList body.outerListPC codeAligned
    (finish_exec_preserved throughPad exec)
  obtain ⟨lastCall, nf⟩ := run_range_observes routine body.outerCall loadE roE outerAllowed outer_call_decoded
  let outer := hmacOuter k0 (sha256 inner).2
  obtain ⟨secondOut, secondHash, hashB, ng⟩ :=
    sha_execution_observations base _ outer 120 body.outerContract
  have outerCount : outer.bytes.size = 96 := hmacOuter_length _ _
  have secondResult : secondOut = bodyOut := by
    rw [outerCount] at secondHash
    exact Option.some.inj (secondHash.symm.trans body.outerHash)
  rw [secondResult] at hashB
  have outerSteps : callSteps outer.bytes.size = callSteps 96 := congrArg callSteps outerCount
  have throughHash := throughPad.append (lastCall.append hashB)
  obtain ⟨loadF, roF⟩ := throughHash.keeps_routine loaded readonly
  have lastSP := body.sp.trans startSP
  have returnRead : bodyOut.mem.canRead (bodyOut.reg 2#5) 240 = true := by
    rw [lastSP]
    exact (throughHash.permissions _ _).2 stackRead
  have epilogue := frame_epilogue_allowed .finish base bodyOut body.outerReturn codeAligned
    (finish_exec_preserved throughHash exec) (lastSP.symm ▸ spAligned) returnRead
  obtain ⟨out, _, ret, stack, address, regs, digest⟩ := body.returned stackAvailable linkAligned
    (finish_spill_separate s (by omega) separate)
  obtain ⟨returned, nq⟩ := run_range_observes routine ret loadF roF epilogue (returned_decoded .finish)
  refine ⟨out, _, throughHash.append returned, ?_, stack, address, regs, digest, ?_, ?_⟩
  · simp only [List.length_append]
    rw [← outerSteps]
    omega
  · intro addr offStack offOutput
    let frame : Region := ⟨start.reg 2#5, 240⟩
    let full : Region := ⟨s.reg 2#5 - 720#64, 720⟩
    have frameEnd : frame.base.toNat + 240 = (s.reg 2#5).toNat := by
      change (start.reg 2#5).toNat + 240 = _
      rw [startSP]
      exact frame_base_end _ 240 (by omega)
    have fullEnd : full.base.toNat + 720 = (s.reg 2#5).toNat :=
      frame_base_end _ 720 stackAvailable
    have frameValid : frame.Valid := by
      change frame.base.toNat + 240 ≤ 2 ^ 64
      rw [frameEnd]
      exact (s.reg 2#5).isLt.le
    have offFrame : ¬ frame.Contains addr := by
      intro hit
      apply offStack
      change full.base.toNat ≤ addr.toNat ∧ addr.toNat < full.base.toNat + 720
      have lo : frame.base.toNat ≤ addr.toNat := hit.1
      have hi : addr.toNat < frame.base.toNat + 240 := hit.2
      omega
    have offNested : ¬ (callerStack (innerCallState start)).Contains addr := by
      have same : callerStack (innerCallState start) = ⟨full.base, 480⟩ := by
        unfold callerStack entryStack
        change (Region.mk ((innerCallState start).reg 2#5 - 480#64) 480) = ⟨s.reg 2#5 - 720#64, 480⟩
        rw [(inner_call_registers start).2.2.2.2.1, startSP]
        have combine : s.reg 2#5 - 240#64 - 480#64 = s.reg 2#5 - 720#64 := by
          simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
        rw [combine]
      rw [same]
      intro hit
      apply offStack
      change full.base.toNat ≤ addr.toNat ∧ addr.toNat < full.base.toNat + 720
      have hi : addr.toNat < full.base.toNat + 480 := hit.2
      exact ⟨hit.1, by omega⟩
    have keep := caller_outside_delta frame frameValid addr offFrame
    change 240 ≤ (addr - start.reg 2#5).toNat at keep
    have bodyKeep := body.frame addr (Nat.le_trans (by decide : 120 ≤ 240) keep) offNested (by
      rw [enteredFrame_reg .finish s 12#5 (by decide)]
      exact offOutput)
    have returnState : out = restoredFrame .finish bodyOut :=
      Option.some.inj (ret.symm.trans (return_frame .finish bodyOut))
    rw [returnState, restoredFrame_memory, bodyKeep]
    apply enteredFrame_outside
    let spills := regionSlice frame 128 104
    have spillsFit : 128 + 104 ≤ frame.bytes := by change 128 + 104 ≤ 240; decide
    have spillsValid : spills.Valid := regionSlice_valid _ _ _ frameValid spillsFit
    have offSpills : ¬ spills.Contains addr :=
      fun hit => offFrame (regionSlice_inside _ _ _ frameValid spillsFit _ hit)
    have outside := caller_outside_delta spills spillsValid addr offSpills
    change 104 ≤ (addr - (start.reg 2#5 + 128#64)).toNat at outside
    change 104 ≤ (addr - (s.reg 2#5 - 240#64 + 128#64)).toNat
    rwa [startSP] at outside
  · refine ⟨body.outerList, extent, innerEntry, body.outerContract, body.outerListPC,
      body.outerStack.trans startSP,
      body.outerMac.trans (enteredFrame_reg .finish s 12#5 (by decide)), ?_⟩
    have traceA := finish_inner_setup_events start
    have traceH := finish_header_events body.afterInner
    have traceM := finish_mask_events body.header
    have traceB := finish_outer_setup_events body.outerList
    simp only [finish_first_decoded, finish_header_decoded, outer_mask_decoded, outer_call_decoded,
      Option.getD_some] at traceA traceH traceM traceB
    rw [enter_events, traceA, traceH, traceM, pad_code_events _ _ _ _ (by decide), traceB,
      return_events, startPC, body.innerReturn, innerSP, headerPC, maskPC,
      source, dest, body.outerListPC, body.outerReturn, lastSP]
    simp only [List.append_assoc, outer]

/-- Execute the linked finishing helper from entry to return.
The deterministic prologue supplies the state used to express the two
SHA-256 call boundaries and their independently granted extents. -/
theorem finish_execution_from_resources (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock)
    (extent : Nat) (pc : s.pc = routineAddress base finish)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (typed : EncodedByteList (enteredFrame .finish s).mem (s.reg 10#5) inner)
    (keyAt : ∀ i : Fin 64, (enteredFrame .finish s).mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
      k0[i.val].toBitVec)
    (resources : FinishResources base (enteredFrame .finish s) extent)
    (sha : ShaCode (shaAddress base) (enteredFrame .finish s).mem)
    (loaded : finish.Loaded (routineAddress base finish) s.mem.read8)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true)
    (stackAvailable : 720 ≤ (s.reg 2#5).toNat)
    (stackRead : s.mem.canRead (s.reg 2#5 - 240#64) 240 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 240#64) 240 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyRead : s.mem.canRead (s.reg 11#5) 64 = true)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0)
    (separate : (⟨s.reg 2#5 - 240#64, 240⟩ : Region).Disjoint ⟨s.reg 12#5, 32⟩) :
    ∃ out events,
      ProgramExecution base s events out ∧ events.length ≤ 75 + callSteps inner.bytes.size + callSteps 96 ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 720#64, 720⟩ : Region).Contains p →
        ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) ∧
      FinishTrace base s inner k0 events := by
  let entered := enteredFrame .finish s
  have enteredPC : entered.pc = routineAddress base finish + 0x1c#64 := by
    rw [enteredFrame_pc, pc]
  have typedAt : EncodedByteList entered.mem (entered.reg 10#5) inner := by
    rw [enteredFrame_reg .finish s 10#5 (by decide)]
    exact typed
  have keyBytes (i : Fin 64) : entered.mem.read8 (entered.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec := by
    rw [enteredFrame_reg .finish s 11#5 (by decide)]
    exact keyAt i
  have nestedEven (off : Nat) (even : off % 2 = 0) :
      (routineAddress base finish + BitVec.ofNat 64 off).toNat % 2 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨_, ⟨body⟩⟩ := finish_body_from_resources base entered inner k0 extent enteredPC layout accessible
    sizeBound lengthBound typedAt resources sha (nestedEven 0x26 (by decide)) (nestedEven 0xbc (by decide)) keyBytes
  have readonly : RoutineReadOnly finish base s.mem := routine_readonly_of_exec exec
  have spAligned : (s.reg 2#5 - 240#64).toNat % 8 = 0 := by
    have aligned := resources.aligned
    rw [show entered.reg 2#5 = s.reg 2#5 - 240#64 from enteredFrame_sp .finish s] at aligned
    omega
  exact body.execution_from_grants pc loaded readonly codeAligned exec spAligned stackAvailable
    stackRead stackWrite keyAligned keyRead linkAligned separate


private theorem FinishResources.transfer {base : Addr} {s after : CPU} {extent : Nat}
    (grants : FinishResources base s extent)
    (sp : after.reg 2#5 = s.reg 2#5) (input : after.reg 10#5 = s.reg 10#5)
    (key : after.reg 11#5 = s.reg 11#5) (output : after.reg 12#5 = s.reg 12#5)
    (perms : ∀ p, after.mem.perm p = s.mem.perm p)
    (reads : ∀ p n, s.mem.canRead p n = true → after.mem.canRead p n = true) :
    FinishResources base after extent := by
  have w : finishWorkspace after = finishWorkspace s := by simp only [finishWorkspace, sp]
  have i : finishInput after extent = finishInput s extent := by simp only [finishInput, input]
  have k : finishKey after = finishKey s := by simp only [finishKey, key]
  have o : finishOutput after = finishOutput s := by simp only [finishOutput, output]
  have writable (p : Addr) : after.mem.canWrite p 1 = s.mem.canWrite p 1 :=
    allPerm_eq_of_perm perms _ _ _
  exact {
    available := sp.symm ▸ grants.available
    aligned := sp.symm ▸ grants.aligned
    inputAligned := input.symm ▸ grants.inputAligned
    outputAligned := output.symm ▸ grants.outputAligned
    stackValid := w.symm ▸ grants.stackValid
    inputValid := i.symm ▸ grants.inputValid
    keyValid := k.symm ▸ grants.keyValid
    outputValid := o.symm ▸ grants.outputValid
    stackInput := w.symm ▸ i.symm ▸ grants.stackInput
    stackKey := w.symm ▸ k.symm ▸ grants.stackKey
    stackOutput := w.symm ▸ o.symm ▸ grants.stackOutput
    stackCode := w.symm ▸ grants.stackCode
    outputCode := o.symm ▸ grants.outputCode
    outputInput := o.symm ▸ i.symm ▸ grants.outputInput
    inputRead := fun p hp => reads _ _ (grants.inputRead p (i ▸ hp))
    stackRead := fun p hp => reads _ _ (grants.stackRead p (w ▸ hp))
    stackWrite := fun p hp => (writable p).trans (grants.stackWrite p (w ▸ hp))
    outputWrite := fun p hp => (writable p).trans (grants.outputWrite p (o ▸ hp))
  }

set_option maxHeartbeats 3100000 in
/-- The RV64 finishing helper from caller-provided bytes and grants, through
the decoded frame, both linked SHA-256 calls and the restored return. -/
theorem finish_execution_from_caller (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock)
    (extent : Nat) (pc : s.pc = routineAddress base finish)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (typed : EncodedByteList s.mem (s.reg 10#5) inner)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (grants : FinishResources base (s.put 2#5 (s.reg 2#5 - 240#64)) extent)
    (sha : ShaCode (shaAddress base) s.mem)
    (loaded : finish.Loaded (routineAddress base finish) s.mem.read8)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true)
    (stackAvailable : 720 ≤ (s.reg 2#5).toNat)
    (stackRead : s.mem.canRead (s.reg 2#5 - 240#64) 240 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 240#64) 240 = true)
    (keyAligned : (s.reg 11#5).toNat % 8 = 0)
    (keyRead : s.mem.canRead (s.reg 11#5) 64 = true)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0) :
    ∃ out events,
      ProgramExecution base s events out ∧ events.length ≤ 75 + callSteps inner.bytes.size + callSteps 96 ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 720#64, 720⟩ : Region).Contains p →
        ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) ∧
      FinishTrace base s inner k0 events := by
  let beforeBody := s.put 2#5 (s.reg 2#5 - 240#64)
  let saved := enteredFrame .finish s
  let work := finishWorkspace beforeBody
  let stack : Region := ⟨s.reg 2#5 - 240#64, 240⟩
  have adjusted : beforeBody.reg 2#5 = s.reg 2#5 - 240#64 := by
    simp (config := {decide := true}) only [beforeBody, reg_put, if_false, if_true]
  have keepRegister (r : Reg) (other : r ≠ 2#5) : beforeBody.reg r = s.reg r := by
    by_cases z : r = 0
    · subst r
      exact (reg_zero _).trans (reg_zero _).symm
    · simp only [beforeBody, reg_put, if_neg z, if_neg other]
  have nonStack (r : Reg) (other : r ≠ 2#5) : saved.reg r = beforeBody.reg r :=
    (enteredFrame_reg .finish s r other).trans (keepRegister r other).symm
  have memSame : beforeBody.mem = s.mem := rfl
  have savedSP : saved.reg 2#5 = beforeBody.reg 2#5 :=
    (enteredFrame_sp .finish s).trans adjusted.symm
  have perms (p : Addr) : saved.mem.perm p = beforeBody.mem.perm p := by
    rw [enteredFrame_memory, memSame]
    exact Crypto.HMACSHA256.ARM64.writeWords_perm _ _ _ _ _
  have readable (p : Addr) (n : Nat) (h : beforeBody.mem.canRead p n = true) :
      saved.mem.canRead p n = true := by
    rw [enteredFrame_memory]
    exact Crypto.HMACSHA256.ARM64.writeWords_canRead _ _ _ _ _ _ (by rwa [memSame] at h)
  have resources := grants.transfer savedSP (nonStack _ (by decide)) (nonStack _ (by decide))
    (nonStack _ (by decide)) perms readable
  have stackSlice : stack = regionSlice work (480 + 0) 240 := by
    have eq := finish_slice_base beforeBody 0 240
    change (regionSlice work (480 + 0) 240).base = beforeBody.reg 2#5 + 0#64 at eq
    rw [BitVec.add_zero, adjusted] at eq
    exact (congrArg (fun addr => (⟨addr, 240⟩ : Region)) eq).symm
  have inWork (p : Addr) (inside : stack.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ grants.stackValid (by change 480 + 0 + 240 ≤ 720; decide) p (stackSlice ▸ inside)
  have validStack : stack.Valid := stackSlice ▸ regionSlice_valid _ _ _ grants.stackValid
    (by change 480 + 0 + 240 ≤ 720; decide)
  let slots := regionSlice stack 128 104
  have slotFit : 128 + 104 ≤ stack.bytes := by change _ ≤ 240; decide
  have validSlots : slots.Valid := regionSlice_valid _ _ _ validStack slotFit
  have spillBytes (p : Addr) (outside : ¬ work.Contains p) : saved.mem.cells p = s.mem.cells p := by
    have offSlots : ¬slots.Contains p := fun hp =>
      outside (inWork p (regionSlice_inside stack 128 104 validStack slotFit p hp))
    apply enteredFrame_outside .finish s
    exact caller_outside_delta slots validSlots p offSlots
  have initialImage := sha.preserved
    (fun p hp => spillBytes p (fun hit => grants.stackCode p ⟨hit,hp⟩))
    (fun p => by simpa only [memSame] using perms p)
    (fun p n h => readable p n (by simpa only [memSame] using h))
  have inputRegion : finishInput beforeBody extent = ⟨s.reg 10#5, extent⟩ := by
    simp only [finishInput, keepRegister 10#5 (by decide)]
  have keyRegion : finishKey beforeBody = ⟨s.reg 11#5, 64⟩ := by
    simp only [finishKey, keepRegister 11#5 (by decide)]
  have macRegion : finishOutput beforeBody = ⟨s.reg 12#5, 32⟩ := by
    simp only [finishOutput, keepRegister 12#5 (by decide)]
  have source (p : Addr) (h : (⟨s.reg 10#5, extent⟩ : Region).Contains p) :
      saved.mem.cells p = s.mem.cells p := by
    exact spillBytes p (fun hit => grants.stackInput p ⟨hit, inputRegion.symm ▸ h⟩)
  have sourceValid : (⟨s.reg 10#5, extent⟩ : Region).Valid := inputRegion ▸ grants.inputValid
  have word (off : Nat) (room : off + 8 ≤ extent) :
      saved.mem.read64 (s.reg 10#5 + BitVec.ofNat 64 off) =
        s.mem.read64 (s.reg 10#5 + BitVec.ofNat 64 off) := by
    apply Crypto.HMACSHA256.ARM64.read64_eq_of_cells
    intro i
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact source _ (caller_region_contains_offset ⟨s.reg 10#5, extent⟩ sourceValid (off + i.val)
      (by have := i.isLt; change _ < extent; omega))
  have header : 24 ≤ extent := by obtain ⟨a, _, b, _⟩ := layout; omega
  have first := word 0 (by omega)
  change saved.mem.read64 (s.reg 10#5 + 0#64) = s.mem.read64 (s.reg 10#5 + 0#64) at first
  rw [BitVec.add_zero] at first
  have savedTyped : EncodedByteList saved.mem (s.reg 10#5) inner := by
    refine ⟨first.trans typed.size, (word 8 (by omega)).trans typed.offset,
      (word 16 (by omega)).trans typed.count, ?_⟩
    intro i
    have inSource : (⟨s.reg 10#5, extent⟩ : Region).Contains
        (s.reg 10#5 + BitVec.ofNat 64 (inner.offset + i.val)) :=
      caller_region_contains_offset ⟨s.reg 10#5, extent⟩ sourceValid _
        (by have := i.isLt; obtain ⟨_, _, _, h⟩ := layout; change _ < extent; omega)
    unfold Arm64.Memory.read8
    rw [source _ inSource]
    exact typed.bytes i
  have savedKey (i : Fin 64) : saved.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec := by
    let p := s.reg 11#5 + BitVec.ofNat 64 i.val
    have keyValid : (⟨s.reg 11#5, 64⟩ : Region).Valid := keyRegion ▸ grants.keyValid
    have within : (finishKey beforeBody).Contains p := by
      rw [keyRegion]
      exact caller_region_contains_offset ⟨s.reg 11#5, 64⟩ keyValid i.val i.isLt
    unfold Arm64.Memory.read8
    rw [spillBytes _ (fun hp => grants.stackKey _ ⟨hp,within⟩)]
    exact keyAt i
  have separated : stack.Disjoint ⟨s.reg 12#5, 32⟩ := by
    intro p hit
    exact grants.stackOutput p ⟨inWork p hit.1, macRegion.symm ▸ hit.2⟩
  exact finish_execution_from_resources base s inner k0 extent pc layout accessible sizeBound lengthBound savedTyped
    savedKey resources initialImage loaded codeAligned exec stackAvailable stackRead stackWrite keyAligned keyRead
    linkAligned separated

end Crypto.HMACSHA256.RISCV64
