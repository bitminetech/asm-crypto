import Proofs.HMACSHA256.ARM64Ranges
import Proofs.HMACSHA256.ARM64Outer
import Proofs.HMACSHA256.ARM64ShaEntry
import Proofs.HMACSHA256.ARM64FrameTrace

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.ARM64.Imported

structure FinishBody (base : Addr) (s out : Arm64.State) (inner : ByteList) (key : HmacKeyBlock) where
  afterInner : Arm64.State
  header : Arm64.State
  mask : Arm64.State
  outerList : Arm64.State
  innerObservations : List InstructionObservation
  outerObservations : List InstructionObservation
  innerCall : runRange finish 0x1c 4 s = some (innerCallState s)
  innerHash : ShaCallResult (shaAddress base) (innerCallState s) afterInner inner innerObservations
  innerReturn : afterInner.pc = routineAddress base finish + 0x2c#64
  innerSP : afterInner.sp = s.sp
  innerKey : afterInner.readReg64 .x19 = s.readReg64 .x1
  outerSP : outerList.sp = s.sp
  outerMac : outerList.readReg64 .x20 = s.readReg64 .x2
  writeHeader : runRange finish 0x2c 6 afterInner = some header
  preparePad : runRange finish 0x44 4 header = some mask
  writePad : runRange finish 0x54 16 mask = some outerList
  outerCall : runRange finish 0x94 3 outerList = some (outerCallState outerList)
  outerHash : ShaCallResult (shaAddress base) (outerCallState outerList) out
    (hmacOuter key (sha256 inner).2) outerObservations
  outerReturn : out.pc = routineAddress base finish + 0xa0#64
  sp : out.sp = s.sp
  digest : memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish inner key).map UInt8.toBitVec
  frame : ∀ p, 416 ≤ (p - entryStack s).toNat →
    24 ≤ (p - (s.sp + 96#64)).toNat → 64 ≤ (p - (s.sp + 120#64)).toNat →
    32 ≤ (p - (s.sp + 184#64)).toNat → 32 ≤ (p - s.readReg64 .x2).toNat →
    out.mem.cells p = s.mem.cells p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2300000 in
/-- Both ARM64 hashes execute directly in the actual caller memory. The
verified SHA-256 frames let the helper resume with K0, the MAC pointer, and
the previously computed inner digest in their original locations. -/
theorem finish_body (base : Addr) (s : Arm64.State) (inner : ByteList) (key : HmacKeyBlock) (extent : Nat)
    (pc : s.pc = routineAddress base finish + 0x1c#64)
    (innerReady : CallerEntry (shaAddress base) (innerCallState s) inner extent)
    (align : s.spAligned = true)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = key[i.val].toBitVec)
    (keyOffInnerStack : ∀ i : Fin 64, 416 ≤
      (s.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack (innerCallState s)).toNat)
    (keyOffInnerOutput : ∀ i : Fin 64, 32 ≤
      (s.readReg64 .x1 + BitVec.ofNat 64 i.val - (s.sp + 184#64)).toNat)
    (keyOffHeader : ∀ i : Fin 64, 24 ≤
      (s.readReg64 .x1 + BitVec.ofNat 64 i.val - (s.sp + 96#64)).toNat)
    (keyOffPad : ∀ i : Fin 64, 64 ≤
      (s.readReg64 .x1 + BitVec.ofNat 64 i.val - (s.sp + 120#64)).toNat)
    (writeRead : ∀ mid observations, ShaCallResult (shaAddress base) (innerCallState s) mid inner observations →
      (∀ i : Fin 3, mid.mem.canWrite (mid.sp + 96#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true) ∧
      (∀ i : Fin 8, mid.mem.canWrite (mid.sp + 120#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true) ∧
      (∀ i : Fin 8, mid.mem.canRead (mid.readReg64 .x19 + BitVec.ofNat 64 (8 * i.val)) 8 = true))
    (outerResources : ∀ mid observations header mask outer,
      ShaCallResult (shaAddress base) (innerCallState s) mid inner observations →
      runRange finish 0x2c 6 mid = some header →
      runRange finish 0x44 4 header = some mask →
      runRange finish 0x54 16 mask = some outer →
      outer.sp = s.sp → outer.readReg64 .x20 = s.readReg64 .x2 →
      ShaResources (shaAddress base) (outerCallState outer) 120) :
    ∃ out, Nonempty (FinishBody base s out inner key) := by
  obtain ⟨_, arg, keyReg, macReg, _, sp, mem⟩ := inner_call_registers s
  obtain ⟨mid, observations, hashed⟩ := sha_actual_call innerReady
  have midPC := hashed.returnAddress.trans (inner_link base s pc)
  have midSP := hashed.abi.stack.trans sp
  have nvKey : mid.readReg64 .x19 = (innerCallState s).readReg64 .x19 :=
    congrFun hashed.abi.nonvolatile ⟨1, by decide⟩
  have nvMac : mid.readReg64 .x20 = (innerCallState s).readReg64 .x20 :=
    congrFun hashed.abi.nonvolatile ⟨2, by decide⟩
  have midKey := nvKey.trans keyReg
  have midMac := nvMac.trans macReg
  have midAligned : mid.spAligned = true := by
    unfold Arm64.State.spAligned
    rw [midSP]
    exact align
  have keyBytes (i : Fin 64) :
      mid.mem.read8 (mid.readReg64 .x19 + BitVec.ofNat 64 i.val) = key[i.val].toBitVec := by
    rw [midKey]
    have kept := hashed.frame _ (keyOffInnerStack i) (by rw [arg]; exact keyOffInnerOutput i)
    rw [mem] at kept
    exact (read8_of_cell _ kept).trans (keyAt i)
  have innerBytes (i : Fin 32) :
      mid.mem.read8 (mid.sp + 184#64 + BitVec.ofNat 64 i.val) = (sha256 inner).2[i.val].toBitVec := by
    rw [midSP, ← arg]
    have byte := congrArg (fun v : Vector (BitVec 8) 32 => v[i.val]) hashed.digest
    simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map] using byte
  obtain ⟨headerWrite, padWrite, keyRead⟩ := writeRead mid observations hashed
  obtain ⟨header, mask, list, headerRun, maskRun, listRun, listSP, listStatus, listPC, listMac, encoding, localFrame⟩ :=
    finish_outer_list mid key (sha256 inner).2 midAligned headerWrite padWrite keyRead
      (by rw [midSP, midKey]; exact keyOffHeader) (by rw [midSP, midKey]; exact keyOffPad) keyBytes innerBytes
  have reached : list.pc = routineAddress base finish + 0x94#64 := by
    rw [listPC, midPC, BitVec.add_assoc]
    rfl
  obtain ⟨input, output, _, stack, listMem⟩ := outer_call_registers list
  let outer := hmacOuter key (sha256 inner).2
  have entry : CallerEntry (shaAddress base) (outerCallState list) outer 120 :=
    establish_sha_entry (hmacOuter_layout key (sha256 inner).2)
      (by change 120 ≤ 120; decide) (by change 120 < 2 ^ 64; decide)
      (by rw [hmacOuter_length]; decide)
      (by rw [input, listMem, listSP]; exact encoding)
      (outerResources mid observations header mask list hashed headerRun maskRun listRun
        (listSP.trans midSP) (listMac.trans midMac))
      (outer_target base list reached) (listStatus.trans hashed.running)
  obtain ⟨out, outerObservations, final⟩ := sha_actual_call entry
  refine ⟨out, ⟨⟨mid, header, mask, list, observations, outerObservations, inner_call s, hashed, midPC, midSP, midKey, listSP.trans midSP, listMac.trans midMac,
    headerRun, maskRun, listRun, outer_call list, final, final.returnAddress.trans (outer_link base list reached),
    (final.abi.stack.trans stack).trans (listSP.trans midSP), ?_, ?_⟩⟩⟩
  · rw [hmacFinish_calls inner key innerReady.length, ← midMac, ← listMac, ← output]
    exact final.digest
  · intro p offStack offHead offPad offInner offMAC
    have stackSame : entryStack (outerCallState list) = entryStack s := by
      unfold entryStack
      rw [stack, listSP, midSP]
    have firstStack : entryStack (innerCallState s) = entryStack s := by
      unfold entryStack
      rw [sp]
    have resultAddress := output.trans (listMac.trans midMac)
    calc
      out.mem.cells p = (outerCallState list).mem.cells p :=
        final.frame p (by rw [stackSame]; exact offStack) (by rw [resultAddress]; exact offMAC)
      _ = list.mem.cells p := congrArg (fun m : Arm64.Memory => m.cells p) listMem
      _ = mid.mem.cells p :=
        localFrame p (by rw [midSP]; exact offHead) (by rw [midSP]; exact offPad)
      _ = (innerCallState s).mem.cells p :=
        hashed.frame p (by rw [firstStack]; exact offStack) (by rw [arg]; exact offInner)
      _ = s.mem.cells p := congrArg (fun m : Arm64.Memory => m.cells p) mem

set_option maxHeartbeats 1800000 in
/-- Connect the computed MAC to the decoded prologue and epilogue. This
composition derives save-area preservation from the two callee frames and the disjoint MAC buffer. -/
theorem FinishBody.returned {base : Addr} {s bodyOut : Arm64.State}
    {inner : ByteList} {k0 : HmacKeyBlock}
    (run : FinishBody base (enteredState s 224#64) bodyOut inner k0)
    (aligned : s.spAligned = true)
    (localAligned : (s.sp - 224#64) &&& 15#64 = 0#64)
    (stackWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - 224#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (stackRead : ∀ i : Fin 12, bodyOut.mem.canRead (bodyOut.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (macOffSaves : ∀ i : Fin 96, 32 ≤
      (s.sp - 224#64 + BitVec.ofNat 64 i.val - s.readReg64 .x2).toNat) :
    ∃ out, runRange finish 0 7 s = some (enteredState s 224#64) ∧
      runRange finish 0xa0 7 bodyOut = some out ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      out.status = .Running ∧ out.mem = bodyOut.mem := by
  have sp : bodyOut.sp = s.sp - 224#64 := run.sp
  have mac : (enteredState s 224#64).readReg64 .x2 = s.readReg64 .x2 := by
    simp (config := { decide := true }) [enteredState, Arm64.Reg.x2, Arm64.Reg.x29,
      Arm64.State.readReg64, Arm64.State.writeReg64, Arm64.State.setMem, Arm64.State.setPC,
      Arm64.RegFile.read, Arm64.RegFile.write]
  have savedCells (i : Fin 96) :
      bodyOut.mem.cells (bodyOut.sp + BitVec.ofNat 64 i.val) =
        (frameMem s 224#64).cells (bodyOut.sp + BitVec.ofNat 64 i.val) := by
    let start := enteredState s 224#64
    rw [run.sp]
    apply run.frame
    · have address : start.sp + BitVec.ofNat 64 i.val - entryStack start =
          BitVec.ofNat 64 (416 + i.val) := by
        let base := entryStack start
        have frame : base + 416#64 = start.sp := BitVec.sub_add_cancel _ _
        calc
          _ = base + 416#64 + BitVec.ofNat 64 i.val - base := by rw [frame]
          _ = _ := by rw [BitVec.add_assoc, address_delta, BitVec.ofNat_add]
      rw [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    · exact outside_span_of_offset _ _ 96 24 (.inl i.isLt) (by decide) (by have := i.isLt; omega)
    · exact outside_span_of_offset _ _ 120 64 (.inl (by have := i.isLt; omega)) (by decide)
        (by have := i.isLt; omega)
    · exact outside_span_of_offset _ _ 184 32 (.inl (by have := i.isLt; omega)) (by decide)
        (by have := i.isLt; omega)
    · rw [mac]
      exact macOffSaves i
  have bodyAligned : bodyOut.spAligned = true := by
    simp [Arm64.State.spAligned, sp, localAligned]
  have word (i : Fin 12) : bodyOut.mem.read64 (bodyOut.sp + BitVec.ofNat 64 (8 * i.val)) =
      s.readReg64 (savedRegister i.val) := by
    calc
      _ = (frameMem s 224#64).read64 (bodyOut.sp + BitVec.ofNat 64 (8 * i.val)) := by
        apply read64_eq_of_cells
        intro j
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact savedCells ⟨8 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
      _ = _ := by
        rw [sp, frameMem]
        exact writeWords_word _ _ _ 12 i.val i.isLt (by decide)
  refine ⟨restoreState bodyOut 224#64, enter_finish s aligned localAligned stackWrite,
    (returns bodyOut bodyAligned stackRead).2.2, ?_, word ⟨1, by decide⟩, ?_, ?_, run.outerHash.running, rfl⟩
  · change bodyOut.sp + 224#64 = _
    rw [sp, BitVec.sub_add_cancel]
  · intro i
    rw [restored_register]
    exact word i
  · change memoryBytes32 bodyOut.mem (s.readReg64 .x2) = _
    rw [← mac]
    exact run.digest

def FinishBody.nativeTrace {base : Addr} {s bodyOut : Arm64.State} {inner : ByteList}
    {k0 : HmacKeyBlock} (body : FinishBody base (enteredState s 224#64) bodyOut inner k0) :
    List InstructionObservation :=
  frameEnterEvents s.pc s.sp 224#64 ++
  rangeEvents finish 0x1c 4 (enteredState s 224#64) ++ body.innerObservations ++
  rangeEvents finish 0x2c 6 body.afterInner ++ rangeEvents finish 0x44 4 body.header ++
  rangeEvents finish 0x54 16 body.mask ++ rangeEvents finish 0x94 3 body.outerList ++
  body.outerObservations ++ frameReturnEvents bodyOut.pc bodyOut.sp 224#64 (s.readReg64 .lr)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3900000 in
/-- Fetch the finishing helper and its actual linked SHA-256 callees through
the epilogue, preserving the independently mapped code throughout. -/
theorem FinishBody.execution_fetched {base : Addr} {s bodyOut : Arm64.State}
    {inner : ByteList} {k0 : HmacKeyBlock}
    (body : FinishBody base (enteredState s 224#64) bodyOut inner k0)
    (pc : s.pc = routineAddress base finish)
    (loaded : (programAt finish (routineAddress base finish)).CodeLoaded s.mem)
    (aligned : s.spAligned = true)
    (localAligned : (s.sp - 224#64) &&& 15#64 = 0#64)
    (stackWrite : ∀ i : Fin 12, s.mem.canWrite (s.sp - 224#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (stackRead : ∀ i : Fin 12, bodyOut.mem.canRead (bodyOut.sp + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (macOffSaves : ∀ i : Fin 96, 32 ≤
      (s.sp - 224#64 + BitVec.ofNat 64 i.val - s.readReg64 .x2).toNat) :
    ∃ out, LinkedExecution base s body.nativeTrace out ∧
      body.nativeTrace.length = 47 + body.innerObservations.length + body.outerObservations.length ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      out.mem = bodyOut.mem := by
  let prog := programAt finish (routineAddress base finish)
  let start := enteredState s 224#64
  have isFinish : finish = entry ∨ finish = key ∨ finish = finish := .inr (.inr rfl)
  obtain ⟨out, enter, leave, sp, link, regs, digest, live, memory⟩ :=
    body.returned aligned localAligned stackWrite stackRead macOffSaves
  have callerLive := run_range_running_before (by decide +kernel) body.innerCall body.innerHash.started
  obtain ⟨pro, na⟩ := run_range_observes isFinish (by simpa only [BitVec.add_zero] using pc)
    (by decide) loaded (by decide +kernel) enter callerLive
  have startPC : start.pc = routineAddress base finish + 0x1c#64 := by
    change s.pc + 28#64 = _
    rw [pc]
  obtain ⟨firstCall, nb⟩ := run_range_observes isFinish startPC (by decide)
    (pro.keeps_code prog loaded) (by decide +kernel) body.innerCall body.innerHash.started
  have proTrace : rangeEvents finish 0 7 s = frameEnterEvents s.pc s.sp 224#64 := by
    simpa only [rangeEvents, finish_enter_decoded, Option.getD_some] using
      save_code_events s 224#64 aligned localAligned stackWrite
  have firstHash := LinkedExecution.shaCall body.innerHash (.nil body.afterInner)
  have front := pro.append (firstCall.append firstHash)
  have outerReady := run_range_running_before (by decide +kernel) body.outerCall body.outerHash.started
  have padReady := run_range_running_before (by decide +kernel) body.writePad outerReady
  have maskReady := run_range_running_before (by decide +kernel) body.preparePad padReady
  obtain ⟨writeHeader, nc⟩ := run_range_observes isFinish body.innerReturn (by decide)
    (front.keeps_code prog loaded) (by decide +kernel) body.writeHeader maskReady
  have throughHeader := front.append writeHeader
  have headerPC : body.header.pc = routineAddress base finish + 0x44#64 := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) body.writeHeader maskReady,
      body.innerReturn, BitVec.add_assoc]
    rfl
  obtain ⟨prepareMask, nd⟩ := run_range_observes isFinish headerPC (by decide)
    (throughHeader.keeps_code prog loaded) (by decide +kernel) body.preparePad padReady
  have throughMask := throughHeader.append prepareMask
  have maskPC : body.mask.pc = routineAddress base finish + 0x54#64 := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) body.preparePad padReady,
      headerPC, BitVec.add_assoc]
    rfl
  obtain ⟨writePad, ne⟩ := run_range_observes isFinish maskPC (by decide)
    (throughMask.keeps_code prog loaded) (by decide +kernel) body.writePad outerReady
  have throughPad := throughMask.append writePad
  have outerPC : body.outerList.pc = routineAddress base finish + 0x94#64 := by
    rw [run_range_end (by decide +kernel) (by decide +kernel) body.writePad outerReady,
      maskPC, BitVec.add_assoc]
    rfl
  obtain ⟨lastCall, nf⟩ := run_range_observes isFinish outerPC (by decide)
    (throughPad.keeps_code prog loaded) (by decide +kernel) body.outerCall body.outerHash.started
  have secondHash := LinkedExecution.shaCall body.outerHash (.nil bodyOut)
  have throughHashes := throughPad.append (lastCall.append secondHash)
  obtain ⟨ret, ng⟩ := run_range_observes isFinish body.outerReturn (by decide)
    (throughHashes.keeps_code prog loaded) (by decide +kernel) leave live
  have bodyAligned : bodyOut.spAligned = true := by
    simp [Arm64.State.spAligned, body.sp, enteredState, localAligned]
  have nativeLink : bodyOut.mem.read64 (bodyOut.sp + 8#64) = s.readReg64 .lr := by
    have exactReturn := (returns bodyOut bodyAligned stackRead).2.2
    have restored := Option.some.inj (exactReturn.symm.trans leave)
    exact (congrArg Arm64.State.pc restored).trans link
  have returnTrace : rangeEvents finish 0xa0 7 bodyOut =
      frameReturnEvents bodyOut.pc bodyOut.sp 224#64 (s.readReg64 .lr) := by
    rw [← nativeLink]
    simpa only [rangeEvents, finish_return_decoded, Option.getD_some] using
      restore_code_events bodyOut 224#64 bodyAligned stackRead
  refine ⟨out, ?_, ?_, sp, link, live, regs, digest, memory⟩
  · simpa only [FinishBody.nativeTrace, proTrace, returnTrace, List.append_nil, List.append_assoc] using
      throughHashes.append ret
  · have setupCount : (rangeEvents finish 0x1c 4 (enteredState s 224#64)).length = 4 := nb
    simp only [FinishBody.nativeTrace, ← proTrace, ← returnTrace, List.length_append, na, setupCount, nc, nd, ne, nf, ng]
    omega

end Crypto.HMACSHA256.ARM64
