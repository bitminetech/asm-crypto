import Proofs.HMACSHA256.Callee
import Proofs.HMACSHA256.X86CallSites
import Proofs.HMACSHA256.X86Outer
import Proofs.HMACSHA256.X86ShaEntry
import Proofs.HMACSHA256.X86Frame
import Proofs.HMACSHA256.X86Return

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (memoryBytes32)

structure FinishBody (base : Val) (s out : Cpu) (inner : ByteList) (key : HmacKeyBlock)
    (extent : Nat) (authority : Authority) where
  afterInner : Cpu
  header : Cpu
  mask : Cpu
  outerList : Cpu
  innerEvents : List Event
  outerEvents : List Event
  innerCall : runRange finish 0x11 4 s = some (innerCallState s)
  innerHash : NativeSerial (shaAddress base) (innerCallState s) afterInner inner extent authority innerEvents
  innerReturn : afterInner.rip = routineAddress base finish + 0x21#64
  writeHeader : runRange finish 0x21 3 afterInner = some header
  preparePad : runRange finish 0x3b 1 header = some mask
  writePad : runRange finish 0x45 24 mask = some outerList
  outerCall : runRange finish 0xa4 3 outerList = some (outerCallState outerList)
  outerHash : NativeSerial (shaAddress base) (outerCallState outerList) out
    (hmacOuter key (sha256 inner).2) 120 authority outerEvents
  outerListFrame : ∀ p, 88 ≤ (p - afterInner.regs.get .rsp).toNat → outerList.mem.read p = afterInner.mem.read p
  outerListSP : outerList.regs.get .rsp = s.regs.get .rsp
  outerListMac : outerList.regs.get .rbp = s.regs.get .rdx
  afterInnerSP : afterInner.regs.get .rsp = s.regs.get .rsp
  outerReturn : out.rip = routineAddress base finish + 0xaf#64
  sp : out.regs.get .rsp = s.regs.get .rsp
  digest : memoryBytes32 (byteView out.mem) (s.regs.get .rdx) = (hmacFinish inner key).map UInt8.toBitVec

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Both x86-64 hashes are the verified SHA-256 executable. The outer
argument and its bytes come from the decoded HMAC stores and CALL, and
the result uses the original MAC pointer. -/
theorem finish_body (base : Val) (s : Cpu) (inner : ByteList) (key : HmacKeyBlock)
    (extent : Nat) (authority : Authority) (live : s.ms = none)
    (pc : s.rip = routineAddress base finish + 0x11#64)
    (shaCanonical : canonical (shaAddress base) = true)
    (returnCanonical : canonical (routineAddress base finish + 0xaf#64) = true)
    (innerReady : PermissionEntry (shaAddress base) (innerCallState s) inner extent authority)
    (keyAt : ∀ i : Fin 64,
      (innerCallState s).mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = key[i.val].toBitVec)
    (keyOffInnerStack : ∀ i : Fin 64,
      ¬ (stackRegion (innerCallState s)).Contains (s.regs.get .rsi + BitVec.ofNat 64 i.val))
    (keyOffInnerOutput : ∀ i : Fin 64,
      ¬ (outputRegion (innerCallState s)).Contains (s.regs.get .rsi + BitVec.ofNat 64 i.val))
    (keyOffHeader : ∀ i : Fin 64, 24 ≤
      (s.regs.get .rsi + BitVec.ofNat 64 i.val - s.regs.get .rsp).toNat)
    (keyOffPad : ∀ i : Fin 64, 64 ≤
      (s.regs.get .rsi + BitVec.ofNat 64 i.val - (s.regs.get .rsp + 24#64)).toNat)
    (outerResources : ∀ mid events header mask outer,
      NativeSerial (shaAddress base) (innerCallState s) mid inner extent authority events →
      runRange finish 0x21 3 mid = some header →
      runRange finish 0x3b 1 header = some mask →
      runRange finish 0x45 24 mask = some outer →
      outer.regs.get .rsp = s.regs.get .rsp →
      outer.regs.get .rbp = s.regs.get .rdx →
      (∀ p, 88 ≤ (p - s.regs.get .rsp).toNat → outer.mem.read p = mid.mem.read p) →
      ShaResources (shaAddress base) (outerCallState outer) (hmacOuter key (sha256 inner).2) 120 authority) :
    ∃ out, Nonempty (FinishBody base s out inner key extent authority) := by
  obtain ⟨_, a1, rbx, rbp, sp, _⟩ := inner_call_registers s
  have inTarget := inner_target base s pc
  have inLink := inner_link base s pc
  have localCall := inner_call s live (by change canonical (innerCallState s).rip = true; rw [inTarget]; exact shaCanonical)
  obtain ⟨mid, es, checked, _⟩ := sha256_callee innerReady
  have midPC := checked.result.pc.trans inLink
  have midSP : mid.regs.get .rsp = s.regs.get .rsp := by
    rw [checked.result.stack, sp]
    exact BitVec.sub_add_cancel _ _
  have midKey : mid.regs.get .rbx = s.regs.get .rsi :=
    (checked.result.saved ⟨0, by decide⟩).trans rbx
  have midMac : mid.regs.get .rbp = s.regs.get .rdx :=
    (checked.result.saved ⟨1, by decide⟩).trans rbp
  have keyBytes (i : Fin 64) :
      mid.mem.read (mid.regs.get .rbx + BitVec.ofNat 64 i.val) = key[i.val].toBitVec := by
    rw [midKey, checked.result.frame _ (keyOffInnerOutput i) (keyOffInnerStack i)]
    exact keyAt i
  have digestBytes (i : Fin 32) :
      mid.mem.read (mid.regs.get .rsp + 88#64 + BitVec.ofNat 64 i.val) = (sha256 inner).2[i.val].toBitVec := by
    have d := congrArg (fun v : Vector (BitVec 8) 32 => v[i.val]) checked.result.digest
    rw [midSP, ← a1]
    simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map, byteView_read] using d
  obtain ⟨header, mask, list, headerRun, maskRun, listRun, listLive, listSP, listMac, listPC, encoding, preserved⟩ :=
    finish_outer_list mid key (sha256 inner).2 checked.result.live
      (by rw [midKey, midSP]; exact keyOffHeader)
      (by rw [midKey, midSP]; exact keyOffPad)
      keyBytes digestBytes
  have atOuter : list.rip = routineAddress base finish + 0xa4#64 := by
    rw [listPC, midPC, BitVec.add_assoc]
    rfl
  have outTarget := outer_target base list atOuter
  have outLink := outer_link base list atOuter
  have outCall := finish_outer_call list listLive (by
    change canonical (outerCallState list).rip = true
    rw [outTarget]
    exact shaCanonical)
  let outer := hmacOuter key (sha256 inner).2
  have expected := outer_encoding_at_call list key (sha256 inner).2 (by rw [listSP]; exact encoding)
  have outEntry : PermissionEntry (shaAddress base) (outerCallState list) outer 120 authority :=
    establish_sha_entry (hmacOuter_layout key (sha256 inner).2) (by change 120 ≤ 120; decide)
      (by change 120 < 2 ^ 64; decide) (by rw [hmacOuter_length]; decide) expected (outerResources mid es header mask list checked headerRun maskRun listRun
        (listSP.trans midSP) (listMac.trans midMac) (by simpa only [midSP] using preserved)) outTarget listLive
      (by rw [outLink]; exact returnCanonical)
  obtain ⟨out, fs, final, _⟩ := sha256_callee outEntry
  have ⟨_, a2, outerSP, _⟩ := outer_call_registers list
  have spOut : out.regs.get .rsp = s.regs.get .rsp := by
    have stack : out.regs.get .rsp = (outerCallState list).regs.get .rsp + 8#64 := final.result.stack
    rw [stack, outerSP, BitVec.sub_add_cancel, listSP, midSP]
  refine ⟨out, ⟨⟨mid, header, mask, list, es, fs, localCall, checked, midPC, headerRun, maskRun, listRun,
    outCall, final, preserved, listSP.trans midSP, listMac.trans midMac, midSP,
    final.result.pc.trans outLink, spOut, ?_⟩⟩⟩
  rw [hmacFinish_calls inner key innerReady.bound, ← midMac, ← listMac, ← a2]
  exact final.result.digest

/-- The x86-64 finishing body's two nested calls return to the real
epilogue. The saved words and return slot are the memory-frame premises
for composing that epilogue with the helper's prologue. -/
theorem FinishBody.returned {base : Val} {s bodyOut : Cpu} {inner : ByteList} {k0 : HmacKeyBlock}
    {extent : Nat} {authority : Authority}
    (run : FinishBody base (enteredFrame .finish s) bodyOut inner k0 extent authority)
    (running : s.ms = none)
    (returnAddress : bodyOut.mem.readSize .q (bodyOut.regs.get .rsp + 184#64) =
      s.mem.readSize .q (s.regs.get .rsp))
    (returnCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true)
    (saved : ∀ i : Fin 6,
      bodyOut.mem.readSize .q (bodyOut.regs.get .rsp + 136#64 + BitVec.ofNat 64 (8 * (5 - i.val))) =
        s.regs.get (savedReg i)) :
    ∃ out, runRange finish 0 7 s = some (enteredFrame .finish s) ∧
      runRange finish 0xaf 8 bodyOut = some out ∧
      out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧
      out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
      (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧
      memoryBytes32 (byteView out.mem) (s.regs.get .rdx) = (hmacFinish inner k0).map UInt8.toBitVec := by
  have live : bodyOut.ms = none := run.outerHash.result.live
  obtain ⟨sp, link, cells⟩ := restored_stack_and_link bodyOut 136#64 7
  have resume : canonical (bodyOut.mem.readSize .q (bodyOut.regs.get .rsp + 184#64)) = true := by
    rw [returnAddress]
    exact returnCanonical
  have linkValue : bodyOut.mem.readSize .q (bodyOut.regs.get .rsp + 136#64 + 48#64) =
      s.mem.readSize .q (s.regs.get .rsp) := by
    rw [BitVec.add_assoc]
    exact returnAddress
  refine ⟨restoredState bodyOut 136#64 7, enter_frame .finish s running, (returns bodyOut live).2.2 resume,
    ?_, link.trans linkValue, ?_, ?_⟩
  · rw [sp, run.sp, entered_frame_stack]
    change s.regs.get .rsp - 48#64 - 136#64 + 136#64 + 56#64 = _
    rw [BitVec.sub_add_cancel, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro i
    rw [restored_register]
    exact saved i
  · rw [cells, ← entered_frame_register .finish s .rdx (by decide)]
    exact run.digest

end Crypto.HMACSHA256.X86_64
