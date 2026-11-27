import Proofs.HMACSHA256.Callee
import Proofs.HMACSHA256.RISCV64CallSites
import Proofs.HMACSHA256.RISCV64Frame
import Proofs.HMACSHA256.RISCV64Outer
import Proofs.HMACSHA256.RISCV64Ranges

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.ARM64.Imported (memoryBytes32)
open Crypto.Baseline (Region)

private theorem saved_key {s out : CPU} (saved : savedRegisters out = savedRegisters s) :
    out.reg 9#5 = s.reg 9#5 :=
  congrArg (fun v : Vector Addr 8 => v[1]) saved

private theorem saved_mac {s out : CPU} (saved : savedRegisters out = savedRegisters s) :
    out.reg 18#5 = s.reg 18#5 :=
  congrArg (fun v : Vector Addr 8 => v[2]) saved

private theorem digest_byte {m : Memory} {addr : Addr} {digest : Digest}
    (bytes : memoryBytes32 m addr = digest.map UInt8.toBitVec) (i : Fin 32) :
    m.read8 (addr + BitVec.ofNat 64 i.val) = digest[i.val].toBitVec := by
  have byte := congrArg (fun v : Vector (BitVec 8) 32 => v[i.val]) bytes
  simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map] using byte

private theorem outer_return_pc (base : Addr) (p : Addr)
    (inner : p = routineAddress base finish + 0x26#64) :
    p + 142#64 = routineAddress base finish + 0xb4#64 := by
  rw [inner, BitVec.add_assoc]
  rfl

/-- The finishing helper between its prologue and epilogue. Local blocks use
the decoded HMAC instructions. Both hashes run the existing checked SHA-256
machine execution, with their ABI and input encodings established separately. -/
structure FinishBody (base : Addr) (s out : CPU) (inner : ByteList) (k0 : HmacKeyBlock) where
  afterInner : CPU
  header : CPU
  mask : CPU
  outerList : CPU
  innerCall : runRange finish 0x1c 4 s = some (innerCallState s)
  innerHash : runUntilReturn (shaAddress base) (innerCallState s) (callSteps inner.bytes.size) = some afterInner
  innerContract : ∃ extent, CallerEntry (shaAddress base) (innerCallState s) inner extent
  innerReturn : afterInner.pc = routineAddress base finish + 0x26#64
  innerStack : afterInner.reg 2#5 = s.reg 2#5
  innerKey : afterInner.reg 9#5 = s.reg 11#5
  writeHeader : runRange finish 0x26 6 afterInner = some header
  preparePad : runRange finish 0x36 9 header = some mask
  writePad : runRange finish 0x54 24 mask = some outerList
  outerListPC : outerList.pc = routineAddress base finish + 0xb4#64
  outerCall : runRange finish 0xb4 3 outerList = some (outerCallState outerList)
  outerHash : runUntilReturn (shaAddress base) (outerCallState outerList) (callSteps 96) = some out
  outerContract : CallerEntry (shaAddress base) (outerCallState outerList)
    (hmacOuter k0 (sha256 inner).2) 120
  outerStack : outerList.reg 2#5 = s.reg 2#5
  outerMac : outerList.reg 18#5 = s.reg 12#5
  outerReturn : out.pc = routineAddress base finish + 0xbc#64
  sp : out.reg 2#5 = s.reg 2#5
  digest : memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec
  frame : ∀ p, 120 ≤ (p - s.reg 2#5).toNat →
    ¬ (callerStack (innerCallState s)).Contains p → ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains p →
    out.mem.cells p = s.mem.cells p

/-- The second call's argument registers described relative to the machine
state at the beginning of the body. The actual registers are established
by the decoded argument setup and the first callee's ABI theorem. -/
def outerBoundary (s : CPU) : CPU :=
  (s.put 10#5 (s.reg 2#5)).put 11#5 (s.reg 12#5)

theorem outer_boundary_registers (s : CPU) :
    (outerBoundary s).reg 10#5 = s.reg 2#5 ∧
    (outerBoundary s).reg 11#5 = s.reg 12#5 ∧
    (outerBoundary s).reg 2#5 = s.reg 2#5 ∧ (outerBoundary s).mem = s.mem := by
  unfold outerBoundary
  simp (config := { decide := true }) only [reg_put, memory_put, if_true, if_false, and_true]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem finish_body (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock) (extent : Nat)
    (pc : s.pc = routineAddress base finish + 0x1c#64)
    (layout : inner.WellFormed) (accessible : inner.size ≤ extent)
    (sizeBound : inner.size < 2 ^ 64) (lengthBound : inner.bytes.size < 2 ^ 61)
    (encoded : EncodedByteList s.mem (s.reg 10#5) inner)
    (innerResources : ShaResources (shaAddress base) (innerCallState s) extent)
    (innerCode : ShaCode (shaAddress base) s.mem)
    (innerLinkAligned : ((routineAddress base finish + 0x26#64 : Addr)).toNat % 2 = 0)
    (outerLinkAligned : ((routineAddress base finish + 0xbc#64 : Addr)).toNat % 2 = 0)
    (keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec)
    (keyOffStack : ∀ i : Fin 64, ¬ (callerStack (innerCallState s)).Contains
      (s.reg 11#5 + BitVec.ofNat 64 i.val))
    (keyOffDigest : ∀ i : Fin 64, ¬ (callerOutput (innerCallState s)).Contains
      (s.reg 11#5 + BitVec.ofNat 64 i.val))
    (keyOffHeader : ∀ i : Fin 64, 24 ≤ (s.reg 11#5 + BitVec.ofNat 64 i.val - s.reg 2#5).toNat)
    (keyOffPad : ∀ i : Fin 64, 64 ≤
      (s.reg 11#5 + BitVec.ofNat 64 i.val - (s.reg 2#5 + 24#64)).toNat)
    (outerResources : ShaResources (shaAddress base) (outerBoundary s) 120)
    (outerListOffImage : ∀ p, (callerImage (shaAddress base)).Contains p →
      88 ≤ (p - s.reg 2#5).toNat) :
    ∃ out, Nonempty (FinishBody base s out inner k0) := by
  obtain ⟨a0, a1, key, mac, sp, _, mem⟩ := inner_call_registers s
  have innerEntry : CallerEntry (shaAddress base) (innerCallState s) inner extent :=
    establish_sha_entry layout accessible sizeBound lengthBound
      (by
        change EncodedByteList (innerCallState s).mem ((innerCallState s).reg 10#5) inner
        rw [a0, mem]
        exact encoded)
      innerResources (by rw [mem]; exact innerCode) (inner_call_target base s pc)
      (by
        change ((innerCallState s).reg 1#5).toNat % 2 = 0
        rw [callee_return_at_inner base s pc]
        exact innerLinkAligned)
  obtain ⟨mid, hash, result, frame, _⟩ := sha256_callee (shaAddress base) (innerCallState s) inner extent innerEntry
  have midSp : mid.reg 2#5 = s.reg 2#5 := result.sp.trans sp
  have midKey := (saved_key result.restored).trans key
  have midMac := (saved_mac result.restored).trans mac
  have midPC := result.pc.trans (callee_return_at_inner base s pc)
  have innerBytes (i : Fin 32) :
      mid.mem.read8 (mid.reg 2#5 + 88#64 + BitVec.ofNat 64 i.val) = (sha256 inner).2[i.val].toBitVec := by
    rw [midSp, ← a1]
    exact digest_byte result.digest i
  have midKeyBytes (i : Fin 64) : mid.mem.read8 (mid.reg 9#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec := by
    rw [midKey]
    unfold Arm64.Memory.read8
    rw [frame _ (keyOffStack i) (keyOffDigest i), mem]
    exact keyAt i
  obtain ⟨header, mask, list, headerRun, maskRun, listRun, stack, address, afterPad, encoding, padFrame, padPerm, padRead⟩ :=
    finish_outer_list mid k0 (sha256 inner).2
      (by rw [midKey, midSp]; exact keyOffHeader)
      (by rw [midKey, midSp]; exact keyOffPad) midKeyBytes innerBytes
  obtain ⟨input, output, stackOut, _, listMem⟩ := outer_call_registers list
  have listPC := outer_return_pc base mid.pc midPC
  have listSP := stack.trans midSp
  have listMac := address.trans midMac
  have listAt : list.pc = routineAddress base finish + 0xb4#64 := afterPad.trans listPC
  obtain ⟨_, innerPath, _⟩ := sha_segment hash
  have perm (p : Addr) : list.mem.perm p = s.mem.perm p :=
    (padPerm p).trans ((innerPath.perm p).trans (congrArg (fun m : Memory => m.perm p) mem))
  have readable (p : Addr) (n : Nat) (h : s.mem.canRead p n = true) : list.mem.canRead p n = true :=
    padRead p n ((innerPath.permissions p n).2 (by rw [mem]; exact h))
  have code := innerCode.preserved
    (fun p h =>
      (padFrame p (by rw [midSp]; exact outerListOffImage p h)).trans
        ((frame p
          (fun inside => innerResources.stackImage p ⟨inside, h⟩)
          (fun inside => innerResources.outputImage p ⟨inside, h⟩)).trans
          (congrArg (fun m : Memory => m.cells p) mem)))
    perm readable
  obtain ⟨a0', a1', sp', m'⟩ := outer_boundary_registers s
  have resources : ShaResources (shaAddress base) (outerCallState list) 120 :=
    outerResources.preserved
      (input.trans (listSP.trans a0'.symm)) (output.trans (listMac.trans a1'.symm))
      (stackOut.trans (listSP.trans sp'.symm))
      (by rw [listMem, m']; exact perm) (by rw [listMem, m']; exact readable)
  let outer := hmacOuter k0 (sha256 inner).2
  have outerLayout : outer.WellFormed := hmacOuter_layout k0 (sha256 inner).2
  have outerSize : outer.size = 120 := rfl
  have outerLength : outer.bytes.size = 96 := hmacOuter_length _ _
  have outerEntry : CallerEntry (shaAddress base) (outerCallState list) outer 120 :=
    establish_sha_entry outerLayout (by omega) (by rw [outerSize]; decide) (by rw [outerLength]; decide)
      (by
        change EncodedByteList (outerCallState list).mem ((outerCallState list).reg 10#5) outer
        rw [input, listMem, stack]
        exact encoding) resources (by rw [listMem]; exact code)
      (outer_call_target base list listAt)
      (by
        change ((outerCallState list).reg 1#5).toNat % 2 = 0
        rw [callee_return_at_outer base list listAt]
        exact outerLinkAligned)
  obtain ⟨out, finalHash, finalResult, outerFrame, _⟩ := sha256_callee (shaAddress base) (outerCallState list) outer 120 outerEntry
  rw [outerLength] at finalHash
  refine ⟨out, ⟨⟨mid, header, mask, list, inner_call s, hash, ⟨extent, innerEntry⟩, midPC, midSp, midKey, headerRun, maskRun, listRun,
    listAt, outer_call list, finalHash, outerEntry, listSP, listMac, finalResult.pc.trans (callee_return_at_outer base list listAt),
    (finalResult.sp.trans stackOut).trans listSP, ?_, ?_⟩⟩⟩
  · rw [hmacFinish_calls inner k0 innerEntry.length, ← listMac, ← output]
    exact finalResult.digest
  · intro p outside awayStack awayMac
    have stackSame : callerStack (outerCallState list) = callerStack (innerCallState s) := by
      have same := (stackOut.trans listSP).trans sp.symm
      simp only [callerStack, entryStack]
      change (⟨(outerCallState list).reg 2#5 - 480, 480⟩ : Region) =
        ⟨(innerCallState s).reg 2#5 - 480, 480⟩
      rw [same]
    have macRegion : callerOutput (outerCallState list) = ⟨s.reg 12#5, 32⟩ := by
      change (⟨(outerCallState list).reg 11#5, 32⟩ : Region) = _
      rw [output, listMac]
    have temp : ¬ (callerOutput (innerCallState s)).Contains p := by
      intro inside
      change (⟨(innerCallState s).reg 11#5, 32⟩ : Region).Contains p at inside
      rw [a1] at inside
      change (s.reg 2#5 + 88#64).toNat ≤ p.toNat ∧ p.toNat < (s.reg 2#5 + 88#64).toNat + 32 at inside
      have available := outerResources.inputValid
      change ((outerBoundary s).reg 10#5).toNat + 120 ≤ 2 ^ 64 at available
      rw [a0'] at available
      rw [BitVec.toNat_add, show (88#64).toNat = 88 from rfl,
        Nat.mod_eq_of_lt (by omega : (s.reg 2#5).toNat + 88 < 2 ^ 64)] at inside
      rw [BitVec.toNat_sub] at outside
      have cap := (s.reg 2#5).isLt
      omega
    calc
      out.mem.cells p = (outerCallState list).mem.cells p :=
        outerFrame p (stackSame ▸ awayStack) (macRegion ▸ awayMac)
      _ = list.mem.cells p := congrArg (fun m : Memory => m.cells p) listMem
      _ = mid.mem.cells p := padFrame p (by rw [midSp]; omega)
      _ = (innerCallState s).mem.cells p := frame p awayStack temp
      _ = s.mem.cells p := congrArg (fun m : Memory => m.cells p) mem

set_option maxHeartbeats 1500000 in
/-- Compose the local fetched ranges with the two SHA-256 executions.
The five range permissions are checked at their concrete instruction
states. Neither callee is replaced by a specification-only step. -/
theorem FinishBody.execution {base : Addr} {s out : CPU} {inner : ByteList} {k0 : HmacKeyBlock}
    (run : FinishBody base s out inner k0)
    (loaded : finish.Loaded (routineAddress base finish) s.mem.read8)
    (readonly : RoutineReadOnly finish base s.mem)
    (beforeInner : RangeAllowed finish base 0x1c 4 s)
    (header : RangeAllowed finish base 0x26 6 run.afterInner)
    (mask : RangeAllowed finish base 0x36 9 run.header)
    (pad : RangeAllowed finish base 0x54 24 run.mask)
    (beforeOuter : RangeAllowed finish base 0xb4 3 run.outerList) :
    ∃ events, ProgramExecution base s events out ∧
      events.length ≤ 46 + callSteps inner.bytes.size + callSteps 96 := by
  have body : finish = entry ∨ finish = key ∨ finish = finish := .inr (.inr rfl)
  obtain ⟨a, setupA, na⟩ := run_range_executes body run.innerCall loaded readonly beforeInner
  obtain ⟨b, hashA, nb⟩ := sha_segment run.innerHash
  have hs := setupA.append hashA
  obtain ⟨m0, ro0⟩ := hs.keeps_routine loaded readonly
  obtain ⟨c, headerRun, nc⟩ := run_range_executes body run.writeHeader m0 ro0 header
  obtain ⟨m1, ro1⟩ := headerRun.keeps_routine m0 ro0
  obtain ⟨d, maskRun, nd⟩ := run_range_executes body run.preparePad m1 ro1 mask
  obtain ⟨m2, ro2⟩ := maskRun.keeps_routine m1 ro1
  obtain ⟨e, padRun, ne⟩ := run_range_executes body run.writePad m2 ro2 pad
  obtain ⟨m3, ro3⟩ := padRun.keeps_routine m2 ro2
  obtain ⟨f, setupB, nf⟩ := run_range_executes body run.outerCall m3 ro3 beforeOuter
  obtain ⟨g, hashB, ng⟩ := sha_segment run.outerHash
  refine ⟨(a ++ b) ++ (c ++ (d ++ (e ++ (f ++ g)))),
    hs.append (headerRun.append (maskRun.append (padRun.append (setupB.append hashB)))), ?_⟩
  simp only [List.length_append]
  omega

set_option maxHeartbeats 1700000 in
/-- Compose a verified finishing body with the decoded prologue and epilogue.
The caller's stack reservation and the MAC separation protect the saved
register slots through both SHA-256 calls and local writes. -/
theorem FinishBody.returned {base : Addr} {s bodyOut : CPU} {inner : ByteList} {k0 : HmacKeyBlock}
    (run : FinishBody base (enteredFrame .finish s) bodyOut inner k0)
    (stackAvailable : 720 ≤ (s.reg 2#5).toNat)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0)
    (macOffSaves : ∀ i : Fin 104, ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains
      ((enteredFrame .finish s).reg 2#5 + BitVec.ofNat 64 (128 + i.val))) :
    ∃ out, runRange finish 0 14 s = some (enteredFrame .finish s) ∧
      runRange finish 0xbc 15 bodyOut = some out ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec := by
  let start := enteredFrame .finish s
  have stackNat : (start.reg 2#5).toNat = (s.reg 2#5).toNat - 240 := by
    rw [show start.reg 2#5 = s.reg 2#5 - 240#64 from enteredFrame_sp .finish s, BitVec.toNat_sub]
    have upper := (s.reg 2#5).isLt
    change (2 ^ 64 - 240 + (s.reg 2#5).toNat) % 2 ^ 64 = _
    omega
  have stackEnd : (callerStack (innerCallState start)).base.toNat + 480 = (start.reg 2#5).toNat := by
    change (((innerCallState start).reg 2#5) - (480 : Addr)).toNat + 480 = _
    rw [(inner_call_registers start).2.2.2.2.1, BitVec.toNat_sub]
    have upper := (start.reg 2#5).isLt
    change (2 ^ 64 - 480 + (start.reg 2#5).toNat) % 2 ^ 64 + 480 = _
    omega
  have keep (i : Fin 104) :
      let p := bodyOut.reg 2#5 + BitVec.ofNat 64 (HmacRoutine.savedOffset .finish + i.val)
      bodyOut.mem.cells p = start.mem.cells p := by
    dsimp only
    rw [run.sp]
    apply run.frame
    · change 120 ≤ (start.reg 2#5 + BitVec.ofNat 64 (128 + i.val) - start.reg 2#5).toNat
      rw [Crypto.ARM64.Imported.address_delta, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    · intro inside
      have hi := i.isLt
      have cap := (s.reg 2#5).isLt
      have address : (start.reg 2#5 + BitVec.ofNat 64 (128 + i.val)).toNat =
          (start.reg 2#5).toNat + 128 + i.val := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 128 + i.val < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : (start.reg 2#5).toNat + (128 + i.val) < 2 ^ 64)]
        omega
      have before := inside.2
      change (start.reg 2#5 + BitVec.ofNat 64 (128 + i.val)).toNat <
        (callerStack (innerCallState start)).base.toNat + 480 at before
      rw [address, stackEnd] at before
      omega
    · rw [enteredFrame_reg .finish s 12#5 (by decide)]
      exact macOffSaves i
  obtain ⟨sp, pc, registers⟩ := epilogue_restores .finish s bodyOut run.sp linkAligned keep
  refine ⟨restoredFrame .finish bodyOut, enter_frame .finish s, return_frame .finish bodyOut,
    sp, pc, registers, ?_⟩
  rw [restoredFrame_memory, ← enteredFrame_reg .finish s 12#5 (by decide)]
  exact run.digest

set_option maxHeartbeats 1700000 in
/-- With the range permissions established, the full finishing helper
executes from its loaded prologue to its real return address in a bounded
number of instructions, including both SHA-256 calls. -/
theorem FinishBody.full_execution {base : Addr} {s bodyOut : CPU}
    {inner : ByteList} {k0 : HmacKeyBlock}
    (run : FinishBody base (enteredFrame .finish s) bodyOut inner k0)
    (loaded : finish.Loaded (routineAddress base finish) s.mem.read8)
    (readonly : RoutineReadOnly finish base s.mem)
    (stackAvailable : 720 ≤ (s.reg 2#5).toNat)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0)
    (macOffSaves : ∀ i : Fin 104, ¬ (⟨s.reg 12#5, 32⟩ : Region).Contains
      ((enteredFrame .finish s).reg 2#5 + BitVec.ofNat 64 (128 + i.val)))
    (prologue : RangeAllowed finish base 0 14 s)
    (beforeInner : RangeAllowed finish base 0x1c 4 (enteredFrame .finish s))
    (header : RangeAllowed finish base 0x26 6 run.afterInner)
    (mask : RangeAllowed finish base 0x36 9 run.header)
    (pad : RangeAllowed finish base 0x54 24 run.mask)
    (beforeOuter : RangeAllowed finish base 0xb4 3 run.outerList)
    (epilogue : RangeAllowed finish base 0xbc 15 bodyOut) :
    ∃ out events,
      ProgramExecution base s events out ∧ events.length ≤ 75 + callSteps inner.bytes.size + callSteps 96 ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec := by
  obtain ⟨out, pro, ret, stack, address, regs, digest⟩ :=
    run.returned stackAvailable linkAligned macOffSaves
  have body : finish = entry ∨ finish = key ∨ finish = finish := .inr (.inr rfl)
  obtain ⟨a, first, na⟩ := run_range_executes body pro loaded readonly prologue
  obtain ⟨loadA, readonlyA⟩ := first.keeps_routine loaded readonly
  obtain ⟨b, middle, nb⟩ := run.execution loadA readonlyA beforeInner header mask pad beforeOuter
  obtain ⟨loadB, readonlyB⟩ := middle.keeps_routine loadA readonlyA
  obtain ⟨c, last, nc⟩ := run_range_executes body ret loadB readonlyB epilogue
  refine ⟨out, a ++ (b ++ c), first.append (middle.append last), ?_, stack, address, regs, digest⟩
  simp only [List.length_append]
  omega

end Crypto.HMACSHA256.RISCV64
