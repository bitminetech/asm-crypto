import Proofs.HMACSHA256.ARM64EntryReturn
import Proofs.HMACSHA256.ARM64Inner

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference
open Crypto.Baseline (Region)

structure EntryCode (base : Addr) (s : Arm64.State) : Prop where
  entry : (programAt entry (routineAddress base entry)).CodeLoaded s.mem
  key : (programAt key (routineAddress base key)).CodeLoaded s.mem
  finish : (programAt finish (routineAddress base finish)).CodeLoaded s.mem
  sha : (program (shaAddress base)).CodeLoaded s.mem

structure EntryResult (s out : Arm64.State) (keyValue message : ByteList) (capacity : Nat) : Prop where
  status : out.readReg64 .x0 = BitVec.ofNat 64 (hmacSha256 keyValue message capacity).status
  sp : out.sp = s.sp
  link : out.pc = s.readReg64 .lr
  live : out.status = .Running
  saved : ∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)
  smallFrame : capacity < hmacScratchRequired message →
    ∀ p, ¬ (entrySaved s).Contains p → out.mem.cells p = s.mem.cells p
  mac : hmacScratchRequired message ≤ capacity →
    memoryBytes32 out.mem (s.readReg64 .x3) = (EthLib.Cryptography.Hash.Hmac.hmac32 keyValue.bytes message.bytes).map UInt8.toBitVec
  scratch : hmacScratchRequired message ≤ capacity →
    EncodedByteList out.mem (s.readReg64 .x2 + 8#64) (hmacInner message (hmacKey keyValue) capacity)
  frame : ∀ p, ¬ (entryWorkspace s).Contains p →
    ¬ (⟨s.readReg64 .x2 + 8#64, 88 + message.bytes.size⟩ : Region).Contains p →
    ¬ (entryMac s).Contains p → out.mem.cells p = s.mem.cells p

structure EntrySuccessTrace (base : Addr) (s : Arm64.State) (keyValue message : ByteList) (capacity : Nat) where
  keyStart : Arm64.State
  keyEvents : List InstructionObservation
  keyTrace : KeyWholeTrace base keyStart keyValue keyEvents
  keyPC : keyStart.pc = routineAddress base key
  keySP : keyStart.sp = s.sp - 160#64
  keyInput : keyStart.readReg64 .x0 = s.readReg64 .x0
  keyOutput : keyStart.readReg64 .x1 = s.sp - 160#64 + 96#64
  keyLink : keyStart.readReg64 .lr = routineAddress base entry + 0x54#64
  innerStart : Arm64.State
  innerEvents : List InstructionObservation
  innerTrace : InnerTrace base innerStart message innerEvents
  innerPC : innerStart.pc = routineAddress base entry + 0x54#64
  innerSP : innerStart.sp = s.sp - 160#64
  messageInput : innerStart.readReg64 .x20 = s.readReg64 .x1
  scratch : innerStart.readReg64 .x21 = s.readReg64 .x2
  finishStart : Arm64.State
  finishOut : Arm64.State
  finishTrace : FinishBody base (enteredState finishStart 224#64) finishOut
    (hmacInner message (hmacKey keyValue) capacity) (hmacKey keyValue)
  finishPC : finishStart.pc = routineAddress base finish
  finishSP : finishStart.sp = s.sp - 160#64
  finishInput : finishStart.readReg64 .x0 = s.readReg64 .x2 + 8#64
  finishKey : finishStart.readReg64 .x1 = s.sp - 160#64 + 96#64
  finishMac : finishStart.readReg64 .x2 = s.readReg64 .x3
  finishLink : finishStart.readReg64 .lr = routineAddress base entry + 0x110#64

def EntrySuccessTrace.events {base : Addr} {s : Arm64.State} {keyValue message : ByteList} {capacity : Nat}
    (trace : EntrySuccessTrace base s keyValue message capacity) : List InstructionObservation :=
  let stack := s.sp - 160#64
  entryKeyCallEvents base stack ++ trace.keyEvents ++ trace.innerEvents ++ entryFinishCallEvents base stack ++
    trace.finishTrace.nativeTrace ++ entrySuccessEvents base stack

def entryReturnEvents (base : Addr) (s : Arm64.State) : List InstructionObservation :=
  frameReturnEvents (routineAddress base entry + 0x114#64) (s.sp - 160#64) 160#64 (s.readReg64 .lr)

inductive EntryTrace (base : Addr) (s : Arm64.State) (keyValue message : ByteList) (capacity : Nat) :
    List InstructionObservation → Prop where
  | small (small : capacity < hmacScratchRequired message) :
      EntryTrace base s keyValue message capacity
        (entryPrefixEvents base s capacity message.bytes.size ++ entryReturnEvents base s)
  | full (room : hmacScratchRequired message ≤ capacity) (body : EntrySuccessTrace base s keyValue message capacity) :
      EntryTrace base s keyValue message capacity
        (entryPrefixEvents base s capacity message.bytes.size ++ body.events ++ entryReturnEvents base s)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6500000 in
/-- Whole linked ARM64 HMAC entry, including the undersized return
and both nested helpers on the sufficient-capacity path. -/
theorem entry_execution_from_caller (base : Addr) (s : Arm64.State)
    (keyValue message : ByteList) (keyExtent messageExtent capacity : Nat)
    (keyLayout : keyValue.WellFormed) (messageLayout : message.WellFormed)
    (keyAccessible : keyValue.size ≤ keyExtent) (messageAccessible : message.size ≤ messageExtent)
    (keySize : keyValue.size < 2 ^ 64) (keyLength : keyValue.bytes.size < 2 ^ 61)
    (messageLength : message.bytes.size < 2 ^ 61 - 64)
    (keyValueAt : EncodedByteList s.mem (s.readReg64 .x0) keyValue)
    (messageAt : EncodedByteList s.mem (s.readReg64 .x1) message)
    (capacityAt : s.mem.read64 (s.readReg64 .x2) = BitVec.ofNat 64 capacity)
    (capMin : 8 ≤ capacity) (cap64 : capacity < 2 ^ 64)
    (g : EntryResources base s keyExtent messageExtent capacity) (loaded : EntryCode base s)
    (pc : s.pc = routineAddress base entry) (live : s.status = .Running) :
    ∃ out events, LinkedExecution base s events out ∧ EntryResult s out keyValue message capacity ∧
      EntryTrace base s keyValue message capacity events := by
  let work := entryWorkspace s
  let spills := entrySaved s
  let block := regionSlice work 736 64
  let keyWork := regionSlice work 128 512
  let finishWork := regionSlice work 0 640
  let scratch := entryScratch s capacity
  let innerRegion := regionSlice scratch 8 (capacity - 8)
  let written := regionSlice scratch 8 (88 + message.bytes.size)
  let k0 := hmacKey keyValue
  let inner := hmacInner message k0 capacity
  have workValid : work.Valid := stackRegion_valid _ _ g.available
  have workFit (off n : Nat) (fits : off + n ≤ 800) : off + n ≤ work.bytes := fits
  have blockValid : block.Valid := regionSlice_valid _ _ _ workValid (workFit 736 64 (by decide))
  have inBlock (p : Addr) (h : block.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ workValid (workFit 736 64 (by decide)) p h
  have inKeyStack (p : Addr) (h : keyWork.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ workValid (workFit 128 512 (by decide)) p h
  have inFinishStack (p : Addr) (h : finishWork.Contains p) : work.Contains p :=
    regionSlice_inside _ _ _ workValid (workFit 0 640 (by decide)) p h
  have insideInner (p : Addr) (h : innerRegion.Contains p) : scratch.Contains p :=
    regionSlice_inside _ _ _ g.scratchValid (by change _ ≤ capacity; omega) p h
  have keyFinishSp (off : Nat) : work.base + BitVec.ofNat 64 (640 + off) =
      (s.sp - 160#64) + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact congrArg (· + BitVec.ofNat 64 off)
      (congrArg Region.base (stackRegion_slice s.sp 800 640 96 (by decide)))
  have blockBase : block.base = s.sp - 160#64 + 96#64 := keyFinishSp 96
  have spillsEq : spills = regionSlice work 640 96 := by
    exact (stackRegion_slice s.sp 800 640 96 (by decide)).symm
  have spillsBase : spills.base = s.sp - 160#64 := rfl
  have spillsValid : spills.Valid := by
    rw [spillsEq]
    exact regionSlice_valid _ _ _ workValid (workFit 640 96 (by decide))
  have inSpill (p : Addr) (h : spills.Contains p) : work.Contains p := by
    rw [spillsEq] at h
    exact regionSlice_inside _ _ _ workValid (workFit 640 96 (by decide)) p h
  have stackRead (i : Fin 12) : s.mem.canRead (s.sp - 160#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    rw [← keyFinishSp]
    exact caller_region_read _ work workValid g.stackRead (640 + 8 * i.val) 8
      (workFit _ _ (by have := i.isLt; omega))
  have low : 160 ≤ s.sp.toNat := by have := g.available; omega
  have frameAlign : (s.sp - 160#64).toNat % 16 = 0 := stackRegion_aligned s.sp 160 g.aligned (by decide) low
  have mask := stack_mask (s.sp - 160#64) frameAlign
  have frameBound := frame_base_end s.sp 160 low
  have msgMin : 24 ≤ messageExtent := by
    have off := messageLayout.1
    have fits := messageLayout.2.2.1
    omega
  obtain ⟨checked, ⟨front⟩⟩ := entry_prefix base s keyExtent messageExtent capacity message.bytes.size
    g capMin msgMin cap64 (by omega) capacityAt messageAt.count pc live loaded.entry
  by_cases short : capacity < hmacScratchRequired message
  · have endPC : checked.pc = routineAddress base entry + 0x114#64 := by
      rw [front.pc, if_pos (show capacity < 96 + message.bytes.size from short)]
    have aligned : checked.spAligned = true := by simp [Arm64.State.spAligned, front.sp, mask]
    obtain ⟨out, ret, status, sp, link, running, regs, memory⟩ :=
      entry_return base s checked (front.execution.keeps_code _ loaded.entry) endPC front.live
        front.sp aligned (fun i => by rw [front.sp]; exact front.execution.grants.read _ _ (stackRead i))
        (by rw [front.memory]; exact fun _ => rfl)
    refine ⟨out, _, front.execution.append ret, ⟨?_, sp, link, running, regs, ?_, ?_, ?_, ?_⟩, .small short⟩
    · rw [status, front.status, hmacSha256_insufficient _ _ _ short]
      rfl
    · intro _ p off
      rw [memory]
      exact front.frame p off
    · intro enough
      exact False.elim (Nat.not_le.mpr short enough)
    · intro enough
      exact False.elim (Nat.not_le.mpr short enough)
    · intro p off _ _
      rw [memory]
      exact front.frame p (fun h => off (inSpill p h))
  · have enough : hmacScratchRequired message ≤ capacity := Nat.le_of_not_gt short
    have room : 96 + message.bytes.size ≤ capacity := enough
    have guardPC : checked.pc = routineAddress base entry + 0x48#64 := by rw [front.pc, if_neg (show ¬ capacity < 96 + message.bytes.size from short)]
    let keyCall := entryKeyCall checked
    obtain ⟨keyPC, keyLink⟩ := entry_key_target base checked guardPC
    have body : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
    obtain ⟨toKey, _⟩ := run_range_observes body guardPC (by decide)
      (front.execution.keeps_code _ loaded.entry) (by decide +kernel)
      (entry_key_call checked) (show keyCall.status = .Running from front.live)
    have beforeKey := front.execution.append toKey
    have keyPtr : keyCall.readReg64 .x0 = s.readReg64 .x0 := by
      simpa (config := {decide := true}) only [keyCall, entryKeyCall, reg_set_pc, reg_write_gpr,
        Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.lr, if_true, if_false] using front.key
    have keyDst : keyCall.readReg64 .x1 = block.base := by
      rw [blockBase, ← front.sp]
      simp (config := {decide := true}) only [keyCall, entryKeyCall, reg_set_pc, reg_write_gpr,
        Arm64.Reg.x1, Arm64.Reg.lr, if_true, if_false]
    have keySp : keyCall.sp = s.sp - 160#64 := front.sp
    have keySrc : keyInput keyCall keyExtent = entryKeyInput s keyExtent := by
      simp only [keyInput, entryKeyInput, keyPtr]
    have keyOut : keyOutput keyCall = block := by
      change (⟨keyCall.readReg64 .x1, 64⟩ : Region) = ⟨block.base, 64⟩
      rw [keyDst]
    have keyStack : keyWorkspace keyCall = keyWork := by
      unfold keyWorkspace
      rw [keySp]
      change (⟨(s.sp - 160#64) - 512#64, 512⟩ : Region) = _
      change (⟨(s.sp - 160#64) - 512#64, 512⟩ : Region) = regionSlice (stackRegion s.sp 800) 128 512
      rw [BitVec.sub_sub, stackRegion_slice s.sp 800 128 512 (by decide)]
      rfl
    have keyAligned : block.base.toNat % 8 = 0 := by
      rw [blockBase, BitVec.toNat_add]
      change ((s.sp - 160#64).toNat + 96) % (2 ^ 64) % 8 = 0
      omega
    have keyGrant : KeyResources base keyCall keyExtent := {
      available := by rw [keySp]; have := g.available; omega
      aligned := keySp.symm ▸ frameAlign
      inputAligned := keyPtr.symm ▸ g.keyAligned
      outputAligned := keyDst.symm ▸ keyAligned
      inputValid := keySrc.symm ▸ g.keyValid
      outputValid := keyOut.symm ▸ blockValid
      imageValid := g.imageValid
      stackInput := fun p h => g.stackKey p ⟨inKeyStack p (keyStack ▸ h.1), keySrc ▸ h.2⟩
      stackOutput := by
        rw [keyStack, keyOut]
        exact regionSlices_disjoint work 128 512 736 64 workValid (by decide) (workFit _ _ (by decide))
      stackImage := fun p h => g.stackImage p ⟨inKeyStack p (keyStack ▸ h.1), h.2⟩
      outputInput := fun p h => g.stackKey p ⟨inBlock p (keyOut ▸ h.1), keySrc ▸ h.2⟩
      outputImage := fun p h => g.stackImage p ⟨inBlock p (keyOut ▸ h.1), h.2⟩
      inputRead := fun p h => beforeKey.grants.read _ _ (g.keyRead p (keySrc ▸ h))
      outputWrite := fun p h => by
        rw [beforeKey.grants.write]
        exact g.stackWrite p (inBlock p (keyOut ▸ h))
      stackRead := fun p h => beforeKey.grants.read _ _ (g.stackRead p (inKeyStack p (keyStack ▸ h)))
      stackWrite := fun p h => by
        rw [beforeKey.grants.write]
        exact g.stackWrite p (inKeyStack p (keyStack ▸ h))
    }
    have actualKey : EncodedByteList keyCall.mem (keyCall.readReg64 .x0) keyValue := by
      change EncodedByteList checked.mem (keyCall.readReg64 .x0) keyValue
      rw [keyPtr]
      exact keyValueAt.preserved keyLayout keyAccessible g.keyValid
        (fun p hit => front.frame p (fun held => g.stackKey p ⟨inSpill p held, hit⟩))
    obtain ⟨afterKey, keyEvents, deriveKey, afterKeySp, afterKeyPc, afterKeyLive, keyRegs, keyBytes, keyFrame, keyTrace⟩ :=
      key_execution_from_caller base keyCall keyValue keyExtent keyLayout keyAccessible keySize keyLength
        actualKey keyGrant keyPC front.live (beforeKey.keeps_code _ loaded.sha) (beforeKey.keeps_code _ loaded.key)
    have throughKey := beforeKey.append deriveKey
    have afterKeyMsg : afterKey.readReg64 .x20 = s.readReg64 .x1 := by
      have wanted : afterKey.readReg64 .x20 = keyCall.readReg64 .x20 := keyRegs ⟨3, by decide⟩
      exact wanted.trans ((show keyCall.readReg64 .x20 = checked.readReg64 .x20 from by
        simp (config := {decide := true}) [keyCall, entryKeyCall, Arm64.Reg.x20, Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.lr]).trans front.message)
    have afterKeyScratch : afterKey.readReg64 .x21 = s.readReg64 .x2 := by
      have wanted : afterKey.readReg64 .x21 = keyCall.readReg64 .x21 := keyRegs ⟨4, by decide⟩
      exact wanted.trans ((show keyCall.readReg64 .x21 = checked.readReg64 .x21 from by
        simp (config := {decide := true}) [keyCall, entryKeyCall, Arm64.Reg.x21, Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.lr]).trans front.scratch)
    have afterKeyMac : afterKey.readReg64 .x22 = s.readReg64 .x3 := by
      have wanted : afterKey.readReg64 .x22 = keyCall.readReg64 .x22 := keyRegs ⟨5, by decide⟩
      exact wanted.trans ((show keyCall.readReg64 .x22 = checked.readReg64 .x22 from by
        simp (config := {decide := true}) [keyCall, entryKeyCall, Arm64.Reg.x22, Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.lr]).trans front.mac)
    have afterKeyFrame (p : Addr) (off : ¬ work.Contains p) : afterKey.mem.cells p = s.mem.cells p :=
      (keyFrame p (fun h => off (inKeyStack p (keyStack ▸ h))) (fun h => off (inBlock p (keyOut ▸ h)))).trans
        (front.frame p (fun h => off (inSpill p h)))
    have msgHere : EncodedByteList afterKey.mem (afterKey.readReg64 .x20) message := by
      rw [afterKeyMsg]
      exact messageAt.preserved messageLayout messageAccessible g.messageValid
        (fun p hit => afterKeyFrame p (fun held => g.stackMessage p ⟨held, hit⟩))
    have scratchAt : afterKey.mem.read64 (afterKey.readReg64 .x21) = BitVec.ofNat 64 capacity := by
      rw [afterKeyScratch, ← capacityAt]
      apply read64_eq_of_cells
      intro i
      apply afterKeyFrame
      intro held
      have hit := caller_region_contains_offset scratch g.scratchValid i.val (by have := i.isLt; change _ < capacity; omega)
      exact g.stackScratch _ ⟨held, hit⟩
    have blockHere : afterKey.sp + 96#64 = block.base := by rw [afterKeySp, keySp, blockBase]
    obtain ⟨prepared, prepEvents, prep, prepPC, prepSp, prepLive, prepScratch, prepMac, encoded, prepFrame, ⟨prepTrace⟩⟩ :=
      entry_inner_list base afterKey message k0 capacity messageExtent messageLayout messageAccessible msgHere scratchAt
        room cap64 (by rw [afterKeyScratch]; exact g.scratchValid) (by rw [afterKeyMsg]; exact g.messageValid)
        (by rw [blockHere]; exact blockValid) (by rw [afterKeyScratch, afterKeyMsg]; exact g.scratchMessage)
        (by rw [afterKeyScratch, blockHere]; exact fun p h => g.stackScratch p ⟨inBlock p h.2, h.1⟩)
        (by rw [blockHere, ← keyDst]; exact keyBytes)
        (by
          rw [afterKeyScratch]
          apply throughKey.grants.read
          simpa only [BitVec.add_zero] using caller_region_read _ scratch g.scratchValid g.scratchRead 0 8 capMin)
        (fun p h => by
          rw [throughKey.grants.write]
          exact g.scratchWrite p (by rwa [afterKeyScratch] at h))
        (fun p h => throughKey.grants.read _ _ (g.messageRead p (by rwa [afterKeyMsg] at h)))
        (fun p h => throughKey.grants.read _ _ (g.stackRead p (inBlock p (by rwa [blockHere] at h))))
        (afterKeyPc.trans keyLink) (throughKey.keeps_code _ loaded.entry) afterKeyLive
    have throughPrep := throughKey.append prep
    let fin := entryFinishCall prepared
    obtain ⟨finishPC, finishLink⟩ := entry_finish_target base prepared prepPC
    obtain ⟨toFin, _⟩ := run_range_observes body prepPC (by decide)
      (throughPrep.keeps_code _ loaded.entry) (by decide +kernel) (entry_finish_call prepared)
      (show fin.status = .Running from prepLive)
    have beforeFinish := throughPrep.append toFin
    have finInput : fin.readReg64 .x0 = scratch.base + 8#64 := by
      have h := prepScratch.trans afterKeyScratch
      simp (config := {decide := true}) only [fin, entryFinishCall, Arm64.Reg.x0, Arm64.Reg.x1,
        Arm64.Reg.x2, Arm64.Reg.lr, reg_set_pc, reg_write_gpr, if_true, if_false]
      rw [h]
      rfl
    have finBlock : fin.readReg64 .x1 = block.base := by
      simp (config := {decide := true}) only [fin, entryFinishCall, Arm64.Reg.x1,
        Arm64.Reg.x2, Arm64.Reg.lr, reg_set_pc, reg_write_gpr, if_true, if_false]
      rw [prepSp, blockHere]
    have finMac : fin.readReg64 .x2 = s.readReg64 .x3 := by
      simpa (config := {decide := true}) only [fin, entryFinishCall, Arm64.Reg.x2,
        Arm64.Reg.lr, reg_set_pc, reg_write_gpr, if_true, if_false] using prepMac.trans afterKeyMac
    have finSp : fin.sp = s.sp - 160#64 := prepSp.trans (afterKeySp.trans keySp)
    have finWork : finishWorkspace fin = finishWork := by
      unfold finishWorkspace
      rw [finSp]
      change (⟨(s.sp - 160#64) - 640#64, 640⟩ : Region) = _
      change (⟨(s.sp - 160#64) - 640#64, 640⟩ : Region) = regionSlice (stackRegion s.sp 800) 0 640
      rw [BitVec.sub_sub, stackRegion_slice s.sp 800 0 640 (by decide)]
      rfl
    have finIn : finishInput fin (capacity - 8) = innerRegion := by
      simp only [finishInput, finInput, innerRegion, regionSlice]
    have finKy : finishKey fin = block := by
      change (⟨fin.readReg64 .x1, 64⟩ : Region) = ⟨block.base, 64⟩
      rw [finBlock]
    have finDst : finishMac fin = entryMac s := by simp only [finishMac, finMac, entryMac]
    have finishGrant : FinishResources base fin (capacity - 8) := {
      available := by rw [finSp]; have := g.available; omega
      aligned := finSp.symm ▸ frameAlign
      inputAligned := by
        rw [finInput, BitVec.toNat_add]
        change ((s.readReg64 .x2).toNat + 8) % 2 ^ 64 % 8 = 0
        have := g.scratchAligned
        omega
      outputAligned := finMac.symm ▸ g.macAligned
      inputValid := finIn.symm ▸ regionSlice_valid _ _ _ g.scratchValid (by change _ ≤ capacity; omega)
      keyValid := finKy.symm ▸ blockValid
      macValid := finDst.symm ▸ g.macValid
      imageValid := g.imageValid
      stackInput := fun p h => g.stackScratch p ⟨inFinishStack p (finWork ▸ h.1), insideInner p (finIn ▸ h.2)⟩
      stackKey := by
        rw [finWork, finKy]
        exact regionSlices_disjoint work 0 640 736 64 workValid (by decide) (workFit _ _ (by decide))
      stackMac := fun p h => g.stackMac p ⟨inFinishStack p (finWork ▸ h.1), finDst ▸ h.2⟩
      stackImage := fun p h => g.stackImage p ⟨inFinishStack p (finWork ▸ h.1), h.2⟩
      macInput := fun p h => g.scratchMac p ⟨insideInner p (finIn ▸ h.2), finDst ▸ h.1⟩
      macKey := fun p h => g.stackMac p ⟨inBlock p (finKy ▸ h.2), finDst ▸ h.1⟩
      macImage := fun p h => g.macImage p ⟨finDst ▸ h.1, h.2⟩
      inputRead := by
        intro p h
        apply beforeFinish.grants.read
        have inScratch := insideInner p (finIn ▸ h)
        exact g.scratchRead p inScratch
      keyRead := fun p h => beforeFinish.grants.read _ _ (g.stackRead p (inBlock p (finKy ▸ h)))
      macWrite := fun p h => by rw [beforeFinish.grants.write]; exact g.macWrite p (finDst ▸ h)
      stackRead := fun p h => beforeFinish.grants.read _ _ (g.stackRead p (inFinishStack p (finWork ▸ h)))
      stackWrite := fun p h => by rw [beforeFinish.grants.write]; exact g.stackWrite p (inFinishStack p (finWork ▸ h))
    }
    have changedInScratch (p : Addr) (h : written.Contains p) : scratch.Contains p :=
      regionSlice_inside _ _ _ g.scratchValid (by change _ ≤ capacity; omega) p h
    have prepareKeeps (p : Addr) (out : ¬ written.Contains p) : prepared.mem.cells p = afterKey.mem.cells p := by
      apply prepFrame
      rw [afterKeyScratch]
      exact out
    have finKeyAt (i : Fin 64) : fin.mem.read8 (fin.readReg64 .x1 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec := by
      rw [finBlock]
      have inRegion := caller_region_contains_offset block blockValid i.val i.isLt
      have same := prepareKeeps (block.base + BitVec.ofNat 64 i.val)
        (fun h => g.stackScratch _ ⟨inBlock _ inRegion, changedInScratch _ h⟩)
      change prepared.mem.read8 _ = _
      rw [read8_of_cell _ same, ← keyDst]
      exact keyBytes i
    have finEncoded : EncodedByteList fin.mem (fin.readReg64 .x0) inner := by
      change EncodedByteList prepared.mem _ inner
      rw [finInput]
      rw [afterKeyScratch] at encoded
      exact encoded
    have innerLayout := hmacInner_layout message k0 capacity enough
    have innerBound : inner.size < 2 ^ 64 := by change capacity - 8 < 2 ^ 64; omega
    obtain ⟨afterFin, finishEvents, ranFinish, afterFinSp, afterFinPc, afterFinLive, _, digest, finishFrame, finishOut, finishTrace, finishEq⟩ :=
      finish_execution_from_caller base fin inner k0 (capacity - 8) innerLayout (by rfl) innerBound
        (hmacInner_sha256_length message k0 capacity messageLength) finEncoded finKeyAt finishGrant finishPC
        prepLive (beforeFinish.keeps_code _ loaded.sha) (beforeFinish.keeps_code _ loaded.finish)
    have throughFin := beforeFinish.append ranFinish
    let done := (afterFin.writeReg64 .x0 0#64).setPC (afterFin.pc + 4#64)
    obtain ⟨success, _⟩ := run_range_observes body (afterFinPc.trans finishLink) (by decide)
      (throughFin.keeps_code _ loaded.entry) (by decide +kernel) (entry_set_success afterFin)
      (show done.status = .Running from afterFinLive)
    have throughStatus := throughFin.append success
    have doneSp : done.sp = s.sp - 160#64 := afterFinSp.trans finSp
    have donePC : done.pc = routineAddress base entry + 0x114#64 := by
      change afterFin.pc + 4#64 = _
      rw [afterFinPc, finishLink, BitVec.add_assoc]
      rfl
    have doneSpAligned : done.spAligned = true := by simp [Arm64.State.spAligned, doneSp, mask]
    have keptSpill (i : Fin 96) : done.mem.cells (done.sp + BitVec.ofNat 64 i.val) =
        (frameMem s 160#64).cells (done.sp + BitVec.ofNat 64 i.val) := by
      let p := done.sp + BitVec.ofNat 64 i.val
      have hit : spills.Contains p := by
        have addr : p = spills.base + BitVec.ofNat 64 i.val := by rw [spillsBase, ← doneSp]
        rw [addr]
        exact caller_region_contains_offset spills spillsValid i.val i.isLt
      have apart : ¬ written.Contains p := fun h => g.stackScratch p ⟨inSpill p hit, changedInScratch p h⟩
      have offMac : ¬ (entryMac s).Contains p := fun h => g.stackMac p ⟨inSpill p hit, h⟩
      have offFin : ¬ finishWork.Contains p := by
        rw [spillsEq] at hit
        exact fun h => regionSlices_disjoint work 0 640 640 96 workValid (by decide) (workFit _ _ (by decide)) p ⟨h, hit⟩
      have offKey : ¬ keyWork.Contains p := by
        rw [spillsEq] at hit
        exact fun h => regionSlices_disjoint work 128 512 640 96 workValid (by decide) (workFit _ _ (by decide)) p ⟨h, hit⟩
      have offBlock : ¬ block.Contains p := by
        rw [spillsEq] at hit
        exact fun h => regionSlices_disjoint work 640 96 736 64 workValid (by decide) (workFit _ _ (by decide)) p ⟨hit, h⟩
      change afterFin.mem.cells p = _
      rw [finishFrame p (by rwa [finWork]) (by rwa [finDst]), show fin.mem = prepared.mem from rfl,
        prepareKeeps p apart, keyFrame p (by rwa [keyStack]) (by rwa [keyOut]),
        show keyCall.mem = checked.mem from rfl, front.memory]
    obtain ⟨out, ret, status, sp, link, running, registers, memory⟩ :=
      entry_return base s done (throughStatus.keeps_code _ loaded.entry) donePC afterFinLive doneSp doneSpAligned
        (fun i => by rw [doneSp]; exact throughStatus.grants.read _ _ (stackRead i)) keptSpill
    let trace : EntrySuccessTrace base s keyValue message capacity := {
      keyStart := keyCall
      keyEvents := keyEvents
      keyTrace := keyTrace
      keyPC := keyPC
      keySP := keySp
      keyInput := keyPtr
      keyOutput := keyDst.trans blockBase
      keyLink := keyLink
      innerStart := afterKey
      innerEvents := prepEvents
      innerTrace := prepTrace
      innerPC := afterKeyPc.trans keyLink
      innerSP := afterKeySp.trans keySp
      messageInput := afterKeyMsg
      scratch := afterKeyScratch
      finishStart := fin
      finishOut := finishOut
      finishTrace := finishTrace
      finishPC := finishPC
      finishSP := finSp
      finishInput := finInput
      finishKey := finBlock.trans blockBase
      finishMac := finMac
      finishLink := finishLink }
    have toKeyTrace := entry_key_call_events base checked guardPC
    rw [front.sp] at toKeyTrace
    have toFinishTrace := entry_finish_call_events base prepared prepPC
    have preparedSP : prepared.sp = s.sp - 160#64 := finSp
    rw [preparedSP] at toFinishTrace
    have successTrace := entry_success_events base afterFin (afterFinPc.trans finishLink)
    rw [afterFinSp, finSp] at successTrace
    rw [toKeyTrace] at toKey
    rw [toFinishTrace] at toFin
    rw [successTrace] at success
    rw [finishEq] at ranFinish
    have bodyRun := (((toKey.append deriveKey).append prep).append toFin).append ranFinish
    have successful := (front.execution.append (bodyRun.append success)).append ret
    refine ⟨out, _, successful, ⟨?_, sp, link, running, registers, ?_, ?_, ?_, ?_⟩, .full enough trace⟩
    · rw [hmacSha256_success _ _ _ enough messageLength, status]
      simp [done, Arm64.Reg.x0, HmacResult.status]
    · intro small
      exact False.elim (short small)
    · intro _
      rw [memory, show done.mem = afterFin.mem from rfl, ← finMac, digest,
        hmacFinish_hmacInner]
    · intro _
      rw [memory, show done.mem = afterFin.mem from rfl]
      rw [← (show fin.readReg64 .x0 = s.readReg64 .x2 + 8#64 from finInput)]
      apply finEncoded.preserved innerLayout (show inner.size ≤ capacity - 8 from Nat.le_refl _)
        finishGrant.inputValid
      intro p h
      exact finishFrame p (fun hit => finishGrant.stackInput p ⟨hit, h⟩)
        (fun hit => finishGrant.macInput p ⟨hit, h⟩)
    · intro p offStack offScratch offMac
      rw [memory, show done.mem = afterFin.mem from rfl,
        finishFrame p (fun h => offStack (inFinishStack p (finWork ▸ h))) (by rwa [finDst]),
        show fin.mem = prepared.mem from rfl, prepareKeeps p offScratch]
      exact afterKeyFrame p offStack

end Crypto.HMACSHA256.ARM64
