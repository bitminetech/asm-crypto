import Proofs.HMACSHA256.ARM64EntryExecution
import Proofs.HMACSHA256.ARM64Scheduling

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference Crypto.Baseline

def linkedCode (base p : Addr) : Prop :=
  (callerImage (shaAddress base)).Contains p ∨
    ∃ r : Routine, (r = entry ∨ r = key ∨ r = finish) ∧
      (⟨routineAddress base r, r.image.size⟩ : Region).Contains p

def entryBorrow (base : Addr) (s : Arm64.State) (keyExtent messageExtent capacity : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (entryKeyInput s keyExtent).Contains p ∨ (entryMessage s messageExtent).Contains p
  exclusive p := (entryWorkspace s).Contains p ∨ (entryScratch s capacity).Contains p ∨ (entryMac s).Contains p

def keyBorrow (base : Addr) (s : Arm64.State) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (keyInput s extent).Contains p
  exclusive p := (keyWorkspace s).Contains p ∨ (keyOutput s).Contains p

def finishBorrow (base : Addr) (s : Arm64.State) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (finishInput s extent).Contains p ∨ (finishKey s).Contains p
  exclusive p := (finishWorkspace s).Contains p ∨ (finishMac s).Contains p

structure NativeEnvironment (scope : BorrowScope) (s : Arm64.State) where
  permissions : ScopedPermissions scope s.mem
  schedule : BorrowEnvironment scope (fun _ => True)

structure EntryCall (base : Addr) (s : Arm64.State) (keyValue message : ByteList)
    (keyExtent messageExtent capacity : Nat) : Prop where
  keyLayout : keyValue.WellFormed
  messageLayout : message.WellFormed
  keyAccessible : keyValue.size ≤ keyExtent
  messageAccessible : message.size ≤ messageExtent
  keySize : keyValue.size < 2 ^ 64
  keyLength : keyValue.bytes.size < 2 ^ 61
  messageLength : message.bytes.size < 2 ^ 61 - 64
  keyValueAt : EncodedByteList s.mem (s.readReg64 .x0) keyValue
  messageAt : EncodedByteList s.mem (s.readReg64 .x1) message
  capacityAt : s.mem.read64 (s.readReg64 .x2) = BitVec.ofNat 64 capacity
  capacityMinimum : 8 ≤ capacity
  capacityBound : capacity < 2 ^ 64
  resources : EntryResources base s keyExtent messageExtent capacity
  code : EntryCode base s
  pc : s.pc = routineAddress base entry
  live : s.status = .Running

structure KeyCall (base : Addr) (s : Arm64.State) (input : ByteList) (extent : Nat) : Prop where
  layout : input.WellFormed
  accessible : input.size ≤ extent
  sizeBound : input.size < 2 ^ 64
  lengthBound : input.bytes.size < 2 ^ 61
  typed : EncodedByteList s.mem (s.readReg64 .x0) input
  resources : KeyResources base s extent
  pc : s.pc = routineAddress base key
  live : s.status = .Running
  sha : (program (shaAddress base)).CodeLoaded s.mem
  loaded : (programAt key (routineAddress base key)).CodeLoaded s.mem

structure FinishCall (base : Addr) (s : Arm64.State) (inner : ByteList) (k0 : HmacKeyBlock) (extent : Nat) : Prop where
  layout : inner.WellFormed
  accessible : inner.size ≤ extent
  sizeBound : inner.size < 2 ^ 64
  lengthBound : inner.bytes.size < 2 ^ 61
  typed : EncodedByteList s.mem (s.readReg64 .x0) inner
  keyAt : ∀ i : Fin 64, s.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec
  resources : FinishResources base s extent
  pc : s.pc = routineAddress base finish
  live : s.status = .Running
  sha : (program (shaAddress base)).CodeLoaded s.mem
  loaded : (programAt finish (routineAddress base finish)).CodeLoaded s.mem

structure ProtectedEntryResult (s out : Arm64.State) (keyValue message : ByteList)
    (capacity : Nat) (scope : BorrowScope) : Prop where
  status : out.readReg64 .x0 = BitVec.ofNat 64 (hmacSha256 keyValue message capacity).status
  sp : out.sp = s.sp
  link : out.pc = s.readReg64 .lr
  live : out.status = .Running
  saved : ∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)
  smallFrame : capacity < hmacScratchRequired message →
    ∀ p, scope.protected p → ¬ (entrySaved s).Contains p → out.mem.cells p = s.mem.cells p
  mac : hmacScratchRequired message ≤ capacity →
    memoryBytes32 out.mem (s.readReg64 .x3) = (EthLib.Cryptography.Hash.Hmac.hmac32 keyValue.bytes message.bytes).map UInt8.toBitVec
  scratch : hmacScratchRequired message ≤ capacity →
    EncodedByteList out.mem (s.readReg64 .x2 + 8#64) (hmacInner message (hmacKey keyValue) capacity)
  frame : ∀ p, scope.protected p → ¬ (entryWorkspace s).Contains p →
    ¬ (⟨s.readReg64 .x2 + 8#64, 88 + message.bytes.size⟩ : Region).Contains p →
    ¬ (entryMac s).Contains p → out.mem.cells p = s.mem.cells p

private theorem borrowed_digest {scope : BorrowScope} {a b : Arm64.Memory} {ptr : Addr}
    (cells : SameCellsOn scope.protected a b)
    (protectedBytes : ∀ i < 32, scope.protected (ptr + BitVec.ofNat 64 i)) :
    memoryBytes32 a ptr = memoryBytes32 b ptr := by
  apply Vector.ext
  intro i hi
  simp only [memoryBytes32, Vector.getElem_ofFn, Arm64.Memory.read8, cells _ (protectedBytes i hi)]

theorem entry_execution_concurrent {base : Addr} {s : Arm64.State} {keyValue message : ByteList}
    {keyExtent messageExtent capacity : Nat}
    (caller : EntryCall base s keyValue message keyExtent messageExtent capacity)
    (environment : NativeEnvironment (entryBorrow base s keyExtent messageExtent capacity) s) :
    ∃ out obs, ScheduledExecution base environment.schedule 0 s obs out ∧
      ProtectedEntryResult s out keyValue message capacity (entryBorrow base s keyExtent messageExtent capacity) ∧
      (∀ e ∈ obs, CallAccess (entryBorrow base s keyExtent messageExtent capacity) (observedAccessEvent e)) ∧
      EntryTrace base s keyValue message capacity obs := by
  let scope := entryBorrow base s keyExtent messageExtent capacity
  obtain ⟨out, obs, run, value, trace⟩ := entry_execution_from_caller base s keyValue message keyExtent messageExtent capacity
    caller.keyLayout caller.messageLayout caller.keyAccessible caller.messageAccessible caller.keySize caller.keyLength
    caller.messageLength caller.keyValueAt caller.messageAt caller.capacityAt caller.capacityMinimum caller.capacityBound
    caller.resources caller.code caller.pc caller.live
  have actual := run.native_execution value.live
  obtain ⟨after, scheduled, projected, memory⟩ := actual.scheduled environment.schedule environment.permissions 0 s
    rfl (fun _ _ => rfl)
  have reg (r : Arm64.Reg) : after.readReg64 r = out.readReg64 r :=
    (congrArg (fun t : Arm64.State => t.readReg64 r) projected).symm
  refine ⟨after, obs, scheduled, ⟨(reg _).trans value.status,
    (congrArg Arm64.State.sp projected).symm.trans value.sp,
    (congrArg Arm64.State.pc projected).symm.trans value.link,
    (congrArg Arm64.State.status projected).symm.trans value.live,
    fun i => (reg _).trans (value.saved i), ?_, ?_, ?_, ?_⟩,
    actual.borrowed_accesses environment.permissions, trace⟩
  · intro small p held offSpill
    exact (memory p held).symm.trans (value.smallFrame small p offSpill)
  · intro enough
    have agrees := borrowed_digest (scope := scope) memory (ptr := s.readReg64 .x3) (fun i hi =>
      .inr (.inr (.inr (caller_region_contains_offset (entryMac s) caller.resources.macValid i hi))))
    exact agrees.symm.trans (value.mac enough)
  · intro enough
    have fit : 8 + (capacity - 8) ≤ capacity := by have := caller.capacityMinimum; omega
    have inside : (regionSlice (entryScratch s capacity) 8 (capacity - 8)).Valid :=
      regionSlice_valid _ _ _ caller.resources.scratchValid fit
    apply (value.scratch enough).preserved (hmacInner_layout _ _ _ enough) (extent := capacity - 8) (by rfl) inside
    intro p onScratch
    exact (memory p (.inr (.inr (.inl (regionSlice_inside _ _ _ caller.resources.scratchValid fit p onScratch))))).symm
  · intro p held offStack offScratch offMac
    exact (memory p held).symm.trans (value.frame p offStack offScratch offMac)

theorem key_execution_concurrent {base : Addr} {s : Arm64.State} {input : ByteList} {extent : Nat}
    (caller : KeyCall base s input extent) (environment : NativeEnvironment (keyBorrow base s extent) s) :
    ∃ out obs, ScheduledExecution base environment.schedule 0 s obs out ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec) ∧
      (∀ p, (keyBorrow base s extent).protected p → ¬ (keyWorkspace s).Contains p →
        ¬ (keyOutput s).Contains p → out.mem.cells p = s.mem.cells p) ∧
      (∀ e ∈ obs, CallAccess (keyBorrow base s extent) (observedAccessEvent e)) ∧ KeyWholeTrace base s input obs := by
  obtain ⟨serial, obs, run, sp, link, live, saved, value, frame, trace⟩ := key_execution_from_caller
    base s input extent caller.layout caller.accessible caller.sizeBound caller.lengthBound caller.typed
    caller.resources caller.pc caller.live caller.sha caller.loaded
  have actual := run.native_execution live
  obtain ⟨after, schedule, cpu, cells⟩ := actual.scheduled environment.schedule environment.permissions 0 s
    rfl (fun _ _ => rfl)
  refine ⟨after, obs, schedule, (congrArg Arm64.State.sp cpu).symm.trans sp,
    (congrArg Arm64.State.pc cpu).symm.trans link, (congrArg Arm64.State.status cpu).symm.trans live,
    fun i => ((congrArg (fun t : Arm64.State => t.readReg64 (savedRegister i.val)) cpu).symm).trans (saved i),
    ?_, ?_, actual.borrowed_accesses environment.permissions, trace⟩
  · intro i
    have address := caller_region_contains_offset (keyOutput s) caller.resources.outputValid i.val i.isLt
    have byte : after.mem.cells (s.readReg64 .x1 + BitVec.ofNat 64 i.val) =
        serial.mem.cells (s.readReg64 .x1 + BitVec.ofNat 64 i.val) := (cells _ (.inr (.inr address))).symm
    unfold Arm64.Memory.read8 at value ⊢
    rw [byte]
    exact value i
  · intro p owned offStack offKey
    exact (cells p owned).symm.trans (frame p offStack offKey)

theorem finish_execution_concurrent {base : Addr} {s : Arm64.State} {inner : ByteList} {k0 : HmacKeyBlock}
    {extent : Nat} (caller : FinishCall base s inner k0 extent)
    (environment : NativeEnvironment (finishBorrow base s extent) s) :
    ∃ out obs, ScheduledExecution base environment.schedule 0 s obs out ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
      (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
      memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, (finishBorrow base s extent).protected p → ¬ (finishWorkspace s).Contains p →
        ¬ (finishMac s).Contains p → out.mem.cells p = s.mem.cells p) ∧
      (∀ e ∈ obs, CallAccess (finishBorrow base s extent) (observedAccessEvent e)) ∧
      ∃ bodyOut, ∃ body : FinishBody base (enteredState s 224#64) bodyOut inner k0,
        obs = body.nativeTrace := by
  obtain ⟨serial, obs, run, sp, link, live, saved, value, frame, trace⟩ := finish_execution_from_caller
    base s inner k0 extent caller.layout caller.accessible caller.sizeBound caller.lengthBound caller.typed
    caller.keyAt caller.resources caller.pc caller.live caller.sha caller.loaded
  have actual := run.native_execution live
  obtain ⟨after, schedule, cpu, cells⟩ := actual.scheduled environment.schedule environment.permissions 0 s
    rfl (fun _ _ => rfl)
  refine ⟨after, obs, schedule, (congrArg Arm64.State.sp cpu).symm.trans sp,
    (congrArg Arm64.State.pc cpu).symm.trans link, (congrArg Arm64.State.status cpu).symm.trans live,
    fun i => ((congrArg (fun t : Arm64.State => t.readReg64 (savedRegister i.val)) cpu).symm).trans (saved i),
    ?_, ?_, actual.borrowed_accesses environment.permissions, trace⟩
  · have agrees := borrowed_digest cells (ptr := s.readReg64 .x2) (fun i hi =>
      .inr (.inr (caller_region_contains_offset (finishMac s) caller.resources.macValid i hi)))
    exact agrees.symm.trans value
  · intro p owned offStack offMac
    exact (cells p owned).symm.trans (frame p offStack offMac)

end Crypto.HMACSHA256.ARM64
