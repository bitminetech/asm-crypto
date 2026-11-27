import Proofs.HMACSHA256.RISCV64Entry
import Proofs.HMACSHA256.RISCV64Inner
import Proofs.HMACSHA256.RISCV64KeyResources
import Proofs.HMACSHA256.RISCV64FinishResources

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported
  (caller_region_contains_offset caller_region_read caller_region_write caller_outside_delta
    memoryBytes32)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

def entryWorkspace (s : CPU) : Region := stackRegion (s.reg 2#5) 896
def entryKeyInput (s : CPU) (extent : Nat) : Region := ⟨s.reg 10#5, extent⟩
def entryMessageInput (s : CPU) (extent : Nat) : Region := ⟨s.reg 11#5, extent⟩
def entryScratch (s : CPU) (capacity : Nat) : Region := ⟨s.reg 12#5, capacity⟩
def entryScratchWritten (s : CPU) (innerCount : Nat) : Region :=
  ⟨s.reg 12#5 + 8#64, 24 + innerCount⟩

theorem entry_scratch_written_slice (s : CPU) (capacity n : Nat) :
    entryScratchWritten s (64 + n) = regionSlice (entryScratch s capacity) 8 (88 + n) := by
  unfold entryScratchWritten regionSlice entryScratch
  congr 1
  omega

def entryMac (s : CPU) : Region := ⟨s.reg 13#5, 32⟩

structure EntryResources (base : Addr) (s : CPU) (keyExtent messageExtent capacity : Nat) : Prop where
  stackAvailable : 896 ≤ (s.reg 2#5).toNat
  stackAligned : (s.reg 2#5).toNat % 16 = 0
  keyAligned : (s.reg 10#5).toNat % 8 = 0
  messageAligned : (s.reg 11#5).toNat % 8 = 0
  scratchAligned : (s.reg 12#5).toNat % 8 = 0
  macAligned : (s.reg 13#5).toNat % 8 = 0
  keyValid : (entryKeyInput s keyExtent).Valid
  messageValid : (entryMessageInput s messageExtent).Valid
  scratchValid : (entryScratch s capacity).Valid
  macValid : (entryMac s).Valid
  stackKey : (entryWorkspace s).Disjoint (entryKeyInput s keyExtent)
  stackMessage : (entryWorkspace s).Disjoint (entryMessageInput s messageExtent)
  stackScratch : (entryWorkspace s).Disjoint (entryScratch s capacity)
  stackMac : (entryWorkspace s).Disjoint (entryMac s)
  stackSha : (entryWorkspace s).Disjoint (callerImage (shaAddress base))
  scratchKey : (entryScratch s capacity).Disjoint (entryKeyInput s keyExtent)
  scratchMessage : (entryScratch s capacity).Disjoint (entryMessageInput s messageExtent)
  scratchMac : (entryScratch s capacity).Disjoint (entryMac s)
  macKey : (entryMac s).Disjoint (entryKeyInput s keyExtent)
  macMessage : (entryMac s).Disjoint (entryMessageInput s messageExtent)
  macSha : (entryMac s).Disjoint (callerImage (shaAddress base))
  keyRead : ∀ p, (entryKeyInput s keyExtent).Contains p → s.mem.canRead p 1 = true
  messageRead : ∀ p, (entryMessageInput s messageExtent).Contains p → s.mem.canRead p 1 = true
  scratchRead : ∀ p, (entryScratch s capacity).Contains p → s.mem.canRead p 1 = true
  scratchWrite : ∀ p, (entryScratch s capacity).Contains p → s.mem.canWrite p 1 = true
  macWrite : ∀ p, (entryMac s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (entryWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (entryWorkspace s).Contains p → s.mem.canWrite p 1 = true

structure RoutineGrant (base : Addr) (routine : Routine) (m : Memory) : Prop where
  loaded : routine.Loaded (routineAddress base routine) m.read8
  aligned : (routineAddress base routine).toNat % 2 = 0
  executable : m.canExec (routineAddress base routine) routine.image.size = true

theorem RoutineGrant.preserved {base : Addr} {routine : Routine} {s out : CPU} {events}
    (grant : RoutineGrant base routine s.mem) (run : ProgramExecution base s events out) :
    RoutineGrant base routine out.mem :=
  ⟨(run.keeps_routine grant.loaded (routine_readonly_of_exec grant.executable)).1,
    grant.aligned, (allPerm_eq_of_perm run.perm _ _ _).trans grant.executable⟩

theorem ShaCode.preserved_by_execution {base codeBase : Addr} {s out : CPU} {events}
    (code : ShaCode codeBase s.mem) (run : ProgramExecution base s events out) :
    ShaCode codeBase out.mem := by
  refine code.preserved (fun p inside => ?_) run.perm (fun p n => (run.permissions p n).2)
  have lo : codeBase.toNat ≤ p.toNat := inside.1
  have hi : p.toNat < codeBase.toNat + Crypto.RISCV64.image.size := inside.2
  let i := p.toNat - codeBase.toNat
  have equal : codeBase + BitVec.ofNat 64 i = p := by
    have bounded := p.isLt
    apply BitVec.eq_of_toNat_eq
    dsimp only [i]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p.toNat - codeBase.toNat < 2 ^ 64),
      Nat.add_sub_of_le lo, Nat.mod_eq_of_lt bounded]
  rw [← equal]
  exact run.protected _ (code.readonly i (by dsimp [i]; omega))

/-- The stack below the two local calls is wholly contained in the entry's
allocation. K0 occupies its first 64 bytes above the nested workspace. -/
def entryFrame (s : CPU) : Region := regionSlice (entryWorkspace s) 720 176
def entryKeyBlock (s : CPU) : Region := regionSlice (entryWorkspace s) 720 64
def entrySpills (s : CPU) : Region := regionSlice (entryWorkspace s) 784 104
def entryKeyStack (s : CPU) : Region := regionSlice (entryWorkspace s) 128 592
def entryFinishStack (s : CPU) : Region := regionSlice (entryWorkspace s) 0 720
def entryInner (s : CPU) (capacity : Nat) : Region :=
  regionSlice (entryScratch s capacity) 8 (capacity - 8)

theorem entryFrame_base (s : CPU) : (entryFrame s).base = s.reg 2#5 - 176#64 :=
  congrArg Region.base (stackRegion_slice _ 896 720 176 (by decide))

theorem entryKeyBlock_base (s : CPU) : (entryKeyBlock s).base = s.reg 2#5 - 176#64 :=
  congrArg Region.base (stackRegion_slice _ 896 720 64 (by decide))

theorem entrySpills_base (s : CPU) :
    (entrySpills s).base = s.reg 2#5 - 176#64 + 64#64 := by
  have base := entryFrame_base s
  change (s.reg 2#5 - 896#64 + 784#64) = _
  change (s.reg 2#5 - 896#64 + 720#64) = _ at base
  rw [← base, BitVec.add_assoc]
  rfl

theorem entryKeyStack_same (s called : CPU) (sp : called.reg 2#5 = s.reg 2#5 - 176#64) :
    keyWorkspace called = entryKeyStack s := by
  have address : s.reg 2#5 - 176#64 - 592#64 = s.reg 2#5 - 768#64 := by
    rw [BitVec.sub_sub]
    rfl
  change (⟨called.reg 2#5 - 592#64, 592⟩ : Region) = _
  rw [sp, address]
  exact (stackRegion_slice _ 896 128 592 (by decide)).symm

theorem entryFinishStack_same (s called : CPU) (sp : called.reg 2#5 = s.reg 2#5 - 176#64) :
    finishWorkspace (called.put 2#5 (called.reg 2#5 - 240#64)) = entryFinishStack s := by
  have address : s.reg 2#5 - 176#64 - 240#64 - 480#64 = s.reg 2#5 - 896#64 := by
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl
  unfold finishWorkspace
  simp (config := { decide := true }) only [reg_put, if_true, if_false, sp]
  change (⟨s.reg 2#5 - 176#64 - 240#64 - 480#64, 720⟩ : Region) = _
  rw [address]
  exact (stackRegion_slice _ 896 0 720 (by decide)).symm

theorem EntryResources.key_call {base : Addr} {s called : CPU} {keyExtent messageExtent capacity : Nat}
    {events} (g : EntryResources base s keyExtent messageExtent capacity)
    (run : ProgramExecution base s events called)
    (input : called.reg 10#5 = s.reg 10#5)
    (output : called.reg 11#5 = s.reg 2#5 - 176#64)
    (sp : called.reg 2#5 = s.reg 2#5 - 176#64) :
    KeyResources base called keyExtent := by
  let whole := entryWorkspace s
  have valid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have nested := entryKeyStack_same s called sp
  have inputRegion : keyInputRegion called keyExtent = entryKeyInput s keyExtent := by
    simp only [keyInputRegion, entryKeyInput, input]
  have outputRegion : keyBlockRegion called = entryKeyBlock s := by
    change (⟨called.reg 11#5, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [output, entryKeyBlock_base]
  have inStack (p : Addr) (h : (keyWorkspace called).Contains p) : whole.Contains p := by
    rw [nested] at h
    exact regionSlice_inside whole 128 592 valid (by change 128 + 592 ≤ 896; decide) p h
  have inK0 (p : Addr) (h : (keyBlockRegion called).Contains p) : whole.Contains p := by
    rw [outputRegion] at h
    exact regionSlice_inside whole 720 64 valid (by change 720 + 64 ≤ 896; decide) p h
  have frameAlign : (s.reg 2#5 - 176#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 176 g.stackAligned (by decide) (by have := g.stackAvailable; omega)
  exact {
    available := by
      rw [sp]
      have height := frame_base_end (s.reg 2#5) 176 (by have := g.stackAvailable; omega)
      have full := g.stackAvailable
      change 592 ≤ (s.reg 2#5 - BitVec.ofNat 64 176).toNat
      omega
    aligned := sp.symm ▸ frameAlign
    inputAligned := input.symm ▸ g.keyAligned
    blockAligned := by rw [output]; omega
    inputValid := inputRegion.symm ▸ g.keyValid
    blockValid := by
      rw [outputRegion]
      exact regionSlice_valid whole 720 64 valid (by change 720 + 64 ≤ 896; decide)
    blockInput := fun p h => g.stackKey p ⟨inK0 p h.1, inputRegion ▸ h.2⟩
    stackInput := fun p h => g.stackKey p ⟨inStack p h.1, inputRegion ▸ h.2⟩
    stackBlock := by
      rw [nested, outputRegion]
      exact regionSlices_disjoint whole 128 592 720 64 valid (by decide)
        (by change 720 + 64 ≤ 896; decide)
    stackImage := fun p h => g.stackSha p ⟨inStack p h.1, h.2⟩
    blockImage := fun p h => g.stackSha p ⟨inK0 p h.1, h.2⟩
    inputRead := fun p h => (run.permissions p 1).2 (g.keyRead p (inputRegion ▸ h))
    blockWrite := fun p h => ((run.permissions p 1).1).trans (g.stackWrite p (inK0 p h))
    stackRead := fun p h => (run.permissions p 1).2 (g.stackRead p (inStack p h))
    stackWrite := fun p h => ((run.permissions p 1).1).trans (g.stackWrite p (inStack p h))
  }

set_option maxHeartbeats 1800000 in
theorem EntryResources.finish_call {base : Addr} {s called : CPU} {keyExtent messageExtent capacity : Nat}
    {events} (g : EntryResources base s keyExtent messageExtent capacity)
    (run : ProgramExecution base s events called)
    (input : called.reg 10#5 = s.reg 12#5 + 8#64)
    (keyAt : called.reg 11#5 = s.reg 2#5 - 176#64)
    (output : called.reg 12#5 = s.reg 13#5)
    (sp : called.reg 2#5 = s.reg 2#5 - 176#64)
    (capacityMin : 8 ≤ capacity) :
    FinishResources base (called.put 2#5 (called.reg 2#5 - 240#64)) (capacity - 8) := by
  let whole := entryWorkspace s
  let inner := entryInner s capacity
  let before := called.put 2#5 (called.reg 2#5 - 240#64)
  have valid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have stack := entryFinishStack_same s called sp
  have innerRegion : finishInput before (capacity - 8) = inner := by
    simp (config := { decide := true }) only [before, finishInput, reg_put, if_false, input,
      inner, entryInner, regionSlice, entryScratch]
  have keyRegion : finishKey before = entryKeyBlock s := by
    simp (config := { decide := true }) only [before, finishKey, reg_put, if_false, keyAt]
    change (⟨s.reg 2#5 - 176#64, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [entryKeyBlock_base]
  have macRegion : finishOutput before = entryMac s := by
    simp (config := { decide := true }) only [before, finishOutput, entryMac, reg_put, if_false, output]
  have stackInside (p : Addr) (h : (finishWorkspace before).Contains p) : whole.Contains p := by
    rw [stack] at h
    exact regionSlice_inside whole 0 720 valid (by change 0 + 720 ≤ 896; decide) p h
  have innerInside (p : Addr) (h : (finishInput before (capacity - 8)).Contains p) :
      (entryScratch s capacity).Contains p := by
    rw [innerRegion] at h
    exact regionSlice_inside _ _ _ g.scratchValid
      (by change 8 + (capacity - 8) ≤ capacity; omega) p h
  have spFrame : before.reg 2#5 = s.reg 2#5 - 416#64 := by
    simp (config := { decide := true }) only [before, reg_put, if_true, if_false, sp, BitVec.sub_sub]
    rfl
  have aligned : (before.reg 2#5).toNat % 16 = 0 := by
    rw [spFrame]
    exact stackRegion_aligned _ 416 g.stackAligned (by decide) (by have := g.stackAvailable; omega)
  have available : 480 ≤ (before.reg 2#5).toNat := by
    rw [spFrame]
    have height := frame_base_end (s.reg 2#5) 416 (by have := g.stackAvailable; omega)
    have total := g.stackAvailable
    change 480 ≤ (s.reg 2#5 - BitVec.ofNat 64 416).toNat
    omega
  have inputAlign : ((s.reg 12#5 + 8#64).toNat % 8) = 0 := by
    rw [BitVec.toNat_add]
    change (((s.reg 12#5).toNat + 8) % 2 ^ 64) % 8 = 0
    have := g.scratchAligned
    omega
  exact {
    available := available
    aligned := aligned
    inputAligned := by
      simpa (config := { decide := true }) only [before, reg_put, if_false, input] using inputAlign
    outputAligned := by
      simpa (config := { decide := true }) only [before, reg_put, if_false, output] using g.macAligned
    stackValid := by
      rw [stack]
      exact regionSlice_valid whole 0 720 valid (by change 0 + 720 ≤ 896; decide)
    inputValid := by
      rw [innerRegion]
      exact regionSlice_valid _ _ _ g.scratchValid (by change 8 + (capacity - 8) ≤ capacity; omega)
    keyValid := by
      rw [keyRegion]
      exact regionSlice_valid whole 720 64 valid (by change 720 + 64 ≤ 896; decide)
    outputValid := macRegion.symm ▸ g.macValid
    stackInput := fun p h => g.stackScratch p ⟨stackInside p h.1, innerInside p h.2⟩
    stackKey := by
      rw [stack, keyRegion]
      exact regionSlices_disjoint whole 0 720 720 64 valid (by decide)
        (by change 720 + 64 ≤ 896; decide)
    stackOutput := fun p h => g.stackMac p ⟨stackInside p h.1, macRegion ▸ h.2⟩
    stackCode := fun p h => g.stackSha p ⟨stackInside p h.1, h.2⟩
    outputCode := fun p h => g.macSha p ⟨macRegion ▸ h.1, h.2⟩
    outputInput := fun p h => g.scratchMac p ⟨innerInside p h.2, macRegion ▸ h.1⟩
    inputRead := fun p h => (run.permissions p 1).2 (g.scratchRead p (innerInside p h))
    stackRead := fun p h => (run.permissions p 1).2 (g.stackRead p (stackInside p h))
    stackWrite := fun p h => ((run.permissions p 1).1).trans (g.stackWrite p (stackInside p h))
    outputWrite := fun p h => ((run.permissions p 1).1).trans (g.macWrite p (macRegion ▸ h))
  }

theorem EntryResources.frame_grants {base : Addr} {s : CPU} {keyExtent messageExtent capacity : Nat}
    (g : EntryResources base s keyExtent messageExtent capacity) :
    (s.reg 2#5 - 176#64).toNat % 8 = 0 ∧
      s.mem.canRead (s.reg 2#5 - 176#64) 176 = true ∧
      s.mem.canWrite (s.reg 2#5 - 176#64) 176 = true := by
  let whole := entryWorkspace s
  have valid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have aligned : (s.reg 2#5 - 176#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 176 g.stackAligned (by decide) (by have := g.stackAvailable; omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [← entryFrame_base]
    exact caller_region_read s.mem whole valid g.stackRead 720 176 (by change 720 + 176 ≤ 896; decide)
  · rw [← entryFrame_base]
    exact caller_region_write s.mem whole valid g.stackWrite 720 176 (by change 720 + 176 ≤ 896; decide)

theorem EntryResources.capacity_grants {base : Addr} {s : CPU} {keyExtent messageExtent capacity : Nat}
    (g : EntryResources base s keyExtent messageExtent capacity)
    (capacityMin : 8 ≤ capacity) (header : 24 ≤ messageExtent) :
    (Access.read (s.reg 12#5) .double).permitted s.mem = true ∧
      (Access.read (s.reg 11#5 + 16#64) .double).permitted s.mem = true := by
  have size : s.mem.canRead (s.reg 12#5) 8 = true := by
    have allowed := caller_region_read s.mem _ g.scratchValid g.scratchRead 0 8 (by
      change 0 + 8 ≤ capacity
      omega)
    change s.mem.canRead (s.reg 12#5 + 0#64) 8 = true at allowed
    rwa [BitVec.add_zero] at allowed
  have count : s.mem.canRead (s.reg 11#5 + 16#64) 8 = true :=
    caller_region_read s.mem _ g.messageValid g.messageRead 16 8 header
  constructor
  · simp only [Access.permitted, Width.bytes, g.scratchAligned, beq_self_eq_true, size, Bool.true_and]
  · simp only [Access.permitted, Width.bytes, count, Bool.and_true, beq_iff_eq, BitVec.toNat_add]
    change (((s.reg 11#5).toNat + 16) % 2 ^ 64) % 8 = 0
    have := g.messageAligned
    omega

def EntryPreparationTrace (base : Addr) (s : CPU) (keyValue message : ByteList) (capacity : Nat)
    (events : List (List Access)) : Prop :=
  ∃ (called followingKey : CPU) (keyEvents : List (List Access)),
    called.pc = routineAddress base key ∧
    called.reg 2#5 = s.reg 2#5 - 176#64 ∧ called.reg 10#5 = s.reg 10#5 ∧
    called.reg 11#5 = s.reg 2#5 - 176#64 ∧ KeyTrace base called keyValue keyEvents ∧
    followingKey.reg 2#5 = s.reg 2#5 - 176#64 ∧ followingKey.reg 18#5 = s.reg 11#5 ∧
    followingKey.reg 19#5 = s.reg 12#5 ∧
    events = entryBeforeKeyEvents base s (BitVec.ofNat 64 capacity) ++ keyEvents ++
      entryInnerEvents base followingKey message

def entryFinishSetupEvents (base : Addr) : List (List Access) :=
  let pc := routineAddress base entry + 0x104#64
  [[.fetch pc 4], [.fetch (pc + 4#64) 2], [.fetch (pc + 6#64) 2], [.fetch (pc + 8#64) 4]]

def EntrySuccessTrace (base : Addr) (s : CPU) (keyValue message : ByteList) (capacity : Nat)
    (events : List (List Access)) : Prop :=
  ∃ (finishState : CPU) (prepared finishEvents : List (List Access)),
    EntryPreparationTrace base s keyValue message capacity prepared ∧
    finishState.pc = routineAddress base finish ∧
    finishState.reg 2#5 = s.reg 2#5 - 176#64 ∧ finishState.reg 10#5 = s.reg 12#5 + 8#64 ∧
    finishState.reg 11#5 = s.reg 2#5 - 176#64 ∧ finishState.reg 12#5 = s.reg 13#5 ∧
    FinishTrace base finishState (hmacInner message (hmacKey keyValue) capacity) (hmacKey keyValue) finishEvents ∧
    events = prepared ++ entryFinishSetupEvents base ++ finishEvents ++ entrySuccessReturnEvents base s

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- On the successful guard branch, execute the real key helper and build the
inner list. The two input lists, scratch and MAC retain their caller-owned
addresses. The saved register slots remain ready for the final return. -/
theorem EntryResources.prepare_inner {base : Addr} {s : CPU} {keyExtent messageExtent capacity : Nat}
    (g : EntryResources base s keyExtent messageExtent capacity)
    (keyValue message : ByteList) (keyLayout : keyValue.WellFormed) (messageLayout : message.WellFormed)
    (keyFits : keyValue.size ≤ keyExtent) (messageFits : message.size ≤ messageExtent)
    (keySize : keyValue.size < 2 ^ 64) (keyLength : keyValue.bytes.size < 2 ^ 61)
    (keyEncoded : EncodedByteList s.mem (s.reg 10#5) keyValue)
    (messageEncoded : EncodedByteList s.mem (s.reg 11#5) message)
    (capacityAt : s.mem.read64 (s.reg 12#5) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (capacitySize : capacity < 2 ^ 64)
    (pc : s.pc = routineAddress base entry)
    (entryCode : RoutineGrant base entry s.mem) (keyCode : RoutineGrant base key s.mem)
    (sha : ShaCode (shaAddress base) s.mem) :
    ∃ prepared events, ProgramExecution base s events prepared ∧
      events.length ≤ 75 + keyStepBound keyValue.bytes.size +
        8 * (message.bytes.size / 8) + 7 * (message.bytes.size % 8) ∧
      prepared.pc = routineAddress base entry + 0x104#64 ∧ prepared.reg 2#5 = s.reg 2#5 - 176#64 ∧
      prepared.reg 19#5 = s.reg 12#5 ∧ prepared.reg 20#5 = s.reg 13#5 ∧
      EncodedByteList prepared.mem (s.reg 12#5 + 8#64) (hmacInner message (hmacKey keyValue) capacity) ∧
      (∀ i : Fin 64, prepared.mem.read8 (prepared.reg 2#5 + BitVec.ofNat 64 i.val) =
        (hmacKey keyValue)[i.val].toBitVec) ∧
      (∀ i : Fin 104, let p := prepared.reg 2#5 + BitVec.ofNat 64 (64 + i.val)
        prepared.mem.cells p = (enteredFrame .entry s).mem.cells p) ∧
      (∀ p, ¬ (entryWorkspace s).Contains p → ¬ (entryScratchWritten s (64 + message.bytes.size)).Contains p →
        prepared.mem.cells p = s.mem.cells p) ∧ EntryPreparationTrace base s keyValue message capacity events := by
  let whole := entryWorkspace s
  let scratch := entryScratch s capacity
  let msgRegion := entryMessageInput s messageExtent
  let spill := entrySpills s
  let k0Region := entryKeyBlock s
  have valid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have spillFits : 784 + 104 ≤ whole.bytes := by change 784 + 104 ≤ 896; decide
  have spillValid : spill.Valid := regionSlice_valid _ _ _ valid spillFits
  have k0Fits : 720 + 64 ≤ whole.bytes := by change 720 + 64 ≤ 896; decide
  have k0Valid : k0Region.Valid := regionSlice_valid _ _ _ valid k0Fits
  have inWholeSpills (p : Addr) (hit : spill.Contains p) : whole.Contains p :=
    regionSlice_inside _ _ _ valid spillFits p hit
  have inWholeK0 (p : Addr) (hit : k0Region.Contains p) : whole.Contains p :=
    regionSlice_inside _ _ _ valid k0Fits p hit
  obtain ⟨stackAlignment, _, stackWrite⟩ := g.frame_grants
  have msgRead : s.mem.canRead (s.reg 11#5) messageExtent = true := by
    have h := caller_region_read s.mem msgRegion g.messageValid g.messageRead 0 messageExtent (by
      change 0 + messageExtent ≤ messageExtent
      omega)
    change s.mem.canRead (s.reg 11#5 + 0#64) messageExtent = true at h
    rwa [BitVec.add_zero] at h
  have scratchRead : s.mem.canRead (s.reg 12#5) capacity = true := by
    have h := caller_region_read s.mem scratch g.scratchValid g.scratchRead 0 capacity (by
      change 0 + capacity ≤ capacity
      omega)
    change s.mem.canRead (s.reg 12#5 + 0#64) capacity = true at h
    rwa [BitVec.add_zero] at h
  have scratchWrite : s.mem.canWrite (s.reg 12#5) capacity = true := by
    have h := caller_region_write s.mem scratch g.scratchValid g.scratchWrite 0 capacity (by
      change 0 + capacity ≤ capacity
      omega)
    change s.mem.canWrite (s.reg 12#5 + 0#64) capacity = true at h
    rwa [BitVec.add_zero] at h
  have msgHeader : 24 ≤ messageExtent := by
    have := messageLayout.1
    have := messageLayout.2.2.1
    omega
  obtain ⟨capacityRead, countRead⟩ := g.capacity_grants (by omega) msgHeader
  have savedOutside (p : Addr) (outside : ¬ spill.Contains p) :
      104 ≤ (p - (s.reg 2#5 - 176#64 + 64#64)).toNat := by
    have h := caller_outside_delta spill spillValid p outside
    change 104 ≤ (p - (entrySpills s).base).toNat at h
    rwa [entrySpills_base] at h
  have notSpill (p : Addr) (whereAt : p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64) (i : Fin 8) :
      104 ≤ (p + BitVec.ofNat 64 i.val - (s.reg 2#5 - 176#64 + 64#64)).toNat := by
    apply savedOutside
    intro hit
    have within := inWholeSpills _ hit
    rcases whereAt with rfl | rfl
    · exact g.stackScratch _ ⟨within, caller_region_contains_offset scratch g.scratchValid i.val (by
        have := i.isLt
        change i.val < capacity
        omega)⟩
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add] at within
      exact g.stackMessage _ ⟨within, caller_region_contains_offset msgRegion g.messageValid (16 + i.val) (by
        have := i.isLt
        change 16 + i.val < messageExtent
        omega)⟩
  have lenFits : message.bytes.size < 2 ^ 64 := by omega
  obtain ⟨called, beforeKey, prefixLen, keyPC, keyLink, keyInput, keyOutput, keySP, keyMem,
    oldMessage, oldScratch, oldMac⟩ := entry_before_key_fetched base s
    (BitVec.ofNat 64 capacity) (BitVec.ofNat 64 message.bytes.size) pc entryCode.loaded entryCode.aligned
    entryCode.executable stackAlignment stackWrite capacityRead countRead capacityAt messageEncoded.count
    notSpill (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacitySize, Nat.mod_eq_of_lt lenFits] using room)
  have calledKey : EncodedByteList called.mem (called.reg 10#5) keyValue := by
    rw [keyInput]
    apply keyEncoded.preserved keyLayout keyFits g.keyValid
    intro p inside
    rw [keyMem]
    exact enteredFrame_outside .entry s p
      (savedOutside p (fun hit => g.stackKey p ⟨inWholeSpills p hit, inside⟩))
  have keyLinkEven : (called.reg 1#5).toNat % 2 = 0 := by
    rw [keyLink, BitVec.toNat_add]
    change (((routineAddress base entry).toNat + 70) % 2 ^ 64) % 2 = 0
    have := entryCode.aligned
    omega
  have keyGrant := keyCode.preserved beforeKey
  obtain ⟨returnsKey, keyEvents, executeKey, keySteps, keyReturn, keyStack, regs, block, keyKeeps, keyTrace⟩ :=
    key_execution_from_caller base called keyValue keyExtent keyPC keyLayout keyFits keySize keyLength
      calledKey (g.key_call beforeKey keyInput keyOutput keySP) (sha.preserved_by_execution beforeKey)
      keyGrant.loaded keyGrant.aligned keyGrant.executable keyLinkEven
  have pathKey := beforeKey.append executeKey
  have afterSP := keyStack.trans keySP
  have afterMsg : returnsKey.reg 18#5 = s.reg 11#5 := (regs ⟨3, by decide⟩).trans oldMessage
  have afterScratch : returnsKey.reg 19#5 = s.reg 12#5 := (regs ⟨4, by decide⟩).trans oldScratch
  have afterMac : returnsKey.reg 20#5 = s.reg 13#5 := (regs ⟨5, by decide⟩).trans oldMac
  have keyStackRegion := entryKeyStack_same s called keySP
  have keyBlockRegionEq : keyBlockRegion called = k0Region := by
    change (⟨called.reg 11#5, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [keyOutput, entryKeyBlock_base]
  have inNestedStack (p : Addr) (hit : (keyWorkspace called).Contains p) : whole.Contains p := by
    rw [keyStackRegion] at hit
    exact regionSlice_inside whole 128 592 valid (by change 128 + 592 ≤ 896; decide) p hit
  have keyOutside (p : Addr) (outside : ¬ whole.Contains p) :
      returnsKey.mem.cells p = s.mem.cells p := by
    rw [keyKeeps p (fun hit => outside (inNestedStack p hit))
      (fun hit => outside (inWholeK0 p (keyBlockRegionEq ▸ hit))), keyMem]
    exact enteredFrame_outside .entry s p (savedOutside p (fun hit => outside (inWholeSpills p hit)))
  have keySaves (p : Addr) (inside : spill.Contains p) :
      returnsKey.mem.cells p = (enteredFrame .entry s).mem.cells p := by
    rw [← keyMem]
    apply keyKeeps
    · rw [keyStackRegion]
      intro hit
      exact regionSlices_disjoint whole 128 592 784 104 valid (by decide) spillFits _ ⟨hit, inside⟩
    · rw [keyBlockRegionEq]
      intro hit
      exact regionSlices_disjoint whole 720 64 784 104 valid (by decide) spillFits _ ⟨hit, inside⟩
  have afterMsgEncoded : EncodedByteList returnsKey.mem (returnsKey.reg 18#5) message := by
    rw [afterMsg]
    exact messageEncoded.preserved messageLayout messageFits g.messageValid
      (fun p inside => keyOutside p (fun hit => g.stackMessage p ⟨hit, inside⟩))
  have afterCapacity : returnsKey.mem.read64 (returnsKey.reg 19#5) = BitVec.ofNat 64 capacity := by
    rw [afterScratch, ← capacityAt]
    apply read64_eq_of_cells
    intro i
    apply keyOutside
    intro hit
    exact g.stackScratch _ ⟨hit, caller_region_contains_offset scratch g.scratchValid i.val (by
      change i.val < capacity
      have := i.isLt
      omega)⟩
  have k0At (i : Fin 64) : returnsKey.mem.read8 (returnsKey.reg 2#5 + BitVec.ofNat 64 i.val) =
      (hmacKey keyValue)[i.val].toBitVec := by
    rw [afterSP, ← keyOutput]
    exact block i
  have k0RegionAfter : (⟨returnsKey.reg 2#5, 64⟩ : Region) = k0Region := by
    change (⟨returnsKey.reg 2#5, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [afterSP, entryKeyBlock_base]
  have k0Read : returnsKey.mem.canRead (returnsKey.reg 2#5) 64 = true := by
    rw [afterSP, ← entryKeyBlock_base]
    exact (pathKey.permissions _ _).2
      (caller_region_read s.mem whole valid g.stackRead 720 64 k0Fits)
  have entryNext := entryCode.preserved pathKey
  obtain ⟨prepared, executeInner, innerSteps, innerPC, innerStack, innerScratch, innerMac,
    encoded, keepsScratch⟩ :=
    entry_inner_list_fetched base returnsKey message (hmacKey keyValue) capacity messageExtent
      (keyReturn.trans keyLink) entryNext.loaded entryNext.aligned entryNext.executable
      messageLayout messageFits afterMsgEncoded afterCapacity room capacitySize
      (afterScratch.symm ▸ g.scratchValid) (afterMsg.symm ▸ g.messageValid)
      (k0RegionAfter.symm ▸ k0Valid)
      (by rw [afterScratch, afterMsg]; exact g.scratchMessage)
      (by rw [afterScratch, k0RegionAfter]; exact fun p h => g.stackScratch p ⟨inWholeK0 p h.2, h.1⟩)
      k0At (afterScratch.symm ▸ g.scratchAligned) (afterMsg.symm ▸ g.messageAligned)
      (afterSP.symm ▸ stackAlignment)
      (by rw [afterScratch]; exact (pathKey.permissions _ _).2 scratchRead)
      (by rw [afterScratch]; exact (pathKey.permissions _ _).1.trans scratchWrite)
      (by rw [afterMsg]; exact (pathKey.permissions _ _).2 msgRead) k0Read
  have cut (p : Addr) :
      (regionSlice ⟨returnsKey.reg 19#5, capacity⟩ 8 (88 + message.bytes.size)).Contains p →
        (entryScratch s capacity).Contains p := by
    rw [afterScratch]
    exact regionSlice_inside (entryScratch s capacity) 8 _ g.scratchValid (by change _ ≤ capacity; omega) p
  refine ⟨prepared, _, pathKey.append executeInner, ?_, innerPC, innerStack.trans afterSP,
    innerScratch.trans afterScratch, innerMac.trans afterMac, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · rw [← afterScratch]
    exact encoded
  · intro i
    rw [innerStack]
    unfold Arm64.Memory.read8
    rw [keepsScratch _ (by
      intro hit
      have actual := cut _ hit
      have within := caller_region_contains_offset k0Region k0Valid i.val i.isLt
      change (entryKeyBlock s).Contains ((entryKeyBlock s).base + BitVec.ofNat 64 i.val) at within
      rw [afterSP, ← entryKeyBlock_base s] at actual
      exact g.stackScratch _ ⟨inWholeK0 _ within, actual⟩)]
    exact k0At i
  · intro i
    dsimp only
    rw [innerStack, afterSP]
    let p := s.reg 2#5 - 176#64 + BitVec.ofNat 64 (64 + i.val)
    have inside : spill.Contains p := by
      have here := caller_region_contains_offset spill spillValid i.val i.isLt
      change spill.Contains ((entrySpills s).base + BitVec.ofNat 64 i.val) at here
      rw [entrySpills_base] at here
      simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using here
    have away : ¬ (regionSlice ⟨returnsKey.reg 19#5, capacity⟩ 8 (88 + message.bytes.size)).Contains p :=
      fun hit => g.stackScratch p ⟨inWholeSpills p inside, cut p hit⟩
    exact (keepsScratch p away).trans (keySaves p inside)
  · intro p outsideStack outsideScratch
    have across : (regionSlice ⟨returnsKey.reg 19#5, capacity⟩ 8 (88 + message.bytes.size)) =
        entryScratchWritten s (64 + message.bytes.size) := by
      rw [afterScratch, entry_scratch_written_slice]
      rfl
    exact (keepsScratch p (fun h => outsideScratch (across ▸ h))).trans (keyOutside p outsideStack)
  · refine ⟨called, returnsKey, keyEvents, keyPC, keySP, keyInput, keyOutput, keyTrace,
      afterSP, afterMsg, afterScratch, ?_⟩
    simp only [List.append_assoc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6500000 in
/-- Execute the public RV64 entry when the scratch capacity is sufficient,
including the helper calls and the native return. -/
theorem EntryResources.successful_execution {base : Addr} {s : CPU}
    {keyExtent messageExtent capacity : Nat} (g : EntryResources base s keyExtent messageExtent capacity)
    (keyValue message : ByteList) (keyLayout : keyValue.WellFormed) (messageLayout : message.WellFormed)
    (keyFits : keyValue.size ≤ keyExtent) (messageFits : message.size ≤ messageExtent)
    (keySize : keyValue.size < 2 ^ 64) (keyLength : keyValue.bytes.size < 2 ^ 61)
    (messageLength : message.bytes.size < 2 ^ 61 - 64)
    (keyEncoded : EncodedByteList s.mem (s.reg 10#5) keyValue)
    (messageEncoded : EncodedByteList s.mem (s.reg 11#5) message)
    (capacityAt : s.mem.read64 (s.reg 12#5) = BitVec.ofNat 64 capacity)
    (room : 96 + message.bytes.size ≤ capacity) (capacitySize : capacity < 2 ^ 64)
    (pc : s.pc = routineAddress base entry)
    (entryCode : RoutineGrant base entry s.mem) (keyCode : RoutineGrant base key s.mem)
    (finishCode : RoutineGrant base finish s.mem) (sha : ShaCode (shaAddress base) s.mem)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0) :
    ∃ out events, ProgramExecution base s events out ∧
      events.length ≤ 170 + keyStepBound keyValue.bytes.size +
        8 * (message.bytes.size / 8) + 7 * (message.bytes.size % 8) +
        callSteps (64 + message.bytes.size) + callSteps 96 ∧
      out.reg 10#5 = 0#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 13#5) =
        (EthLib.Cryptography.Hash.Hmac.hmac32 keyValue.bytes message.bytes).map UInt8.toBitVec ∧
      EncodedByteList out.mem (s.reg 12#5 + 8#64) (hmacInner message (hmacKey keyValue) capacity) ∧
      (∀ p, ¬ (entryWorkspace s).Contains p → ¬ (entryScratchWritten s (64 + message.bytes.size)).Contains p →
        ¬ (entryMac s).Contains p → out.mem.cells p = s.mem.cells p) ∧
      EntrySuccessTrace base s keyValue message capacity events := by
  let whole := entryWorkspace s
  let inner := hmacInner message (hmacKey keyValue) capacity
  let alloc := entryInner s capacity
  let spill := entrySpills s
  have wholeValid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have spillFits : 784 + 104 ≤ whole.bytes := by change 784 + 104 ≤ 896; decide
  have spillValid : spill.Valid := regionSlice_valid _ _ _ wholeValid spillFits
  have innerValid : alloc.Valid := regionSlice_valid _ _ _ g.scratchValid
    (by change 8 + (capacity - 8) ≤ capacity; omega)
  obtain ⟨prepared, firstEvents, toInner, firstCount, innerPC, innerSP, scratch, mac, encoded, keyAt,
    saveSlots, innerFrame, preparedTrace⟩ := g.prepare_inner keyValue message keyLayout messageLayout keyFits messageFits
      keySize keyLength keyEncoded messageEncoded capacityAt room capacitySize pc entryCode keyCode sha
  let called := entryFinishCall prepared
  have stageCode := entryCode.preserved toInner
  obtain ⟨input, keyPtr, output, sp, link, mem⟩ := entry_finish_arguments prepared
  have input : called.reg 10#5 = s.reg 12#5 + 8#64 := input.trans (congrArg (· + 8#64) scratch)
  have k0 : called.reg 11#5 = s.reg 2#5 - 176#64 := keyPtr.trans innerSP
  have output : called.reg 12#5 = s.reg 13#5 := output.trans mac
  have sp : called.reg 2#5 = s.reg 2#5 - 176#64 := sp.trans innerSP
  have calleeLink : called.reg 1#5 = routineAddress base entry + 0x110#64 := by
    rw [link, innerPC, BitVec.add_assoc]
    rfl
  have which : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨invoke, invokeCount⟩ := run_range_observes which (entry_finish_call prepared)
    stageCode.loaded (routine_readonly_of_exec stageCode.executable)
    (entry_finish_call_allowed base prepared innerPC stageCode.aligned stageCode.executable) entry_finish_call_decoded
  have trace := entry_finish_call_events prepared
  simp only [entry_finish_call_decoded, Option.getD_some, innerPC] at trace
  rw [trace] at invoke invokeCount
  have toCallee : ProgramExecution base s (firstEvents ++ entryFinishSetupEvents base) called := toInner.append invoke
  have layout : inner.WellFormed := hmacInner_layout _ _ _ room
  have accessible : inner.size ≤ capacity - 8 := by change capacity - 8 ≤ capacity - 8; omega
  have size : inner.size < 2 ^ 64 := by change capacity - 8 < 2 ^ 64; omega
  have length : inner.bytes.size < 2 ^ 61 := hmacInner_sha256_length _ _ _ messageLength
  have value : EncodedByteList called.mem (called.reg 10#5) inner := by rw [input, mem]; exact encoded
  have available : 720 ≤ (called.reg 2#5).toNat := by
    rw [sp]
    have h := frame_base_end (s.reg 2#5) 176 (by have := g.stackAvailable; omega)
    have total := g.stackAvailable
    change 720 ≤ (s.reg 2#5 - BitVec.ofNat 64 176).toNat
    omega
  have entrySp16 : (s.reg 2#5 - 176#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 176 g.stackAligned (by decide) (by have := g.stackAvailable; omega)
  have keyAlignment : (called.reg 11#5).toNat % 8 = 0 := by rw [k0]; omega
  have linkAligned : (called.reg 1#5).toNat % 2 = 0 := by
    rw [calleeLink, BitVec.toNat_add]
    change (((routineAddress base entry).toNat + 272) % 2 ^ 64) % 2 = 0
    have h := entryCode.aligned
    omega
  have stackFrame : called.reg 2#5 - 240#64 = (regionSlice whole 480 240).base := by
    rw [sp, BitVec.sub_sub]
    exact (congrArg Region.base (stackRegion_slice _ 896 480 240 (by decide))).symm
  have stackRead : called.mem.canRead (called.reg 2#5 - 240#64) 240 = true := by
    rw [stackFrame]
    exact (toCallee.permissions _ _).2
      (caller_region_read s.mem whole wholeValid g.stackRead 480 240 (by change 480 + 240 ≤ 896; decide))
  have stackWrite : called.mem.canWrite (called.reg 2#5 - 240#64) 240 = true := by
    rw [stackFrame]
    exact (toCallee.permissions _ _).1.trans
      (caller_region_write s.mem whole wholeValid g.stackWrite 480 240 (by change 480 + 240 ≤ 896; decide))
  have k0Read : called.mem.canRead (called.reg 11#5) 64 = true := by
    rw [k0, ← entryKeyBlock_base]
    exact (toCallee.permissions _ _).2
      (caller_region_read s.mem whole wholeValid g.stackRead 720 64 (by change 720 + 64 ≤ 896; decide))
  have correctK0 (i : Fin 64) : called.mem.read8 (called.reg 11#5 + BitVec.ofNat 64 i.val) =
      (hmacKey keyValue)[i.val].toBitVec := by
    rw [mem, keyPtr]
    exact keyAt i
  have next := finishCode.preserved toCallee
  obtain ⟨finished, doneEvents, finishRun, finishCount, finishSP, finishPC, _, digest, finishFrame, finishTrace⟩ :=
    finish_execution_from_caller base called inner (hmacKey keyValue) (capacity - 8)
      (entry_finish_target base prepared innerPC) layout accessible size length value correctK0
      (g.finish_call toCallee input k0 output sp (by omega)) (sha.preserved_by_execution toCallee)
      next.loaded next.aligned next.executable available stackRead stackWrite keyAlignment k0Read linkAligned
  have throughFinish := toCallee.append finishRun
  have finishedStack := finishSP.trans sp
  have nested : (⟨called.reg 2#5 - 720#64, 720⟩ : Region) = entryFinishStack s := by
    rw [sp, BitVec.sub_sub]
    exact (stackRegion_slice _ 896 0 720 (by decide)).symm
  have inNested (p : Addr) (hit : (⟨called.reg 2#5 - 720#64, 720⟩ : Region).Contains p) :
      whole.Contains p := by
    rw [nested] at hit
    exact regionSlice_inside whole 0 720 wholeValid (by change 0 + 720 ≤ 896; decide) p hit
  have saves (i : Fin 104) :
      let p := finished.reg 2#5 + BitVec.ofNat 64 (64 + i.val)
      finished.mem.cells p = (enteredFrame .entry s).mem.cells p := by
    dsimp only
    rw [finishedStack]
    let p := s.reg 2#5 - 176#64 + BitVec.ofNat 64 (64 + i.val)
    have inside : spill.Contains p := by
      have here := caller_region_contains_offset spill spillValid i.val i.isLt
      change spill.Contains ((entrySpills s).base + BitVec.ofNat 64 i.val) at here
      rw [entrySpills_base] at here
      simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using here
    have offStack : ¬ (⟨called.reg 2#5 - 720#64, 720⟩ : Region).Contains p := by
      rw [nested]
      intro hit
      exact regionSlices_disjoint whole 0 720 784 104 wholeValid (by decide) spillFits p ⟨hit, inside⟩
    have offMac : ¬ (⟨called.reg 12#5, 32⟩ : Region).Contains p := by
      rw [output]
      intro hit
      exact g.stackMac p ⟨regionSlice_inside _ _ _ wholeValid spillFits _ inside, hit⟩
    rw [finishFrame p offStack offMac, mem]
    simpa only [innerSP, p] using saveSlots i
  have entryNext := entryCode.preserved throughFinish
  have finalRead : finished.mem.canRead (finished.reg 2#5) 176 = true := by
    rw [finishedStack, ← entryFrame_base]
    exact (throughFinish.permissions _ _).2
      (caller_region_read s.mem whole wholeValid g.stackRead 720 176 (by change 720 + 176 ≤ 896; decide))
  have restoredAlign : (finished.reg 2#5).toNat % 8 = 0 := by rw [finishedStack]; omega
  obtain ⟨out, ret, retCount, ok, outSP, outPC, regs, outMem⟩ :=
    entry_success_return_fetched base s finished (finishPC.trans calleeLink) entryNext.loaded
      entryNext.aligned entryNext.executable finishedStack restoredAlign finalRead returnAligned saves
  refine ⟨out, _, throughFinish.append ret, ?_, ok, outSP, outPC, regs, ?_, ?_, ?_, ?_⟩
  · change doneEvents.length ≤ 75 + callSteps
        (hmacInner message (hmacKey keyValue) capacity).bytes.size + callSteps 96 at finishCount
    rw [hmacInner_length] at finishCount
    simp only [List.length_append, retCount, entryFinishSetupEvents, List.length_cons, List.length_nil]
    omega
  · rw [outMem, ← output, ← hmacFinish_hmacInner keyValue message capacity]
    exact digest
  · rw [outMem]
    apply encoded.preserved layout accessible innerValid
    intro p inside
    have inScratch : (entryScratch s capacity).Contains p := regionSlice_inside _ _ _ g.scratchValid
      (by change 8 + (capacity - 8) ≤ capacity; omega) p inside
    rw [finishFrame p (fun hit => g.stackScratch p ⟨inNested p hit, inScratch⟩) (by
      rw [output]
      exact fun hit => g.scratchMac p ⟨inScratch, hit⟩), mem]
  · intro p offStack offScratch offMac
    rw [outMem, finishFrame p (fun hit => offStack (inNested p hit)) (by rw [output]; exact offMac), mem]
    exact innerFrame p offStack offScratch
  · refine ⟨called, firstEvents, doneEvents, preparedTrace, entry_finish_target base prepared innerPC,
      sp, input, k0, output, finishTrace, ?_⟩
    simp only [List.append_assoc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- On insufficient capacity, the same caller grants support an immediate
return. Message and key inputs, scratch and MAC keep their original bytes. -/
theorem EntryResources.undersized_execution {base : Addr} {s : CPU}
    {keyExtent messageExtent capacity : Nat} (g : EntryResources base s keyExtent messageExtent capacity)
    (message : ByteList) (messageLayout : message.WellFormed) (messageFits : message.size ≤ messageExtent)
    (messageEncoded : EncodedByteList s.mem (s.reg 11#5) message)
    (capacityAt : s.mem.read64 (s.reg 12#5) = BitVec.ofNat 64 capacity)
    (capacityMin : 8 ≤ capacity) (capacitySize : capacity < 2 ^ 64)
    (messageSize : message.bytes.size < 2 ^ 64)
    (short : capacity < 96 + message.bytes.size)
    (pc : s.pc = routineAddress base entry) (entryCode : RoutineGrant base entry s.mem)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0) :
    ∃ out, ProgramExecution base s (entrySmallEvents base s (BitVec.ofNat 64 capacity)) out ∧
      (entrySmallEvents base s (BitVec.ofNat 64 capacity)).length ≤ 40 ∧
      out.reg 10#5 = 1#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ p, ¬ (entryFrame s).Contains p → out.mem.cells p = s.mem.cells p) := by
  let whole := entryWorkspace s
  have valid : whole.Valid := stackRegion_valid _ _ g.stackAvailable
  have frame : entryFrame s = ⟨s.reg 2#5 - 176#64, 176⟩ := stackRegion_slice _ 896 720 176 (by decide)
  have inside (p : Addr) (hit : (⟨s.reg 2#5 - 176#64, 176⟩ : Region).Contains p) :
      whole.Contains p := by
    rw [← frame] at hit
    exact regionSlice_inside whole 720 176 valid (by change 720 + 176 ≤ 896; decide) p hit
  have msgHeader : 24 ≤ messageExtent := by
    have := messageLayout.1
    have := messageLayout.2.2.1
    omega
  obtain ⟨stackAligned, stackRead, stackWrite⟩ := g.frame_grants
  obtain ⟨capacityRead, countRead⟩ := g.capacity_grants capacityMin msgHeader
  have separate (p : Addr) (whereAt : p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64) (i : Fin 8) :
      ¬ (⟨s.reg 2#5 - 176#64, 176⟩ : Region).Contains (p + BitVec.ofNat 64 i.val) := by
    intro hit
    have inStack := inside _ hit
    rcases whereAt with rfl | rfl
    · exact g.stackScratch _ ⟨inStack,
        caller_region_contains_offset _ g.scratchValid i.val (by change i.val < capacity; have := i.isLt; omega)⟩
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add] at inStack
      exact g.stackMessage _ ⟨inStack,
        caller_region_contains_offset _ g.messageValid (16 + i.val) (by
          change 16 + i.val < messageExtent
          have := i.isLt
          omega)⟩
  obtain ⟨out, run, bound, status, sp, link, regs, restored⟩ :=
    undersized_entry_fetched base s (BitVec.ofNat 64 capacity) (BitVec.ofNat 64 message.bytes.size) pc
      entryCode.loaded entryCode.aligned entryCode.executable (by have := g.stackAvailable; omega)
      stackAligned stackRead stackWrite capacityRead countRead capacityAt messageEncoded.count separate
      returnAligned (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacitySize, Nat.mod_eq_of_lt messageSize]
        using short)
  exact ⟨out, run, bound, status, sp, link, regs, by rw [frame]; exact restored⟩

end Crypto.HMACSHA256.RISCV64
