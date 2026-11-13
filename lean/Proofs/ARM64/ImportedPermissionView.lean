import Proofs.ARM64.ImportedCallerEntry
import Proofs.ARM64.ImportedAccess

/-!
A conservative borrowed permission view for SHA-256, preserving every byte.
The view grants RX to the recorded image, RW to the 416-byte stack, W to the
32-byte digest, and R only to the 24-byte input header and used payload; all
other addresses lack logical permission. Full input extent remains an explicit
semantic accessibility and separation obligation, including unused room.

PermissionViewInputs states caller/profile semantic grants through Authority,
independently of imported permission bits. It derives unchanged CallInputs
without assuming physical mappings are unmapped, non-executable, or exactly
these rights. Constructing this mathematical view performs no protection change.

The target profile supplies physical correspondence, including tagged-address
aliases, grant validity, lifetime and interference.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
local instance (region : Region) (p : BitVec 64) : Decidable (region.Contains p) :=
  inferInstanceAs (Decidable (region.base.toNat ≤ p.toNat ∧ p.toNat < region.base.toNat + region.bytes))

def callerHeader (s : Arm64.State) : Region := ⟨s.readReg64 .x0, 24⟩
def callerPayload (s : Arm64.State) (message : Crypto.Reference.ByteList) : Region :=
  ⟨s.readReg64 .x0 + BitVec.ofNat 64 message.offset, message.bytes.size⟩

def permissionReadFootprint (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : Prop :=
  (callerHeader s).Contains p ∨ (callerPayload s message).Contains p ∨
    (callerImage base).Contains p ∨ (callerStack s).Contains p

def permissionWriteFootprint (s : Arm64.State) (p : BitVec 64) : Prop :=
  (callerOutput s).Contains p ∨ (callerStack s).Contains p

/-- Caller-established semantic grants are independent of imported model
permission bits. Connecting this Authority and byte view to physical hardware,
address tagging, ownership lifetime and interference is a separate obligation. -/
structure PermissionViewInputs (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority) : Prop where
  layout : message.WellFormed
  size64 : message.size < 2 ^ 64
  accessible : message.size ≤ extent
  headerFits : 24 ≤ extent
  length : message.bytes.size < 2 ^ 61
  messageAligned : (s.readReg64 .x0).toNat % 8 = 0
  digestAligned : (s.readReg64 .x1).toNat % 8 = 0
  stackAligned : s.sp.toNat % 16 = 0
  stackAvailable : 416 ≤ s.sp.toNat
  inputValid : (callerInput s extent).Valid
  outputValid : (callerOutput s).Valid
  stackValid : (callerStack s).Valid
  imageValid : (callerImage base).Valid
  outputInput : (callerOutput s).Disjoint (callerInput s extent)
  outputStack : (callerOutput s).Disjoint (callerStack s)
  outputImage : (callerOutput s).Disjoint (callerImage base)
  stackInput : (callerStack s).Disjoint (callerInput s extent)
  stackImage : (callerStack s).Disjoint (callerImage base)
  /-- Semantic accessibility of the complete independently supplied extent;
  the logical view still denies reads from unused room. -/
  inputAccessible : ∀ p, (callerInput s extent).Contains p → authority.readable p
  headerRead : ∀ p, (callerHeader s).Contains p → authority.readable p
  payloadRead : ∀ p, (callerPayload s message).Contains p → authority.readable p
  stackRead : ∀ p, (callerStack s).Contains p → authority.readable p
  stackWrite : ∀ p, (callerStack s).Contains p → authority.writable p
  outputWrite : ∀ p, (callerOutput s).Contains p → authority.writable p
  imageRead : ∀ p, (callerImage base).Contains p → authority.readable p
  imageExec : ∀ p, (callerImage base).Contains p → authority.executable p
  sizeValue : s.mem.read64 (s.readReg64 .x0) = BitVec.ofNat 64 message.size
  offsetValue : s.mem.read64 (s.readReg64 .x0 + 8#64) = BitVec.ofNat 64 message.offset
  countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 message.bytes.size
  bytes : ∀ i : Fin message.bytes.size,
    s.mem.read8 (s.readReg64 .x0 + BitVec.ofNat 64 (message.offset + i.val)) =
      (message.bytes.get! i.val).toBitVec
  pc : s.pc = base
  running : s.status = .Running
  codeAligned : base.toNat % 4 = 0
  codeBytes : ∀ i, (hi : i < (program base).code.length) →
    s.mem.read8 (base + BitVec.ofNat 64 i) = (program base).code[i]

def logicalPermission (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : Option Arm64.Perm :=
  if (callerImage base).Contains p then some Arm64.Perm.rx
  else if (callerStack s).Contains p then some Arm64.Perm.rw
  else if (callerOutput s).Contains p then some { r := false, w := true, x := false }
  else if (callerHeader s).Contains p ∨ (callerPayload s message).Contains p then some Arm64.Perm.ro
  else none

def logicalMemory (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) : Arm64.Memory :=
  Arm64.Memory.ofFn s.mem.read8 (logicalPermission base s message)

def logicalState (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) : Arm64.State :=
  { s with mem := logicalMemory base s message }

theorem logicalMemory_read8 (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    (logicalMemory base s message).read8 p = s.mem.read8 p := rfl

theorem logicalMemory_read64 (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    (logicalMemory base s message).read64 p = s.mem.read64 p := by
  simp only [Arm64.Memory.read64, logicalMemory_read8]

theorem logicalMemory_perm (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    (logicalMemory base s message).perm p = logicalPermission base s message p := by
  by_cases image : (callerImage base).Contains p <;>
    by_cases stack : (callerStack s).Contains p <;>
    by_cases output : (callerOutput s).Contains p <;>
    by_cases input : (callerHeader s).Contains p ∨ (callerPayload s message).Contains p
  all_goals simp [logicalMemory, Arm64.Memory.ofFn, Arm64.Memory.perm, logicalPermission,
    image, stack, output, input, Arm64.Perm.rwx, Arm64.Perm.rx, Arm64.Perm.rw, Arm64.Perm.ro]

theorem logicalMemory_noLazy (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    (logicalMemory base s message).isLazyFree p = false := by
  by_cases image : (callerImage base).Contains p <;>
    by_cases stack : (callerStack s).Contains p <;>
    by_cases output : (callerOutput s).Contains p <;>
    by_cases input : (callerHeader s).Contains p ∨ (callerPayload s message).Contains p
  all_goals simp [logicalMemory, Arm64.Memory.ofFn, Arm64.Memory.isLazyFree, logicalPermission,
    image, stack, output, input, Arm64.Perm.rx, Arm64.Perm.rw, Arm64.Perm.ro]

theorem logicalPermission_read (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (read : (logicalPermission base s message p).r = true) :
    permissionReadFootprint base s message p := by
  unfold logicalPermission at read
  split at read
  · exact Or.inr (Or.inr (Or.inl ‹_›))
  · split at read
    · exact Or.inr (Or.inr (Or.inr ‹_›))
    · split at read
      · contradiction
      · split at read
        · rcases ‹(callerHeader s).Contains p ∨ (callerPayload s message).Contains p› with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · contradiction

theorem logicalPermission_write (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (write : ((logicalPermission base s message p).w && !(logicalPermission base s message p).x) = true) :
    permissionWriteFootprint s p := by
  unfold logicalPermission at write
  split at write
  · contradiction
  · split at write
    · exact Or.inr ‹_›
    · split at write
      · exact Or.inl ‹_›
      · split at write <;> contradiction

theorem view_data_extent (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    message.offset + message.bytes.size ≤ extent := by
  have wf := entry.layout
  rcases wf with ⟨_, _, _, countSize⟩
  have accessible := entry.accessible
  omega

theorem view_header_valid (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) : (callerHeader s).Valid := by
  have valid := entry.inputValid
  have fits := entry.headerFits
  change (s.readReg64 .x0).toNat + extent ≤ 2 ^ 64 at valid
  change (s.readReg64 .x0).toNat + 24 ≤ 2 ^ 64
  omega

theorem view_header_subset (s : Arm64.State) (extent : Nat) (fits : 24 ≤ extent) (p : BitVec 64)
    (inside : (callerHeader s).Contains p) : (callerInput s extent).Contains p := by
  change (s.readReg64 .x0).toNat ≤ p.toNat ∧ p.toNat < (s.readReg64 .x0).toNat + 24 at inside
  change (s.readReg64 .x0).toNat ≤ p.toNat ∧ p.toNat < (s.readReg64 .x0).toNat + extent
  omega

theorem view_payload_nat (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (nonempty : 0 < message.bytes.size) :
    (callerPayload s message).base.toNat = (s.readReg64 .x0).toNat + message.offset := by
  have dataExtent := view_data_extent base s message extent authority entry
  have valid := entry.inputValid
  change (s.readReg64 .x0).toNat + extent ≤ 2 ^ 64 at valid
  have offset64 : message.offset < 2 ^ 64 := by have := (s.readReg64 .x0).isLt; omega
  have sum : (s.readReg64 .x0).toNat + message.offset < 2 ^ 64 := by omega
  simp only [callerPayload, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt offset64, Nat.mod_eq_of_lt sum]

theorem view_payload_valid (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) : (callerPayload s message).Valid := by
  by_cases empty : message.bytes.size = 0
  · unfold Region.Valid callerPayload
    simp only [empty, Nat.add_zero]
    exact Nat.le_of_lt (BitVec.isLt _)
  · have address := view_payload_nat base s message extent authority entry (by omega)
    have dataExtent := view_data_extent base s message extent authority entry
    have valid := entry.inputValid
    change (s.readReg64 .x0).toNat + extent ≤ 2 ^ 64 at valid
    unfold Region.Valid
    rw [address]
    change (s.readReg64 .x0).toNat + message.offset + message.bytes.size ≤ 2 ^ 64
    omega

theorem view_payload_subset (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (inside : (callerPayload s message).Contains p) : (callerInput s extent).Contains p := by
  have dataExtent := view_data_extent base s message extent authority entry
  by_cases empty : message.bytes.size = 0
  · unfold Region.Contains callerPayload at inside
    simp only [empty, Nat.add_zero] at inside
    omega
  · have address := view_payload_nat base s message extent authority entry (by omega)
    unfold Region.Contains at inside ⊢
    rw [address] at inside
    change (s.readReg64 .x0).toNat ≤ p.toNat ∧ p.toNat < (s.readReg64 .x0).toNat + extent
    change (s.readReg64 .x0).toNat + message.offset ≤ p.toNat ∧
      p.toNat < (s.readReg64 .x0).toNat + message.offset + message.bytes.size at inside
    omega

theorem logicalMemory_read_one (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (read : permissionReadFootprint base s message p)
    (outside : ¬(callerOutput s).Contains p) : (logicalMemory base s message).canRead p 1 = true := by
  simp only [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree,
    logicalMemory_perm, logicalMemory_noLazy, Bool.not_false, Bool.and_true]
  unfold logicalPermission
  split
  · rfl
  · split
    · rfl
    · try rw [if_neg outside]
      split
      · rfl
      · unfold permissionReadFootprint at read
        tauto

theorem logicalMemory_write_one (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (write : permissionWriteFootprint s p)
    (outside : ¬(callerImage base).Contains p) : (logicalMemory base s message).canWrite p 1 = true := by
  simp only [Arm64.Memory.canWrite, Arm64.Memory.allPerm, logicalMemory_perm, Bool.and_true]
  unfold logicalPermission
  rw [if_neg outside]
  split
  · rfl
  · unfold permissionWriteFootprint at write
    have output : (callerOutput s).Contains p := by tauto
    rw [if_pos output]
    rfl

@[simp] theorem view_perm_writeSized (m : Arm64.Memory) (size : Arm64.MemWidth)
    (a p : BitVec 64) (value : BitVec 64) : (m.writeSized size a value).perm p = m.perm p := by
  cases size <;> simp [Arm64.Memory.writeSized, Arm64.Memory.write16, Arm64.Memory.write32, Arm64.Memory.write64]

theorem view_execStr_perm (size : Arm64.MemWidth) (rt : Arm64.Reg) (addr : Arm64.AddrMode)
    (s : Arm64.State) (p : BitVec 64) : (Arm64.execStr size rt addr s).mem.perm p = s.mem.perm p := by
  simp only [Arm64.execStr]
  repeat' split
  all_goals simp only [Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.setStatus,
    Arm64.State.writeReg64, view_perm_writeSized]

theorem view_execStp_perm (width : Arm64.RegWidth) (rt1 rt2 : Arm64.Reg) (addr : Arm64.AddrMode)
    (s : Arm64.State) (p : BitVec 64) : (Arm64.execStp width rt1 rt2 addr s).mem.perm p = s.mem.perm p := by
  simp only [Arm64.execStp]
  repeat' split
  all_goals simp only [Arm64.State.advancePC, Arm64.State.setMem, Arm64.State.setStatus,
    Arm64.State.writeReg64, view_perm_writeSized]

theorem permitted_preserves_permissions (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (s : Arm64.State) (p : BitVec 64) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).mem.perm p = s.mem.perm p := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at permitted
  case str size rt addr => exact view_execStr_perm size rt addr s p
  case stp width rt1 rt2 addr => exact view_execStp_perm width rt1 rt2 addr s p
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execLdp,
    Arm64.execAddSubImm, Arm64.execLogicalImm, Arm64.execMoveWide, Arm64.execBitfield,
    Arm64.execLogicalShift, Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1]
  all_goals repeat' split
  all_goals rfl

def DataAccess.WithinView (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (access : DataAccess) : Prop :=
  ∀ i, i < access.bytes → if access.write then
    permissionWriteFootprint entryState (access.address + BitVec.ofNat 64 i)
    else permissionReadFootprint base entryState message (access.address + BitVec.ofNat 64 i)

theorem allowed_within_view (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (m : Arm64.Memory)
    (permissions : ∀ p, m.perm p = logicalPermission base entryState message p)
    (access : DataAccess) (allowed : access.Allowed m) : access.WithinView base entryState message := by
  intro i hi
  unfold DataAccess.Allowed at allowed
  cases write : access.write
  · simp only [write, Bool.false_eq_true, ↓reduceIte] at allowed ⊢
    have pair : m.allPerm (·.r) access.address access.bytes = true ∧
        m.allNoLazyFree access.address access.bytes = true := by
      simpa only [Arm64.Memory.canRead, Bool.and_eq_true] using allowed
    have guard := pair.1
    have bit := (allPerm_true_iff m (·.r) access.address access.bytes).mp guard i hi
    rw [permissions] at bit
    exact logicalPermission_read base entryState message _ bit
  · simp only [write, ↓reduceIte] at allowed ⊢
    have bit := (allPerm_true_iff m (fun p => p.w && !p.x) access.address access.bytes).mp allowed i hi
    rw [permissions] at bit
    exact logicalPermission_write base entryState message _ bit

theorem view_read_grant (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (inside : permissionReadFootprint base s message p) : (logicalMemory base s message).canRead p 1 = true := by
  apply logicalMemory_read_one base s message p inside
  intro output
  rcases inside with header | payload | image | stack
  · exact entry.outputInput p ⟨output, view_header_subset s extent entry.headerFits p header⟩
  · exact entry.outputInput p ⟨output, view_payload_subset base s message extent authority entry p payload⟩
  · exact entry.outputImage p ⟨output, image⟩
  · exact entry.outputStack p ⟨output, stack⟩

theorem view_write_grant (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (inside : permissionWriteFootprint s p) : (logicalMemory base s message).canWrite p 1 = true := by
  apply logicalMemory_write_one base s message p inside
  intro image
  rcases inside with output | stack
  · exact entry.outputImage p ⟨output, image⟩
  · exact entry.stackImage p ⟨stack, image⟩

theorem view_code_loaded (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    (program base).CodeLoaded (logicalMemory base s message) := by
  apply codeLoaded_iff.mpr
  refine ⟨entry.codeAligned, ?_, ?_⟩
  · rw [program_code_length]
    exact entry.imageValid
  · intro i hi
    have small : i < 896 := by rwa [program_code_length] at hi
    have inside := caller_region_contains_offset (callerImage base) entry.imageValid i small
    refine ⟨(logicalMemory_read8 base s message _).trans (entry.codeBytes i hi), ?_, logicalMemory_noLazy base s message _⟩
    rw [logicalMemory_perm]
    unfold logicalPermission
    exact if_pos inside

theorem permission_view_inputs (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    CallInputs base (logicalState base s message) message.bytes := by
  let view := logicalState base s message
  have wf := entry.layout
  rcases wf with ⟨offsetMinimum, offsetAligned, offsetSize, countSize⟩
  have dataExtent := view_data_extent base s message extent authority entry
  have payload : inputPayload view = (callerPayload s message).base := by
    change s.readReg64 .x0 + (logicalMemory base s message).read64 (s.readReg64 .x0 + 8#64) =
      s.readReg64 .x0 + BitVec.ofNat 64 message.offset
    rw [logicalMemory_read64, entry.offsetValue]
  have inputAddress (i : Nat) : inputPayload view + BitVec.ofNat 64 i =
      s.readReg64 .x0 + BitVec.ofNat 64 (message.offset + i) := by
    rw [payload]
    change (s.readReg64 .x0 + BitVec.ofNat 64 message.offset) + BitVec.ofNat 64 i = _
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have headerReads (p : BitVec 64) (inside : (callerHeader s).Contains p) : view.mem.canRead p 1 = true :=
    view_read_grant base s message extent authority entry p (Or.inl inside)
  have payloadReads (p : BitVec 64) (inside : (callerPayload s message).Contains p) : view.mem.canRead p 1 = true :=
    view_read_grant base s message extent authority entry p (Or.inr (Or.inl inside))
  have stackReads (p : BitVec 64) (inside : (callerStack s).Contains p) : view.mem.canRead p 1 = true :=
    view_read_grant base s message extent authority entry p (Or.inr (Or.inr (Or.inr inside)))
  have imageReads (p : BitVec 64) (inside : (callerImage base).Contains p) : view.mem.canRead p 1 = true :=
    view_read_grant base s message extent authority entry p (Or.inr (Or.inr (Or.inl inside)))
  have stackWrites (p : BitVec 64) (inside : (callerStack s).Contains p) : view.mem.canWrite p 1 = true :=
    view_write_grant base s message extent authority entry p (Or.inr inside)
  have outputWrites (p : BitVec 64) (inside : (callerOutput s).Contains p) : view.mem.canWrite p 1 = true :=
    view_write_grant base s message extent authority entry p (Or.inl inside)
  have countValue : view.mem.read64 (view.readReg64 .x0 + 16#64) = BitVec.ofNat 64 message.bytes.size :=
    (logicalMemory_read64 base s message _).trans entry.countValue
  refine ⟨entry.length, entry.pc, entry.running, view_code_loaded base s message extent authority entry,
    caller_stack_alignment s entry.stackAligned entry.stackAvailable, ?_, ?_, countValue,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact caller_region_read view.mem (callerHeader s) (view_header_valid base s message extent authority entry) headerReads 8 8 (by change 8 + 8 ≤ 24; decide)
  · exact caller_region_read view.mem (callerHeader s) (view_header_valid base s message extent authority entry) headerReads 16 8 (by change 16 + 8 ≤ 24; decide)
  · intro off n bound
    exact caller_region_read view.mem (callerStack s) entry.stackValid stackReads off n bound
  · intro off n bound
    exact caller_region_write view.mem (callerStack s) entry.stackValid stackWrites off n bound
  · intro off n bound
    rw [payload]
    exact caller_region_read view.mem (callerPayload s message) (view_payload_valid base s message extent authority entry) payloadReads off n bound
  · intro off n bound
    exact caller_region_write view.mem (callerOutput s) entry.outputValid outputWrites off n bound
  · intro off n bound
    exact caller_region_read view.mem (callerImage base) entry.imageValid imageReads off n bound
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    exact entry.stackImage _ ⟨inside, caller_region_contains_offset (callerImage base) entry.imageValid i.val i.isLt⟩
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    apply entry.stackInput _ ⟨inside, ?_⟩
    have point := caller_region_contains_offset (callerPayload s message)
      (view_payload_valid base s message extent authority entry) i.val i.isLt
    rw [payload]
    exact view_payload_subset base s message extent authority entry _ point
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    exact entry.outputStack _ ⟨caller_region_contains_offset (callerOutput s) entry.outputValid i.val i.isLt, inside⟩
  · intro i
    rw [inputAddress]
    exact (logicalMemory_read8 base s message _).trans (entry.bytes i)

/-- Every transient successful data access is bounded by the fixed entry-time
header/used-payload/code/stack read regions and output/stack write regions. -/
def ViewAccessPath (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, current => match Arm64.decode word with
    | none => False
    | some instruction => (∀ access ∈ dataAccesses instruction current,
        access.WithinView base entryState message) ∧
      ViewAccessPath base entryState message rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current)

theorem runWords_view_accessPath (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (current out : Arm64.State)
    (permissions : ∀ p, current.mem.perm p = logicalPermission base entryState message p)
    (permitted : PermittedWords words) (executed : runWords words current = some out)
    (running : out.status = .Running) : ViewAccessPath base entryState message words current := by
  induction words generalizing current with
  | nil => exact True.intro
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current) = some out at executed
      have instructionAllowed := permitted word (by simp) instruction decoded
      have nextRunning := runWords_running_before rest _ out permitted.tail executed running
      have guards := permitted_accesses_allowed instruction current instructionAllowed nextRunning
      have nextPermissions (p : BitVec 64) :
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction current).mem.perm p =
            logicalPermission base entryState message p :=
        (permitted_preserves_permissions instruction instructionAllowed current p).trans (permissions p)
      simp only [ViewAccessPath, decoded]
      refine ⟨?_, ih _ nextPermissions permitted.tail executed⟩
      intro access member
      exact allowed_within_view base entryState message current.mem permissions access (guards access member)

theorem logical_runWords_accessPath (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (out : Arm64.State)
    (permitted : PermittedWords words)
    (executed : runWords words (logicalState base entryState message) = some out)
    (running : out.status = .Running) :
    ViewAccessPath base entryState message words (logicalState base entryState message) :=
  runWords_view_accessPath base entryState message words _ out
    (logicalMemory_perm base entryState message) permitted executed running

theorem view_path_observed (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (current out : Arm64.State)
    (path : ViewAccessPath base entryState message words current)
    (executed : runWords words current = some out) :
    ∃ observations, runWordsObserved words current = some (out, observations) ∧
      ∀ observation ∈ observations, ∀ access ∈ observation.accesses,
        access.WithinView base entryState message := by
  induction words generalizing current with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    refine ⟨[], rfl, ?_⟩
    simp
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current) = some out at executed
      simp only [ViewAccessPath, decoded] at path
      obtain ⟨observations, observed, confined⟩ := ih _ path.2 executed
      refine ⟨instructionObservation instruction current :: observations, ?_, ?_⟩
      · simp only [runWordsObserved, decoded, Bind.bind, Option.bind, observed, pure, Pure.pure]
      · intro observation member access accessMember
        rcases List.mem_cons.mp member with same | later
        · subst observation
          exact path.1 access accessMember
        · exact confined observation later access accessMember

theorem logical_runWords_observed (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (out : Arm64.State)
    (permitted : PermittedWords words)
    (executed : runWords words (logicalState base entryState message) = some out)
    (running : out.status = .Running) :
    ∃ observations, runWordsObserved words (logicalState base entryState message) = some (out, observations) ∧
      ∀ observation ∈ observations, ∀ access ∈ observation.accesses,
        access.WithinView base entryState message :=
  view_path_observed base entryState message words _ out
    (logical_runWords_accessPath base entryState message words out permitted executed running) executed

theorem logicalPermission_exec (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (execute : (logicalPermission base s message p).x = true) : (callerImage base).Contains p := by
  unfold logicalPermission at execute
  split at execute
  · assumption
  · split at execute
    · contradiction
    · split at execute
      · contradiction
      · split at execute <;> contradiction

theorem view_exec_within (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (m : Arm64.Memory)
    (permissions : ∀ p, m.perm p = logicalPermission base entryState message p)
    (address : BitVec 64) (bytes : Nat) (execute : m.canExec address bytes = true) :
    ∀ i, i < bytes → (callerImage base).Contains (address + BitVec.ofNat 64 i) := by
  intro i hi
  have bit := (allPerm_true_iff m (·.x) address bytes).mp execute i hi
  rw [permissions] at bit
  exact logicalPermission_exec base entryState message _ bit

theorem view_read_authority (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (inside : permissionReadFootprint base s message p) : authority.readable p := by
  rcases inside with header | payload | image | stack
  · exact entry.headerRead p header
  · exact entry.payloadRead p payload
  · exact entry.imageRead p image
  · exact entry.stackRead p stack

theorem view_write_authority (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (inside : permissionWriteFootprint s p) : authority.writable p := by
  rcases inside with output | stack
  · exact entry.outputWrite p output
  · exact entry.stackWrite p stack

theorem view_access_authority (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (access : DataAccess)
    (inside : access.WithinView base s message) : ∀ i, i < access.bytes →
      if access.write then authority.writable (access.address + BitVec.ofNat 64 i)
      else authority.readable (access.address + BitVec.ofNat 64 i) := by
  intro i hi
  have byte := inside i hi
  cases writing : access.write
  · simp only [writing, Bool.false_eq_true, ↓reduceIte] at byte ⊢
    exact view_read_authority base s message extent authority entry _ byte
  · simp only [writing, ↓reduceIte] at byte ⊢
    exact view_write_authority base s message extent authority entry _ byte

theorem logical_runWords_observed_authority (base : BitVec 64) (entryState : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base entryState message extent authority)
    (words : List (BitVec 32)) (out : Arm64.State)
    (permitted : PermittedWords words)
    (executed : runWords words (logicalState base entryState message) = some out)
    (running : out.status = .Running) :
    ∃ observations, runWordsObserved words (logicalState base entryState message) = some (out, observations) ∧
      (∀ observation ∈ observations, ∀ access ∈ observation.accesses,
        access.WithinView base entryState message) ∧
      (∀ observation ∈ observations, ∀ access ∈ observation.accesses, ∀ i, i < access.bytes →
        if access.write then authority.writable (access.address + BitVec.ofNat 64 i)
        else authority.readable (access.address + BitVec.ofNat 64 i)) := by
  obtain ⟨observations, observed, confined⟩ := logical_runWords_observed base entryState message words out permitted executed running
  refine ⟨observations, observed, confined, ?_⟩
  intro observation member access accessMember
  exact view_access_authority base entryState message extent authority entry access
    (confined observation member access accessMember)

end Crypto.ARM64.Imported
