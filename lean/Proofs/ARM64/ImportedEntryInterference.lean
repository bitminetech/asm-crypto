import Proofs.ARM64.ImportedInstructionLocality

/-!
Entry stability under an environment step before the recorded SUB allocates
SHA-256's frame. Private CPU agreement and full-cell preservation of the
complete input extent, image and digest retain all static entry facts. Positive
read/write grants over the reserved 416-byte future stack are the explicit
accessibility/lifetime environment law; its old bytes may change arbitrarily.
The static protected footprint is proved disjoint from that stack.

The projected form permits unrelated global-tail progress. No stack-byte
agreement, execution witness or candidate result is a premise. This entry
bridge does not alone establish the full concurrent execution or a physical
permission/alias profile.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure EntryCPUAgreement (before after : Arm64.State) : Prop where
  registers : after.regs = before.regs
  sp : after.sp = before.sp
  pc : after.pc = before.pc
  status : after.status = before.status

theorem entryCPUAgreement_of_projection (before after : Arm64.State)
    (same : CPUProjection after = CPUProjection before) : EntryCPUAgreement before after := by
  constructor
  · have value := congrArg Arm64.State.regs same
    exact value
  · have value := congrArg Arm64.State.sp same
    exact value
  · have value := congrArg Arm64.State.pc same
    exact value
  · have value := congrArg Arm64.State.status same
    exact value

theorem EntryCPUAgreement.read {before after : Arm64.State} (cpu : EntryCPUAgreement before after)
    (reg : Arm64.Reg) : after.readReg64 reg = before.readReg64 reg := by
  cases reg <;> simp only [Arm64.State.readReg64, cpu.registers, cpu.sp]

theorem EntryCPUAgreement.stackBase {before after : Arm64.State} (cpu : EntryCPUAgreement before after) :
    entryStack after = entryStack before := by simp only [entryStack, cpu.sp]

def entryProtected (base : BitVec 64) (s : Arm64.State) (extent : Nat) (p : BitVec 64) : Prop :=
  (callerInput s extent).Contains p ∨ (callerImage base).Contains p ∨ (callerOutput s).Contains p

structure EntryStackGrants (s : Arm64.State) (memory : Arm64.Memory) : Prop where
  read : ∀ off n, off + n ≤ 416 → memory.canRead (entryStack s + BitVec.ofNat 64 off) n = true
  write : ∀ off n, off + n ≤ 416 → memory.canWrite (entryStack s + BitVec.ofNat 64 off) n = true

theorem entry_input_cells (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (off n : Nat) (bound : off + n ≤ extent) :
    CellsOnRange t.mem (logicalState base s message).mem (s.readReg64 .x0 + BitVec.ofNat 64 off) n := by
  intro i hi
  have inside := caller_region_contains_offset (callerInput s extent) entry.inputValid (off + i) (by change off + i < extent; omega)
  have cell := same _ (Or.inl inside)
  simpa only [callerInput, BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem entry_image_cells (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (off n : Nat) (bound : off + n ≤ 896) :
    CellsOnRange t.mem (logicalState base s message).mem (base + BitVec.ofNat 64 off) n := by
  intro i hi
  have inside := caller_region_contains_offset (callerImage base) entry.imageValid (off + i) (by change off + i < 896; omega)
  have cell := same _ (Or.inr (Or.inl inside))
  simpa only [callerImage, BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem entry_output_cells (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (off n : Nat) (bound : off + n ≤ 32) :
    CellsOnRange t.mem (logicalState base s message).mem (s.readReg64 .x1 + BitVec.ofNat 64 off) n := by
  intro i hi
  have inside := caller_region_contains_offset (callerOutput s) entry.outputValid (off + i) (by change off + i < 32; omega)
  have cell := same _ (Or.inr (Or.inr inside))
  simpa only [callerOutput, BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem entry_read64_cells (left right : Arm64.Memory) (address : BitVec 64)
    (same : CellsOnRange left right address 8) : left.read64 address = right.read64 address := by
  exact readSized_cells_eq left right address .X64 false same

theorem permission_view_entry_interference (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (cpu : EntryCPUAgreement (logicalState base s message) t)
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (stack : EntryStackGrants s t.mem) : CallInputs base t message.bytes := by
  let before := logicalState base s message
  have original : CallInputs base before message.bytes := permission_view_inputs base s message extent authority entry
  have beforeReg0 : before.readReg64 .x0 = s.readReg64 .x0 := rfl
  have beforeReg1 : before.readReg64 .x1 = s.readReg64 .x1 := rfl
  have reg0 : t.readReg64 .x0 = s.readReg64 .x0 := (cpu.read .x0).trans beforeReg0
  have reg1 : t.readReg64 .x1 = s.readReg64 .x1 := (cpu.read .x1).trans beforeReg1
  have stackBase := cpu.stackBase
  have dataExtent := view_data_extent base s message extent authority entry
  have header8 := entry_input_cells base s t message extent authority entry same 8 8 (by have := entry.headerFits; omega)
  have header16 := entry_input_cells base s t message extent authority entry same 16 8 (by have := entry.headerFits; omega)
  have offsetValue := entry_read64_cells t.mem before.mem (s.readReg64 .x0 + 8#64) header8
  have countValue := entry_read64_cells t.mem before.mem (s.readReg64 .x0 + 16#64) header16
  have payload : inputPayload t = inputPayload before := by
    unfold inputPayload
    rw [reg0, beforeReg0, offsetValue]
  have sourcePayload : inputPayload before = s.readReg64 .x0 + BitVec.ofNat 64 message.offset := by
    change s.readReg64 .x0 + (logicalMemory base s message).read64 (s.readReg64 .x0 + 8#64) = _
    rw [logicalMemory_read64, entry.offsetValue]
  have inputAddress (off : Nat) : inputPayload before + BitVec.ofNat 64 off =
      s.readReg64 .x0 + BitVec.ofNat 64 (message.offset + off) := by
    rw [sourcePayload, BitVec.ofNat_add, BitVec.add_assoc]
  have dataCells (off n : Nat) (bound : off + n ≤ message.bytes.size) :
      CellsOnRange t.mem before.mem (inputPayload before + BitVec.ofNat 64 off) n := by
    rw [inputAddress]
    exact entry_input_cells base s t message extent authority entry same (message.offset + off) n (by omega)
  refine ⟨original.bound, cpu.pc.trans original.pc, cpu.status.trans original.running, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply codeLoaded_of_cells original.loaded
    intro i hi
    rw [program_code_length] at hi
    have inside := caller_region_contains_offset (callerImage base) entry.imageValid i hi
    exact same _ (Or.inr (Or.inl inside))
  · rw [stackBase]; exact original.aligned
  · rw [reg0, canRead_cells_eq t.mem before.mem _ 8 header8]
    simpa only [beforeReg0] using original.offsetRead
  · rw [reg0, canRead_cells_eq t.mem before.mem _ 8 header16]
    simpa only [beforeReg0] using original.countRead
  · rw [reg0, countValue]
    simpa only [beforeReg0] using original.countValue
  · intro off n bound
    rw [stackBase]
    exact stack.read off n bound
  · intro off n bound
    rw [stackBase]
    exact stack.write off n bound
  · intro off n bound
    rw [payload, canRead_cells_eq t.mem before.mem _ n (dataCells off n bound)]
    exact original.inputRead off n bound
  · intro off n bound
    rw [reg1, canWrite_cells_eq t.mem before.mem _ n
      (entry_output_cells base s t message extent authority entry same off n bound)]
    simpa only [beforeReg1] using original.outputWrite off n bound
  · intro off n bound
    rw [canRead_cells_eq t.mem before.mem _ n (entry_image_cells base s t message extent authority entry same off n bound)]
    exact original.codeRead off n bound
  · intro i
    rw [stackBase]
    exact original.imageOutside i
  · intro i
    rw [payload, stackBase]
    exact original.inputOutside i
  · intro i
    rw [reg1, stackBase]
    simpa only [beforeReg1] using original.outputOutside i
  · intro i
    have cells : CellsOnRange t.mem before.mem (inputPayload before) message.bytes.size := by
      simpa only [BitVec.add_zero] using dataCells 0 message.bytes.size (by omega)
    rw [payload]
    exact (read8_of_cell _ (cells i.val i.isLt)).trans (original.inputBytes i)

theorem permission_view_entry_interference_projected (base : BitVec 64) (s t : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (cpu : CPUProjection t = CPUProjection (logicalState base s message))
    (same : SameCellsOn (entryProtected base s extent) t.mem (logicalState base s message).mem)
    (stack : EntryStackGrants s t.mem) : CallInputs base t message.bytes :=
  permission_view_entry_interference base s t message extent authority entry
    (entryCPUAgreement_of_projection _ _ cpu) same stack


theorem entryProtected_not_stack (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) (p : BitVec 64)
    (stack : (callerStack s).Contains p) : ¬entryProtected base s extent p := by
  intro held
  rcases held with input | image | output
  · exact entry.stackInput p ⟨stack, input⟩
  · exact entry.stackImage p ⟨stack, image⟩
  · exact entry.outputStack p ⟨output, stack⟩

theorem permission_view_entry_stack_grants (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    EntryStackGrants s (logicalState base s message).mem := by
  have original := permission_view_inputs base s message extent authority entry
  exact ⟨original.stackRead, original.stackWrite⟩

end Crypto.ARM64.Imported
