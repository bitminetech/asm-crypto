import Proofs.ARM64.ImportedConcurrentCall
import Proofs.ARM64.ImportedWholeCallFrame

/-!
Readonly input/image byte preservation for the actual scheduled SHA-256 call.
The complete independently supplied input extent and image remain borrowed.
The native serial frame is applied after the first environment step and then
transported through that step's static cells and the final scheduled cells.
Unborrowed memory, deallocated stack bytes and unrelated global state may
advance; no old unowned snapshot is restored or claimed unchanged.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem concurrent_serial_entry_inputs (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent) :
    CallInputs base (concurrentSerialStart environment message) message.bytes := by
  let view := logicalState base s message
  let start := concurrentSerialStart environment message
  have cpu : CPUProjection start = CPUProjection view := environment.cpu 0 view
  have same : SameCellsOn (entryProtected base s extent) start.mem view.mem := by
    intro p inside
    exact (environment.staticCells 0 view p inside).symm
  have stack := environment.reservation 0 view
    (permission_view_entry_stack_grants base s message extent authority entry)
  exact permission_view_entry_interference_projected base s start message extent authority entry cpu same stack

theorem concurrent_readonly_borrow_byte (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment)
    (p : BitVec 64) (borrowed : (staticBorrowScope base s extent).protected p)
    (outsideStack : ¬(callerStack s).Contains p) (outsideOutput : ¬(callerOutput s).Contains p) :
    call.schedule.actualOut.mem.read8 p = s.mem.read8 p := by
  let start := concurrentSerialStart environment message
  let view := logicalState base s message
  have inputs := concurrent_serial_entry_inputs base s message extent authority entry environment
  have cpu : CPUProjection start = CPUProjection view := call.rebasedCPU
  have context := entryCPUAgreement_of_projection view start cpu
  have sp : start.sp = s.sp := context.sp
  have output : start.readReg64 .x1 = s.readReg64 .x1 := context.read .x1
  have bottom : entryStack start = entryStack s := by
    unfold entryStack
    rw [sp]
  have frame := whole_call_memory_frame base start message.bytes inputs call.serialOut call.serialExecuted
  have serialCell : call.serialOut.mem.cells p = start.mem.cells p := by
    apply frame p
    · rw [bottom]
      exact caller_outside_delta (callerStack s) entry.stackValid p outsideStack
    · rw [output]
      exact caller_outside_delta (callerOutput s) entry.outputValid p outsideOutput
  have finalByte : call.schedule.actualOut.mem.read8 p = call.serialOut.mem.read8 p :=
    (read8_of_cell p (call.schedule.cells p borrowed)).symm
  have serialByte : call.serialOut.mem.read8 p = start.mem.read8 p := read8_of_cell p serialCell
  have entryCell : view.mem.cells p = start.mem.cells p :=
    environment.staticCells 0 view p ((static_borrow_protected base s extent p).mp borrowed)
  have entryByte : start.mem.read8 p = view.mem.read8 p := (read8_of_cell p entryCell).symm
  exact finalByte.trans (serialByte.trans (entryByte.trans (logicalMemory_read8 base s message p)))

structure ConcurrentReadonlyBorrows (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) : Prop where
  input : ∀ p, (callerInput s extent).Contains p → call.schedule.actualOut.mem.read8 p = s.mem.read8 p
  image : ∀ p, (callerImage base).Contains p → call.schedule.actualOut.mem.read8 p = s.mem.read8 p

theorem concurrent_call_readonly_borrows (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent)
    (call : ConcurrentCallCore base s message extent authority environment) :
    ConcurrentReadonlyBorrows base s message extent authority environment call := by
  refine ⟨?_, ?_⟩
  · intro p inside
    exact concurrent_readonly_borrow_byte base s message extent authority entry environment call p
      (Or.inl (Or.inl inside)) (fun held => entry.stackInput p ⟨held, inside⟩)
      (fun held => entry.outputInput p ⟨held, inside⟩)
  · intro p inside
    exact concurrent_readonly_borrow_byte base s message extent authority entry environment call p
      (Or.inl (Or.inr inside)) (fun held => entry.stackImage p ⟨held, inside⟩)
      (fun held => entry.outputImage p ⟨held, inside⟩)

theorem sha256_concurrent_readonly_borrows (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (environment : DynamicEnvironment base s extent) :
    ∃ call : ConcurrentCallCore base s message extent authority environment,
      ConcurrentReadonlyBorrows base s message extent authority environment call := by
  obtain ⟨call⟩ := sha256_concurrent_call_core base s message extent authority entry environment
  exact ⟨call, concurrent_call_readonly_borrows base s message extent authority entry environment call⟩

end Crypto.ARM64.Imported
