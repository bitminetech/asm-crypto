import Proofs.HMACSHA256.RISCV64EntryExecution
import Proofs.HMACSHA256.RISCV64Scheduling

namespace Crypto.HMACSHA256.RISCV64

set_option maxRecDepth 8192

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (Region BorrowScope AccessEvent CallAccess EnvironmentAccess DataRace)
open Crypto.ARM64.Imported (caller_region_contains_offset memoryBytes32)

def linkedCode (base p : Addr) : Prop :=
  (callerImage (shaAddress base)).Contains p ∨
    ∃ r : Routine, (r = entry ∨ r = key ∨ r = finish) ∧
      (p - routineAddress base r).toNat < r.image.size

def entryBorrow (base : Addr) (s : CPU) (keyExtent messageExtent capacity : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (entryKeyInput s keyExtent).Contains p ∨
    (entryMessageInput s messageExtent).Contains p
  exclusive p := (entryWorkspace s).Contains p ∨ (entryScratch s capacity).Contains p ∨ (entryMac s).Contains p

structure NativeEnvironment (scope : BorrowScope) (s : CPU) where
  permissions : ScopedPermissions scope s.mem
  schedule : MemorySchedule scope.protected
  effect : Nat → CPU → AccessEvent
  allowed : ∀ tick state, EnvironmentAccess scope (effect tick state)

abbrev EntryEnvironment (base : Addr) (s : CPU) (keyExtent messageExtent capacity : Nat) :=
  NativeEnvironment (entryBorrow base s keyExtent messageExtent capacity) s

def ProtectedEntryResult (s out : CPU) (scope : BorrowScope) (capacity : Nat) (result : HmacResult) : Prop :=
  out.reg 10#5 = BitVec.ofNat 64 result.status ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
  (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
  match result with
  | .bufferTooSmall =>
      ∀ p, scope.protected p → ¬ (entryFrame s).Contains p → out.mem.cells p = s.mem.cells p
  | .ok digest inner =>
      memoryBytes32 out.mem (s.reg 13#5) = digest.map UInt8.toBitVec ∧
        EncodedByteList out.mem (s.reg 12#5 + 8#64) inner ∧
        ∀ p, scope.protected p → ¬ (entryWorkspace s).Contains p → ¬ (entryScratchWritten s inner.bytes.size).Contains p →
          ¬ (entryMac s).Contains p → out.mem.cells p = s.mem.cells p

set_option maxHeartbeats 2600000 in
private theorem entry_result_under_borrow {base : Addr} {s serial actual : CPU} {keyValue message : ByteList}
    {keyExtent messageExtent capacity : Nat} (entry : EntryCall base s keyValue message keyExtent messageExtent capacity)
    (result : EntryResult s serial capacity (hmacSha256 keyValue message capacity))
    (same : BorrowAgreement (entryBorrow base s keyExtent messageExtent capacity).protected serial actual) :
    ProtectedEntryResult s actual (entryBorrow base s keyExtent messageExtent capacity) capacity
      (hmacSha256 keyValue message capacity) := by
  let scope := entryBorrow base s keyExtent messageExtent capacity
  have registers (r : Reg) : actual.reg r = serial.reg r := by
    unfold CPU.reg
    rw [← same.registers]
  obtain ⟨status, sp, pc, saved, state⟩ := result
  refine ⟨(registers _).trans status, (registers _).trans sp, same.pc.symm.trans pc,
    fun i => (registers _).trans (saved i), ?_⟩
  by_cases small : capacity < hmacScratchRequired message
  · simp only [hmacSha256, if_pos small] at state ⊢
    exact fun p borrowed outside => (same.memory p borrowed).symm.trans (state p outside)
  simp only [hmacSha256, if_neg small] at state ⊢
  obtain ⟨digest, inner, cells⟩ := state
  have outDigest : memoryBytes32 actual.mem (s.reg 13#5) = memoryBytes32 serial.mem (s.reg 13#5) := by
    apply Vector.ext
    intro i hi
    simp only [memoryBytes32, Vector.getElem_ofFn]
    apply read8_same
    have output := caller_region_contains_offset (entryMac s) entry.resources.macValid i hi
    exact (same.memory _ (.inr (.inr (.inr output)))).symm
  refine ⟨outDigest.trans digest, ?_, ?_⟩
  · have room : hmacScratchRequired message ≤ capacity := Nat.le_of_not_gt small
    have capacityFit : 8 + (capacity - 8) ≤ capacity := by have := entry.capacityMin; omega
    have valid : (entryInner s capacity).Valid :=
      regionSlice_valid _ _ _ entry.resources.scratchValid capacityFit
    apply inner.preserved (hmacInner_layout _ _ _ room) (extent := capacity - 8) (by rfl) valid
    intro p inside
    have scratch := regionSlice_inside _ _ _ entry.resources.scratchValid capacityFit p inside
    exact (same.memory p (.inr (.inr (.inl scratch)))).symm
  · intro p borrowed offStack offScratch offMac
    exact (same.memory p borrowed).symm.trans (cells p offStack offScratch offMac)

/-- Concurrent execution under any schedule preserving the borrowed cells.
The scheduled call has the same retired access trace as its serial execution,
the EthLib result on the owned buffers, and no race with an allowed event. -/
theorem entry_execution_concurrent {base : Addr} {s : CPU} {keyValue message : ByteList}
    {keyExtent messageExtent capacity : Nat} (caller : EntryCall base s keyValue message keyExtent messageExtent capacity)
    (environment : EntryEnvironment base s keyExtent messageExtent capacity) :
    let scope := entryBorrow base s keyExtent messageExtent capacity
    ∃ actual events,
      ScheduledExecution base environment.schedule 0 s events actual ∧
      events.length ≤ entryStepBound keyValue.bytes.size message.bytes.size capacity ∧
      EntryTrace base s keyValue message capacity events ∧
      ProtectedEntryResult s actual scope capacity (hmacSha256 keyValue message capacity) ∧
      ∀ event ∈ events, ∀ access ∈ event, CallAccess scope (memoryEvent access) ∧
        ∀ tick machine, ¬ DataRace (memoryEvent access) (environment.effect tick machine) := by
  let scope := entryBorrow base s keyExtent messageExtent capacity
  obtain ⟨serial, events, run, bound, result, trace⟩ := entry_execution_from_caller caller
  obtain ⟨actual, scheduled, same⟩ := run.scheduled_borrowed scope environment.permissions
    caller.shaCode.executable environment.schedule 0
  refine ⟨actual, events, scheduled, bound, trace, entry_result_under_borrow caller result same, ?_⟩
  intro event happened access observed
  exact ⟨run.borrowed_accesses scope environment.permissions event happened access observed,
    fun tick machine => run.no_data_race scope environment.permissions _ (environment.allowed tick machine)
      event happened access observed⟩

end Crypto.HMACSHA256.RISCV64
