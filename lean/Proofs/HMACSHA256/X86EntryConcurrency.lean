import Proofs.HMACSHA256.X86EntryExecution
import Proofs.HMACSHA256.X86FinishConcurrency

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference Crypto.Baseline
open Crypto.ARM64.Imported (caller_region_contains_offset memoryBytes32)

def entryBorrow (base : Val) (s : Cpu) (keyExtent messageExtent capacity : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (entryInputKey s keyExtent).Contains p ∨
    (entryMessage s messageExtent).Contains p ∨ (entryReturn s).Contains p
  exclusive p := (entryWorkspace s).Contains p ∨ (entryScratch s capacity).Contains p ∨ (entryMac s).Contains p

structure EntryCall (base : Val) (s : Cpu) (input message : ByteList)
    (keyExtent messageExtent capacity : Nat) (authority : Authority) : Prop where
  keyLayout : input.WellFormed
  messageLayout : message.WellFormed
  keyFits : input.size ≤ keyExtent
  messageFits : message.size ≤ messageExtent
  keySize : input.size < 2 ^ 64
  keyLength : input.bytes.size < 2 ^ 61
  messageLength : message.bytes.size < 2 ^ 61 - 64
  encodedKey : EncodedByteList (byteView s.mem) (s.regs.get .rdi) input
  encodedMessage : EncodedByteList (byteView s.mem) (s.regs.get .rsi) message
  size : s.mem.readSize .q (s.regs.get .rdx) = BitVec.ofNat 64 capacity
  minCap : 8 ≤ capacity
  cap64 : capacity < 2 ^ 64
  pc : s.rip = routineAddress base entry
  live : s.ms = none
  direction : s.flags.df = false
  resources : EntryResources base s keyExtent messageExtent capacity authority
  entryLoaded : entry.Loaded (routineAddress base entry) s.mem.read
  keyLoaded : key.Loaded (routineAddress base key) s.mem.read
  shaLoaded : ImageLoaded (shaAddress base) s.mem
  fetchAuthority : EntryFetchAuthority base s capacity authority

structure ScheduledEntryResult (scope : BorrowScope) (s out : Cpu) (input message : ByteList)
    (capacity : Nat) : Prop where
  status : out.regs.get .rax = BitVec.ofNat 64 (hmacSha256 input message capacity).status
  live : out.ms = none
  stack : out.regs.get .rsp = s.regs.get .rsp + 8#64
  link : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  registers : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  failure : capacity < hmacScratchRequired message →
    ∀ p, scope.protected p → ¬ (entrySaved s).Contains p → out.mem.read p = s.mem.read p
  digest : hmacScratchRequired message ≤ capacity →
    memoryBytes32 (byteView out.mem) (s.regs.get .rcx) =
      (EthLib.Cryptography.Hash.Hmac.hmac32 input.bytes message.bytes).map UInt8.toBitVec
  inner : hmacScratchRequired message ≤ capacity →
    EncodedByteList (byteView out.mem) (s.regs.get .rdx + 8#64) (hmacInner message (hmacKey input) capacity)
  frame : ∀ p, scope.protected p → ¬ (entryWorkspace s).Contains p →
    ¬ (⟨s.regs.get .rdx + 8#64, 88 + message.bytes.size⟩ : Region).Contains p →
    ¬ (entryMac s).Contains p → out.mem.read p = s.mem.read p

theorem entry_execution_concurrent {base : Val} {s : Cpu} {input message : ByteList}
    {keyExtent messageExtent capacity : Nat} {authority : Authority}
    (caller : EntryCall base s input message keyExtent messageExtent capacity authority)
    (rights : ScopedAuthority (entryBorrow base s keyExtent messageExtent capacity) authority)
    (environment : Environment (entryBorrow base s keyExtent messageExtent capacity)) :
    ∃ out, LinkedSchedule base authority environment 0 s (entryNativeEvents base s input message capacity) out ∧
      ScheduledEntryResult (entryBorrow base s keyExtent messageExtent capacity) s out input message capacity ∧
      (∀ e ∈ entryNativeEvents base s input message capacity, CallAccess (entryBorrow base s keyExtent messageExtent capacity) (ReportedAccess e.1 e.2.1 e.2.2)) ∧
      platformState out = platformState s := by
  let scope := entryBorrow base s keyExtent messageExtent capacity
  obtain ⟨serial, ⟨run⟩⟩ := entry_execution_from_caller base s input message keyExtent messageExtent capacity authority
    caller.keyLayout caller.messageLayout caller.keyFits caller.messageFits caller.keySize caller.keyLength
    caller.messageLength caller.encodedKey caller.encodedMessage caller.size caller.minCap caller.cap64
    caller.pc caller.live caller.direction caller.resources caller.entryLoaded caller.keyLoaded caller.shaLoaded
  have executed := run.native caller.fetchAuthority
  have owned := executed.borrowed_accesses rights
  obtain ⟨mem, scheduled, same⟩ := executed.schedule environment owned 0 s.mem (KeepsBorrowed.refl scope _)
  have result := run.result
  refine ⟨{serial with mem := mem}, scheduled,
    ⟨result.status, result.live, result.stack, result.link, result.registers,
      fun small p protectedCell offSave => (same p protectedCell).trans (result.failure small p offSave),
      ?_, ?_, fun p protectedCell offStack offScratch offOutput =>
        (same p protectedCell).trans (result.frame p offStack offScratch offOutput)⟩, owned, executed.platform⟩
  · intro room
    rw [← result.digest room]
    apply Vector.ext
    intro i hi
    simp only [memoryBytes32, Vector.getElem_ofFn, byteView_read]
    exact same _ (.inr (.inr (.inr (caller_region_contains_offset (entryMac s) caller.resources.macValid i hi))))
  · intro room
    have fits : 8 + (capacity - 8) ≤ capacity := by have := caller.minCap; omega
    apply (result.inner room).preserved (hmacInner_layout _ _ _ room) (extent := capacity - 8) (by rfl)
      (regionSlice_valid _ 8 _ caller.resources.scratchValid fits)
    intro p hit
    exact congrArg (fun byte => some (none, byte))
      (same p (.inr (.inr (.inl (regionSlice_inside _ 8 _ caller.resources.scratchValid fits p hit)))))

end Crypto.HMACSHA256.X86_64
