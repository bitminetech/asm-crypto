import Proofs.HMACSHA256.RISCV64EntryResources

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.ARM64.Imported (memoryBytes32)

/-- Layout and loader assumptions at the public RV64 HMAC entry. The readable
and writable extents are established independently of the encoded sizes. -/
structure EntryCall (base : Addr) (s : CPU) (keyValue message : ByteList)
    (keyExtent messageExtent capacity : Nat) : Prop where
  resources : EntryResources base s keyExtent messageExtent capacity
  pc : s.pc = routineAddress base entry
  returnsAligned : (s.reg 1#5).toNat % 2 = 0
  keyLayout : keyValue.WellFormed
  messageLayout : message.WellFormed
  keySize : keyValue.size < 2 ^ 64
  messageSize : message.size < 2 ^ 64
  keyFits : keyValue.size ≤ keyExtent
  messageFits : message.size ≤ messageExtent
  keyLength : keyValue.bytes.size < 2 ^ 61
  messageLength : message.bytes.size < 2 ^ 61 - 64
  keyEncoded : EncodedByteList s.mem (s.reg 10#5) keyValue
  messageEncoded : EncodedByteList s.mem (s.reg 11#5) message
  capacityAt : s.mem.read64 (s.reg 12#5) = BitVec.ofNat 64 capacity
  capacityMin : 8 ≤ capacity
  capacitySize : capacity < 2 ^ 64
  entryCode : RoutineGrant base entry s.mem
  keyCode : RoutineGrant base key s.mem
  finishCode : RoutineGrant base finish s.mem
  shaCode : ShaCode (shaAddress base) s.mem

def entryStepBound (keyCount messageCount capacity : Nat) : Nat :=
  if capacity < 96 + messageCount then 40 else
    170 + keyStepBound keyCount + 8 * (messageCount / 8) + 7 * (messageCount % 8) +
      callSteps (64 + messageCount) + callSteps 96

def EntryResult (s out : CPU) (capacity : Nat) (result : HmacResult) : Prop :=
  out.reg 10#5 = BitVec.ofNat 64 result.status ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
  (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
  match result with
  | .bufferTooSmall =>
      ∀ p, ¬ (entryFrame s).Contains p → out.mem.cells p = s.mem.cells p
  | .ok digest inner =>
      memoryBytes32 out.mem (s.reg 13#5) = digest.map UInt8.toBitVec ∧
        EncodedByteList out.mem (s.reg 12#5 + 8#64) inner ∧
        ∀ p, ¬ (entryWorkspace s).Contains p → ¬ (entryScratchWritten s inner.bytes.size).Contains p →
          ¬ (entryMac s).Contains p → out.mem.cells p = s.mem.cells p

def EntryTrace (base : Addr) (s : CPU) (keyValue message : ByteList) (capacity : Nat)
    (events : List (List Access)) : Prop :=
  if capacity < 96 + message.bytes.size then events = entrySmallEvents base s (BitVec.ofNat 64 capacity)
  else EntrySuccessTrace base s keyValue message capacity events

/-- The RV64 public entry computes the EthLib reference or returns the
capacity status. The execution checks every fetch and data access, including
all three possible SHA-256 calls, through the native return. -/
theorem entry_execution_from_caller {base : Addr} {s : CPU} {keyValue message : ByteList}
    {keyExtent messageExtent capacity : Nat}
    (caller : EntryCall base s keyValue message keyExtent messageExtent capacity) :
    ∃ out events, ProgramExecution base s events out ∧
      events.length ≤ entryStepBound keyValue.bytes.size message.bytes.size capacity ∧
      EntryResult s out capacity (hmacSha256 keyValue message capacity) ∧
      EntryTrace base s keyValue message capacity events := by
  by_cases short : capacity < 96 + message.bytes.size
  · have representable : message.bytes.size < 2 ^ 64 := by have := caller.messageLength; omega
    obtain ⟨out, run, bound, status, sp, link, saved, keep⟩ :=
      caller.resources.undersized_execution message caller.messageLayout caller.messageFits
        caller.messageEncoded caller.capacityAt caller.capacityMin caller.capacitySize representable short
        caller.pc caller.entryCode caller.returnsAligned
    refine ⟨out, _, run, by simpa only [entryStepBound, if_pos short] using bound, ?_, ?_⟩
    · simp only [hmacSha256, hmacScratchRequired, if_pos short, EntryResult, HmacResult.status]
      exact ⟨status, sp, link, saved, keep⟩
    · simp only [EntryTrace, if_pos short]
  have room : 96 + message.bytes.size ≤ capacity := Nat.le_of_not_gt short
  obtain ⟨out, events, run, bound, status, sp, link, saved, digest, inner, keep, trace⟩ :=
    caller.resources.successful_execution keyValue message caller.keyLayout caller.messageLayout
      caller.keyFits caller.messageFits caller.keySize caller.keyLength caller.messageLength caller.keyEncoded
      caller.messageEncoded caller.capacityAt room caller.capacitySize caller.pc caller.entryCode caller.keyCode
      caller.finishCode caller.shaCode caller.returnsAligned
  refine ⟨out, events, run, by simpa only [entryStepBound, if_neg short] using bound, ?_, ?_⟩
  · simp only [hmacSha256, hmacScratchRequired, if_neg short, EntryResult, HmacResult.status]
    exact ⟨status, sp, link, saved, digest, inner, by simpa only [hmacInner_length] using keep⟩
  · simpa only [EntryTrace, if_neg short] using trace

end Crypto.HMACSHA256.RISCV64
