import Proofs.RISCV64.CallCoverage
import Proofs.ARM64.ImportedCallerEntry

namespace Crypto.RISCV64

open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset
  caller_region_read caller_region_write memoryBytes32)

def callerInput (s : CPU) (extent : Nat) : Region := ⟨s.reg 10, extent⟩
def callerOutput (s : CPU) : Region := ⟨s.reg 11, 32⟩
def callerStack (s : CPU) : Region := ⟨entryStack s, 480⟩
def callerImage (base : Addr) : Region := ⟨base, image.size⟩

/-- LP64D caller conditions for the pointer-only Linux entry. The independent
extent and live memory grants establish the accessible allocation. -/
structure CallerEntry (base : Addr) (s : CPU) (message : Crypto.Reference.ByteList) (extent : Nat) : Prop where
  layout : message.WellFormed
  size64 : message.size < 2^64
  accessible : message.size ≤ extent
  length : message.bytes.size < 2^61
  messageAligned : (s.reg 10).toNat % 8 = 0
  digestAligned : (s.reg 11).toNat % 8 = 0
  stackAligned : (s.reg 2).toNat % 16 = 0
  stackAvailable : 480 ≤ (s.reg 2).toNat
  returnAligned : (s.reg 1).toNat % 2 = 0
  inputValid : (callerInput s extent).Valid
  outputValid : (callerOutput s).Valid
  stackValid : (callerStack s).Valid
  imageValid : (callerImage base).Valid
  outputInput : (callerOutput s).Disjoint (callerInput s extent)
  outputStack : (callerOutput s).Disjoint (callerStack s)
  outputImage : (callerOutput s).Disjoint (callerImage base)
  stackInput : (callerStack s).Disjoint (callerInput s extent)
  stackImage : (callerStack s).Disjoint (callerImage base)
  inputRead : ∀ p, (callerInput s extent).Contains p → s.mem.canRead p 1 = true
  stackRead : ∀ p, (callerStack s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (callerStack s).Contains p → s.mem.canWrite p 1 = true
  outputWrite : ∀ p, (callerOutput s).Contains p → s.mem.canWrite p 1 = true
  sizeValue : s.mem.read64 (s.reg 10) = BitVec.ofNat 64 message.size
  offsetValue : s.mem.read64 (s.reg 10 + 8) = BitVec.ofNat 64 message.offset
  countValue : s.mem.read64 (s.reg 10 + 16) = BitVec.ofNat 64 message.bytes.size
  bytes : ∀ i : Fin message.bytes.size,
    s.mem.read8 (s.reg 10 + BitVec.ofNat 64 (message.offset + i.val)) = (message.bytes.get! i.val).toBitVec
  pc : s.pc = base
  loaded : ImageLoaded base s.mem
  imageAligned : base.toNat % 8 = 0
  imageRead : s.mem.canRead base image.size = true
  textExecute : s.mem.canExec base codeEnd = true
  imageReadOnly : ImageReadOnly base s.mem

private theorem entry_stack_alignment (s : CPU) (aligned : (s.reg 2).toNat % 16 = 0) :
    (entryStack s).toNat % 8 = 0 := by
  unfold entryStack
  rw [BitVec.toNat_sub]
  rw [show (480 : Addr).toNat = 480 from rfl]
  omega

theorem CallerEntry.output_outside {base : Addr} {s : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) (i : Fin 32) :
    480 ≤ (s.reg 11 + BitVec.ofNat 64 i.val - entryStack s).toNat := by
  apply caller_outside_delta (callerStack s) entry.stackValid
  intro onStack
  exact entry.outputStack _ ⟨caller_region_contains_offset (callerOutput s) entry.outputValid i.val i.isLt, onStack⟩

theorem CallerEntry.decoded_layout {base : Addr} {s : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) :
    CallEntry base s message.bytes ∧ CallRegionPermissions base s message.bytes.size := by
  obtain ⟨offsetMinimum, offsetAligned, offsetFits, countFits⟩ := entry.layout
  have headerFits : 24 ≤ extent := by have := entry.accessible; omega
  have payloadFits : message.offset + message.bytes.size ≤ extent := by have := entry.accessible; omega
  have payload : inputPayload s = s.reg 10 + BitVec.ofNat 64 message.offset := by
    unfold inputPayload
    rw [entry.offsetValue]
  have inputAddress (i : Nat) : inputPayload s + BitVec.ofNat 64 i =
      s.reg 10 + BitVec.ofNat 64 (message.offset + i) := by
    rw [payload, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨⟨entry.pc, entry.length, entry.loaded, entry.countValue, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, entry.imageRead, ?_, entry_stack_alignment s entry.stackAligned,
      entry.messageAligned, ?_, entry.imageAligned, entry.digestAligned⟩⟩
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro onStack
    have inside := caller_region_contains_offset (callerInput s extent) entry.inputValid (8+i.val)
      (by change _ < extent; have := i.isLt; omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at inside
    exact entry.stackInput _ ⟨onStack, inside⟩
  · intro i hi
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro onStack
    exact entry.stackImage _ ⟨onStack, caller_region_contains_offset (callerImage base) entry.imageValid i hi⟩
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro onStack
    apply entry.stackInput _ ⟨onStack, ?_⟩
    rw [inputAddress]
    exact caller_region_contains_offset (callerInput s extent) entry.inputValid _
      (by change _ < extent; have := i.isLt; omega)
  · intro i
    rw [inputAddress]
    exact entry.bytes i
  · simpa only [callerStack, BitVec.add_zero] using
      caller_region_read s.mem (callerStack s) entry.stackValid entry.stackRead 0 480 (by change 0+480 ≤ 480; decide)
  · simpa only [callerStack, BitVec.add_zero] using
      caller_region_write s.mem (callerStack s) entry.stackValid entry.stackWrite 0 480 (by change 0+480 ≤ 480; decide)
  · simpa only [callerInput, BitVec.add_zero] using
      caller_region_read s.mem (callerInput s extent) entry.inputValid entry.inputRead 0 24 (by exact headerFits)
  · rw [payload]
    exact caller_region_read s.mem (callerInput s extent) entry.inputValid entry.inputRead
      message.offset message.bytes.size payloadFits
  · simpa only [callerOutput, BitVec.add_zero] using
      caller_region_write s.mem (callerOutput s) entry.outputValid entry.outputWrite 0 32 (by change 0+32 ≤ 32; decide)
  · have offset64 : message.offset < 2^64 := by have := entry.size64; omega
    rw [payload, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offset64,
      Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^64), Nat.add_mod, entry.messageAligned, offsetAligned]

private theorem aligned_return (addr : Addr) (even : addr.toNat % 2 = 0) : addr &&& ~~~(1 : Addr) = addr := by
  have bit0 : addr &&& (1 : Addr) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change addr.toNat &&& (2^1-1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact even
  have ones : (1 : Addr) ||| ~~~(1 : Addr) = BitVec.allOnes 64 := by decide
  calc
    addr &&& ~~~(1 : Addr) = (addr &&& (1 : Addr)) ||| (addr &&& ~~~(1 : Addr)) := by
      rw [bit0]
      exact BitVec.zero_or.symm
    _ = addr &&& ((1 : Addr) ||| ~~~(1 : Addr)) := BitVec.and_or_distrib_left.symm
    _ = addr := by rw [ones, BitVec.and_allOnes]

theorem caller_sha256 (base : Addr) (s : CPU) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out, runUntilReturn base s (callSteps message.bytes.size) = some out ∧
      out.pc = s.reg 1 ∧ out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 ∧
      savedRegisters out = savedRegisters s ∧
      memoryBytes32 out.mem (s.reg 11) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec ∧
      (∀ p, ¬ (callerStack s).Contains p → ¬ (callerOutput s).Contains p → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨inputs, grants⟩ := entry.decoded_layout
  obtain ⟨out, done, pc, status, stack, saved, bytes, frame⟩ := run_sha256_from_regions base s message.bytes
    inputs grants entry.output_outside entry.textExecute entry.imageReadOnly
  exact ⟨out, done, pc.trans (aligned_return _ entry.returnAligned), status, stack, saved, bytes, fun p hs hd =>
    frame p (caller_outside_delta _ entry.stackValid p hs) (caller_outside_delta _ entry.outputValid p hd)⟩

end Crypto.RISCV64
