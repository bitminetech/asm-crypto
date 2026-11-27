import Proofs.HMACSHA256.EncodedByteList
import Proofs.HMACSHA256.RISCV64Program
import Proofs.RISCV64.Caller

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (caller_region_contains_offset)

structure ShaCode (base : Addr) (m : Memory) : Prop where
  loaded : ImageLoaded base m
  aligned : base.toNat % 8 = 0
  valid : (callerImage base).Valid
  readable : m.canRead base Crypto.RISCV64.image.size = true
  executable : m.canExec base codeEnd = true
  readonly : ImageReadOnly base m

theorem allPerm_eq_of_perm {before after : Memory} (perm : ∀ p, after.perm p = before.perm p)
    (test : Option Arm64.Perm → Bool) (p : Addr) (n : Nat) :
    after.allPerm test p n = before.allPerm test p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [Arm64.Memory.allPerm, perm, ih]

theorem ShaCode.preserved {base : Addr} {before after : Memory} (code : ShaCode base before)
    (cells : ∀ p, (callerImage base).Contains p → after.cells p = before.cells p)
    (perm : ∀ p, after.perm p = before.perm p)
    (read : ∀ p n, before.canRead p n = true → after.canRead p n = true) :
    ShaCode base after where
  loaded := by
    intro i within
    unfold Arm64.Memory.read8
    have inside : (callerImage base).Contains (base + BitVec.ofNat 64 i) :=
      caller_region_contains_offset (callerImage base) code.valid i within
    rw [cells _ inside]
    exact code.loaded i within
  aligned := code.aligned
  valid := code.valid
  readable := read _ _ code.readable
  executable := by
    unfold Arm64.Memory.canExec
    rw [allPerm_eq_of_perm perm]
    exact code.executable
  readonly := by
    intro i within
    simp only [perm]
    exact code.readonly i within

/-- Regions and grants at the SHA-256 call boundary. The same environment
serves both calls in the finishing helper and the long-key call. -/
structure ShaResources (base : Addr) (s : CPU) (extent : Nat) : Prop where
  inputAligned : (s.reg 10).toNat % 8 = 0
  outputAligned : (s.reg 11).toNat % 8 = 0
  stackAligned : (s.reg 2).toNat % 16 = 0
  stackAvailable : 480 ≤ (s.reg 2).toNat
  inputValid : (callerInput s extent).Valid
  outputValid : (callerOutput s).Valid
  outputInput : (callerOutput s).Disjoint (callerInput s extent)
  outputStack : (callerOutput s).Disjoint (callerStack s)
  outputImage : (callerOutput s).Disjoint (callerImage base)
  stackInput : (callerStack s).Disjoint (callerInput s extent)
  stackImage : (callerStack s).Disjoint (callerImage base)
  inputRead : ∀ p, (callerInput s extent).Contains p → s.mem.canRead p 1 = true
  outputWrite : ∀ p, (callerOutput s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (callerStack s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (callerStack s).Contains p → s.mem.canWrite p 1 = true

theorem ShaResources.preserved {base : Addr} {before after : CPU} {extent : Nat}
    (grants : ShaResources base before extent)
    (a0 : after.reg 10 = before.reg 10) (a1 : after.reg 11 = before.reg 11)
    (sp : after.reg 2 = before.reg 2)
    (perm : ∀ p, after.mem.perm p = before.mem.perm p)
    (read : ∀ p n, before.mem.canRead p n = true → after.mem.canRead p n = true) :
    ShaResources base after extent := by
  change after.reg 10#5 = before.reg 10#5 at a0
  change after.reg 11#5 = before.reg 11#5 at a1
  change after.reg 2#5 = before.reg 2#5 at sp
  have input : callerInput after extent = callerInput before extent := by simp [callerInput, a0]
  have output : callerOutput after = callerOutput before := by simp [callerOutput, a1]
  have stack : callerStack after = callerStack before := by simp [callerStack, entryStack, sp]
  have writable (p : Addr) : after.mem.canWrite p 1 = before.mem.canWrite p 1 :=
    allPerm_eq_of_perm perm _ _ _
  exact {
    inputAligned := by
      have beforeEq : after.reg 10 = before.reg 10 := a0
      rw [beforeEq]
      exact grants.inputAligned
    outputAligned := by
      have beforeEq : after.reg 11 = before.reg 11 := a1
      rw [beforeEq]
      exact grants.outputAligned
    stackAligned := by
      have beforeEq : after.reg 2 = before.reg 2 := sp
      rw [beforeEq]
      exact grants.stackAligned
    stackAvailable := by
      have beforeEq : after.reg 2 = before.reg 2 := sp
      rw [beforeEq]
      exact grants.stackAvailable
    inputValid := by rw [input]; exact grants.inputValid
    outputValid := by rw [output]; exact grants.outputValid
    outputInput := by rw [input, output]; exact grants.outputInput
    outputStack := by rw [output, stack]; exact grants.outputStack
    outputImage := by rw [output]; exact grants.outputImage
    stackInput := by rw [stack, input]; exact grants.stackInput
    stackImage := by rw [stack]; exact grants.stackImage
    inputRead := fun p inside => read _ _ (grants.inputRead p (input ▸ inside))
    outputWrite := fun p inside => (writable p).trans (grants.outputWrite p (output ▸ inside))
    stackRead := fun p inside => read _ _ (grants.stackRead p (stack ▸ inside))
    stackWrite := fun p inside => (writable p).trans (grants.stackWrite p (stack ▸ inside))
  }

private theorem callee_stack_valid (s : CPU) (available : 480 ≤ (s.reg 2).toNat) :
    (callerStack s).Valid := by
  change (s.reg 2 - (480 : Addr)).toNat + 480 ≤ 2 ^ 64
  rw [BitVec.toNat_sub]
  have within := (s.reg 2).isLt
  change (2 ^ 64 - 480 + (s.reg 2).toNat) % 2 ^ 64 + 480 ≤ 2 ^ 64
  omega

/-- Establish the existing SHA-256 theorem's entry predicate from an
independent extent, the bytes actually serialized by the caller, and the
callee's resources. The FIPS bound applies to the payload length, while
the independently mapped extent supplies the storage for the entire list. -/
theorem establish_sha_entry {base : Addr} {s : CPU} {message : ByteList} {extent : Nat}
    (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (sizeBound : message.size < 2 ^ 64) (lengthBound : message.bytes.size < 2 ^ 61)
    (encoding : EncodedByteList s.mem (s.reg 10) message)
    (resources : ShaResources base s extent) (code : ShaCode base s.mem)
    (pc : s.pc = base) (returnAligned : (s.reg 1).toNat % 2 = 0) :
    CallerEntry base s message extent where
  layout := layout
  size64 := sizeBound
  accessible := accessible
  length := lengthBound
  messageAligned := resources.inputAligned
  digestAligned := resources.outputAligned
  stackAligned := resources.stackAligned
  stackAvailable := resources.stackAvailable
  returnAligned := returnAligned
  inputValid := resources.inputValid
  outputValid := resources.outputValid
  stackValid := callee_stack_valid s resources.stackAvailable
  imageValid := code.valid
  outputInput := resources.outputInput
  outputStack := resources.outputStack
  outputImage := resources.outputImage
  stackInput := resources.stackInput
  stackImage := resources.stackImage
  inputRead := resources.inputRead
  stackRead := resources.stackRead
  stackWrite := resources.stackWrite
  outputWrite := resources.outputWrite
  sizeValue := encoding.size
  offsetValue := encoding.offset
  countValue := encoding.count
  bytes := by
    intro i
    have arrayBytes (a : ByteArray) (index : Nat) : a.get! index = a.data[index]! := by cases a; rfl
    have value := encoding.bytes i
    rw [getElem!_pos message.bytes i.val i.isLt] at value
    rw [arrayBytes, getElem!_pos message.bytes.data i.val i.isLt]
    exact value
  pc := pc
  loaded := code.loaded
  imageAligned := code.aligned
  imageRead := code.readable
  textExecute := code.executable
  imageReadOnly := code.readonly

end Crypto.HMACSHA256.RISCV64
