import Proofs.ARM64.ImportedWholeCall
import Proofs.Baseline

/-!
Derive native CallInputs from a typed ByteList, an independently supplied
accessible extent, complete-region logical grants and separation, truthful
header/data bytes, and initial ABI/loading facts.
-/

namespace Crypto.ARM64.Imported
open Crypto.Baseline

theorem caller_read_of_bytes (m : Arm64.Memory) (p : BitVec 64) (n : Nat)
    (bytes : ∀ i, i < n → m.canRead (p + BitVec.ofNat 64 i) 1 = true) :
    m.canRead p n = true := by
  induction n generalizing p with
  | zero => simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree]
  | succ n ih =>
    have first := bytes 0 (by omega)
    have rest := ih (p + 1#64) (by
      intro i hi
      have value := bytes (i + 1) (by omega)
      have address : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
        rw [BitVec.ofNat_add]
        ac_rfl
      rw [address]
      exact value)
    simp only [BitVec.add_zero, Arm64.Memory.canRead, Arm64.Memory.allPerm,
      Arm64.Memory.allNoLazyFree, Bool.and_true, Bool.and_eq_true] at first rest ⊢
    exact ⟨⟨first.1, rest.1⟩, first.2, rest.2⟩

theorem caller_write_of_bytes (m : Arm64.Memory) (p : BitVec 64) (n : Nat)
    (bytes : ∀ i, i < n → m.canWrite (p + BitVec.ofNat 64 i) 1 = true) :
    m.canWrite p n = true := by
  induction n generalizing p with
  | zero => simp [Arm64.Memory.canWrite, Arm64.Memory.allPerm]
  | succ n ih =>
    have first := bytes 0 (by omega)
    have rest := ih (p + 1#64) (by
      intro i hi
      have value := bytes (i + 1) (by omega)
      have address : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
        rw [BitVec.ofNat_add]
        ac_rfl
      rw [address]
      exact value)
    simpa only [BitVec.add_zero, Arm64.Memory.canWrite, Arm64.Memory.allPerm,
      Bool.and_true, Bool.and_eq_true] using And.intro first rest

theorem caller_region_contains_offset (region : Region) (valid : region.Valid)
    (i : Nat) (bound : i < region.bytes) : region.Contains (region.base + BitVec.ofNat 64 i) := by
  have iv : i < 2 ^ 64 := by unfold Region.Valid at valid; omega
  have sum : region.base.toNat + i < 2 ^ 64 := by unfold Region.Valid at valid; omega
  have value : (region.base + BitVec.ofNat 64 i).toNat = region.base.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt iv, Nat.mod_eq_of_lt sum]
  unfold Region.Contains
  rw [value]
  omega

theorem caller_region_read (m : Arm64.Memory) (region : Region) (valid : region.Valid)
    (grant : ∀ p, region.Contains p → m.canRead p 1 = true)
    (off n : Nat) (bound : off + n ≤ region.bytes) :
    m.canRead (region.base + BitVec.ofNat 64 off) n = true := by
  apply caller_read_of_bytes
  intro i hi
  have cell := grant _ (caller_region_contains_offset region valid (off + i) (by omega))
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem caller_region_write (m : Arm64.Memory) (region : Region) (valid : region.Valid)
    (grant : ∀ p, region.Contains p → m.canWrite p 1 = true)
    (off n : Nat) (bound : off + n ≤ region.bytes) :
    m.canWrite (region.base + BitVec.ofNat 64 off) n = true := by
  apply caller_write_of_bytes
  intro i hi
  have cell := grant _ (caller_region_contains_offset region valid (off + i) (by omega))
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem caller_outside_delta (region : Region) (valid : region.Valid) (p : BitVec 64)
    (outside : ¬region.Contains p) : region.bytes ≤ (p - region.base).toNat := by
  by_contra h
  have inside := caller_region_contains_offset region valid (p - region.base).toNat (by omega)
  have address := address_reconstruct region.base p
  rw [address] at inside
  exact outside inside


def callerInput (s : Arm64.State) (extent : Nat) : Region := ⟨s.readReg64 .x0, extent⟩
def callerOutput (s : Arm64.State) : Region := ⟨s.readReg64 .x1, 32⟩
def callerStack (s : Arm64.State) : Region := ⟨entryStack s, 416⟩
def callerImage (base : BitVec 64) : Region := ⟨base, 896⟩

/-- Typed caller-entry bridge under the imported logical memory view.
The independently supplied extent is not inferred from the embedded size.
Grants describe the complete borrowed regions, including unused input room.
Physical grants, tagged-address interpretation and lifetime follow the target
profile; NativeStatement combines caller entry with the remaining guarantees. -/
structure CallerEntry (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) : Prop where
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
  inputRead : ∀ p, (callerInput s extent).Contains p → s.mem.canRead p 1 = true
  stackRead : ∀ p, (callerStack s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (callerStack s).Contains p → s.mem.canWrite p 1 = true
  outputWrite : ∀ p, (callerOutput s).Contains p → s.mem.canWrite p 1 = true
  sizeValue : s.mem.read64 (s.readReg64 .x0) = BitVec.ofNat 64 message.size
  offsetValue : s.mem.read64 (s.readReg64 .x0 + 8#64) = BitVec.ofNat 64 message.offset
  countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 message.bytes.size
  bytes : ∀ i : Fin message.bytes.size,
    s.mem.read8 (s.readReg64 .x0 + BitVec.ofNat 64 (message.offset + i.val)) =
      (message.bytes.get! i.val).toBitVec
  pc : s.pc = base
  running : s.status = .Running
  loaded : (program base).CodeLoaded s.mem

theorem caller_stack_alignment (s : Arm64.State) (aligned : s.sp.toNat % 16 = 0)
    (available : 416 ≤ s.sp.toNat) : ((entryStack s &&& 15#64) == 0#64) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.toNat_inj.mp
  change (entryStack s).toNat &&& 15 = 0
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have sub : (entryStack s).toNat = s.sp.toNat - 416 := by
    unfold entryStack
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [sub]
  omega

theorem caller_entry_inputs (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) : CallInputs base s message.bytes := by
  have wf := entry.layout
  rcases wf with ⟨offsetMinimum, offsetAligned, offsetSize, countSize⟩
  have dataExtent : message.offset + message.bytes.size ≤ extent := by
    have := entry.accessible
    omega
  have payload : inputPayload s = s.readReg64 .x0 + BitVec.ofNat 64 message.offset := by
    unfold inputPayload
    rw [entry.offsetValue]
  have inputAddress (i : Nat) : inputPayload s + BitVec.ofNat 64 i =
      s.readReg64 .x0 + BitVec.ofNat 64 (message.offset + i) := by
    rw [payload, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨entry.length, entry.pc, entry.running, entry.loaded,
    caller_stack_alignment s entry.stackAligned entry.stackAvailable, ?_, ?_, entry.countValue,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact caller_region_read s.mem (callerInput s extent) entry.inputValid entry.inputRead 8 8 (by change _ ≤ extent; have := entry.headerFits; omega)
  · exact caller_region_read s.mem (callerInput s extent) entry.inputValid entry.inputRead 16 8 (by change _ ≤ extent; have := entry.headerFits; omega)
  · intro off n bound
    exact caller_region_read s.mem (callerStack s) entry.stackValid entry.stackRead off n bound
  · intro off n bound
    exact caller_region_write s.mem (callerStack s) entry.stackValid entry.stackWrite off n bound
  · intro off n bound
    rw [inputAddress]
    exact caller_region_read s.mem (callerInput s extent) entry.inputValid entry.inputRead
      (message.offset + off) n (by change _ ≤ extent; omega)
  · intro off n bound
    exact caller_region_write s.mem (callerOutput s) entry.outputValid entry.outputWrite off n bound
  · intro off n bound
    apply caller_read_of_bytes
    intro i hi
    have cell := (codeLoaded_iff.mp entry.loaded).2.2 (off + i) (by rw [program_code_length]; omega)
    have address : base + BitVec.ofNat 64 off + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (off + i) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    have permission := cell.2.1
    have noLazy := cell.2.2
    change s.mem.perm (base + BitVec.ofNat 64 (off + i)) = some Arm64.Perm.rx at permission
    change s.mem.isLazyFree (base + BitVec.ofNat 64 (off + i)) = false at noLazy
    simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree,
      permission, noLazy, Arm64.Perm.rx]
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    exact entry.stackImage _ ⟨inside, caller_region_contains_offset (callerImage base) entry.imageValid i.val i.isLt⟩
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    apply entry.stackInput _ ⟨inside, ?_⟩
    rw [inputAddress]
    exact caller_region_contains_offset (callerInput s extent) entry.inputValid (message.offset + i.val) (by change _ < extent; have := i.isLt; omega)
  · intro i
    apply caller_outside_delta (callerStack s) entry.stackValid
    intro inside
    exact entry.outputStack _ ⟨caller_region_contains_offset (callerOutput s) entry.outputValid i.val i.isLt, inside⟩
  · intro i
    rw [inputAddress]
    exact entry.bytes i

end Crypto.ARM64.Imported
