import Proofs.Baseline
import Proofs.ARM64.ImportedCallerEntry

namespace Crypto.HMACSHA256

open Crypto.Baseline
open Crypto.ARM64.Imported (caller_region_contains_offset)

def regionSlice (region : Region) (offset bytes : Nat) : Region :=
  ⟨region.base + BitVec.ofNat 64 offset, bytes⟩

theorem regionSlice_valid (region : Region) (offset bytes : Nat)
    (valid : region.Valid) (fits : offset + bytes ≤ region.bytes) :
    (regionSlice region offset bytes).Valid := by
  unfold Region.Valid at valid ⊢
  by_cases empty : bytes = 0
  · have := (regionSlice region offset bytes).base.isLt
    change (regionSlice region offset bytes).base.toNat + bytes ≤ 2 ^ 64
    omega
  · simp only [regionSlice, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : region.base.toNat + offset < 2 ^ 64)]
    omega

theorem regionSlice_inside (region : Region) (offset bytes : Nat)
    (valid : region.Valid) (fits : offset + bytes ≤ region.bytes) (address : Address)
    (inside : (regionSlice region offset bytes).Contains address) :
    region.Contains address := by
  unfold Region.Contains at inside ⊢
  unfold Region.Valid at valid
  have positive : 0 < bytes := by
    change (regionSlice region offset bytes).base.toNat ≤ address.toNat ∧
      address.toNat < (regionSlice region offset bytes).base.toNat + bytes at inside
    omega
  simp only [regionSlice, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : region.base.toNat + offset < 2 ^ 64)] at inside
  omega

theorem regionSlice_subset (region : Region) (a aLen b bLen : Nat)
    (valid : region.Valid) (start : b ≤ a) (ending : a + aLen ≤ b + bLen)
    (fits : b + bLen ≤ region.bytes) (p : Address)
    (hit : (regionSlice region a aLen).Contains p) : (regionSlice region b bLen).Contains p := by
  unfold Region.Contains at hit ⊢
  unfold Region.Valid at valid
  change (regionSlice region a aLen).base.toNat ≤ p.toNat ∧
    p.toNat < (regionSlice region a aLen).base.toNat + aLen at hit
  change (regionSlice region b bLen).base.toNat ≤ p.toNat ∧
    p.toNat < (regionSlice region b bLen).base.toNat + bLen
  have size : 0 < aLen := by omega
  simp only [regionSlice, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : region.base.toNat + a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : region.base.toNat + b < 2 ^ 64)] at hit ⊢
  omega

/-- Two slices with ordered byte extents of the same allocation do not alias. -/
theorem regionSlices_disjoint (region : Region) (a aLen b bLen : Nat)
    (valid : region.Valid) (ordered : a + aLen ≤ b) (fits : b + bLen ≤ region.bytes) :
    (regionSlice region a aLen).Disjoint (regionSlice region b bLen) := by
  intro addr hits
  obtain ⟨first, second⟩ := hits
  unfold Region.Contains at first second
  unfold Region.Valid at valid
  have an : 0 < aLen := by
    change (regionSlice region a aLen).base.toNat ≤ addr.toNat ∧
      addr.toNat < (regionSlice region a aLen).base.toNat + aLen at first
    omega
  have bn : 0 < bLen := by
    change (regionSlice region b bLen).base.toNat ≤ addr.toNat ∧
      addr.toNat < (regionSlice region b bLen).base.toNat + bLen at second
    omega
  simp only [regionSlice, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : region.base.toNat + a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : region.base.toNat + b < 2 ^ 64)] at first second
  omega

theorem disjoint_subsets {a b c d : Region} (separated : a.Disjoint b)
    (inA : ∀ p, c.Contains p → a.Contains p) (inB : ∀ p, d.Contains p → b.Contains p) :
    c.Disjoint d := fun p hit => separated p ⟨inA p hit.1, inB p hit.2⟩

theorem frame_base_end (sp : BitVec 64) (bytes : Nat) (reserved : bytes ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 bytes).toNat + bytes = sp.toNat := by
  have within := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64)]
  omega

/-- The half-open native stack allocation immediately below the incoming SP. -/
def stackRegion (sp : BitVec 64) (size : Nat) : Region :=
  ⟨sp - BitVec.ofNat 64 size, size⟩

theorem stackRegion_valid (sp : BitVec 64) (size : Nat) (available : size ≤ sp.toNat) :
    (stackRegion sp size).Valid := by
  change (sp - BitVec.ofNat 64 size).toNat + size ≤ 2 ^ 64
  rw [frame_base_end sp size available]
  exact sp.isLt.le

theorem stackRegion_slice (sp : BitVec 64) (size off len : Nat) (fits : off ≤ size) :
    regionSlice (stackRegion sp size) off len = ⟨sp - BitVec.ofNat 64 (size - off), len⟩ := by
  unfold regionSlice stackRegion
  congr 1
  calc
    sp - BitVec.ofNat 64 size + BitVec.ofNat 64 off =
        sp - (BitVec.ofNat 64 (size - off) + BitVec.ofNat 64 off) + BitVec.ofNat 64 off := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel fits]
    _ = sp - BitVec.ofNat 64 (size - off) := by
      rw [← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem stackRegion_aligned (sp : BitVec 64) (size : Nat)
    (aligned : sp.toNat % 16 = 0) (frame : size % 16 = 0)
    (available : size ≤ sp.toNat) : (stackRegion sp size).base.toNat % 16 = 0 := by
  have noWrap := frame_base_end sp size available
  change (sp - BitVec.ofNat 64 size).toNat % 16 = 0
  omega

theorem readGrant_slice (m : Arm64.Memory) (region : Region) (offset bytes : Nat)
    (valid : region.Valid) (fits : offset + bytes ≤ region.bytes)
    (readable : ∀ p, region.Contains p → m.canRead p 1 = true) :
    ∀ p, (regionSlice region offset bytes).Contains p → m.canRead p 1 = true :=
  fun p inside => readable p (regionSlice_inside _ _ _ valid fits _ inside)

theorem writeGrant_slice (m : Arm64.Memory) (region : Region) (offset bytes : Nat)
    (valid : region.Valid) (fits : offset + bytes ≤ region.bytes)
    (writable : ∀ p, region.Contains p → m.canWrite p 1 = true) :
    ∀ p, (regionSlice region offset bytes).Contains p → m.canWrite p 1 = true :=
  fun p inside => writable p (regionSlice_inside _ _ _ valid fits _ inside)

end Crypto.HMACSHA256
