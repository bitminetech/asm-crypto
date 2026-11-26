import Proofs.RISCV64.DataTrace

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (allPerm_true_iff)

private theorem noLazy_iff (m : Memory) (p : Addr) (width : Nat) :
    m.allNoLazyFree p width = true ↔ ∀ i < width, m.isLazyFree (p + BitVec.ofNat 64 i) = false := by
  induction width generalizing p with
  | zero => simp [Arm64.Memory.allNoLazyFree]
  | succ n ih =>
    simp only [Arm64.Memory.allNoLazyFree, Bool.and_eq_true, Bool.not_eq_true', ih]
    have offset (i : Nat) : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i+1) := by
      rw [BitVec.ofNat_add]
      ac_rfl
    constructor
    · rintro ⟨zero, rest⟩ i hi
      cases i with
      | zero => simpa using zero
      | succ i => simpa only [offset] using rest i (by omega)
    · intro all
      refine ⟨by simpa using all 0 (by omega), ?_⟩
      intro i hi
      rw [offset]
      exact all (i+1) (by omega)

private theorem shift_allPerm {m : Memory} {p : Addr} {off small large : Nat}
    {test : Option Arm64.Perm → Bool} (whole : m.allPerm test p large = true) (inside : off+small ≤ large) :
    m.allPerm test (p + BitVec.ofNat 64 off) small = true := by
  apply (allPerm_true_iff _ _ _ _).mpr
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact (allPerm_true_iff _ _ _ _).mp whole _ (by omega)

theorem InRegion.readable {m : Memory} {base address : Addr} {size : Nat} {width : Width}
    (inside : InRegion base size address width) (whole : m.canRead base size = true) :
    m.canRead address width.bytes = true := by
  obtain ⟨off, fit, _, rfl⟩ := inside
  simp only [Arm64.Memory.canRead, Bool.and_eq_true] at whole ⊢
  refine ⟨shift_allPerm whole.1 fit, (noLazy_iff _ _ _).mpr ?_⟩
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact (noLazy_iff _ _ _).mp whole.2 _ (by omega)

theorem InRegion.writable {m : Memory} {base address : Addr} {size : Nat} {width : Width}
    (inside : InRegion base size address width) (whole : m.canWrite base size = true) :
    m.canWrite address width.bytes = true := by
  obtain ⟨off, fit, _, rfl⟩ := inside
  exact shift_allPerm whole fit

theorem InRegion.aligned {base address : Addr} {size : Nat} {width : Width}
    (inside : InRegion base size address width) (baseAligned : base.toNat % width.bytes = 0) :
    address.toNat % width.bytes = 0 := by
  obtain ⟨off, _, aligned, rfl⟩ := inside
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have dvd : width.bytes ∣ 2^64 := by cases width <;> decide
  rw [Nat.mod_mod_of_dvd _ dvd, Nat.add_mod, baseAligned, Nat.mod_mod_of_dvd _ dvd, aligned]
  exact Nat.zero_mod _

theorem InRegion.permitted_read {m : Memory} {base address : Addr} {size : Nat} {width : Width}
    (inside : InRegion base size address width) (baseAligned : base.toNat % width.bytes = 0)
    (readable : m.canRead base size = true) : (Access.read address width).permitted m = true := by
  simp only [Access.permitted, inside.aligned baseAligned, inside.readable readable, beq_self_eq_true, Bool.and_self]

theorem InRegion.permitted_write {m : Memory} {base address : Addr} {size : Nat} {width : Width}
    (inside : InRegion base size address width) (baseAligned : base.toNat % width.bytes = 0)
    (writable : m.canWrite base size = true) : (Access.write address width).permitted m = true := by
  simp only [Access.permitted, inside.aligned baseAligned, inside.writable writable, beq_self_eq_true, Bool.and_self]

end Crypto.RISCV64
