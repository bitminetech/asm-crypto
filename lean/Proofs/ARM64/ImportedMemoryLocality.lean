import Proofs.ARM64.ImportedPermissionView

/-!
Locality of the imported scalar memory operations. These helpers preserve
full cells (bytes and permission/liveness metadata) on a declared footprint.
-/
namespace Crypto.ARM64.Imported

def CellsOnRange (left right : Arm64.Memory) (address : BitVec 64) (bytes : Nat) : Prop :=
  ∀ i, i < bytes → left.cells (address + BitVec.ofNat 64 i) = right.cells (address + BitVec.ofNat 64 i)

def SameCellsOn (footprint : BitVec 64 → Prop) (left right : Arm64.Memory) : Prop :=
  ∀ p, footprint p → left.cells p = right.cells p

theorem cellsOnRange_tail {left right : Arm64.Memory} {address : BitVec 64} {bytes : Nat}
    (same : CellsOnRange left right address (bytes + 1)) : CellsOnRange left right (address + 1#64) bytes := by
  intro i hi
  have cell := same (i + 1) (by omega)
  have offset : address + 1#64 + BitVec.ofNat 64 i = address + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.ofNat_add]
    ac_rfl
  rw [offset]
  exact cell

theorem allPerm_cells_eq (left right : Arm64.Memory) (test : Option Arm64.Perm → Bool)
    (address : BitVec 64) (bytes : Nat) (same : CellsOnRange left right address bytes) :
    left.allPerm test address bytes = right.allPerm test address bytes := by
  induction bytes generalizing address with
  | zero => rfl
  | succ bytes ih =>
    have head := same 0 (by omega)
    simp only [BitVec.add_zero] at head
    have permission : left.perm address = right.perm address := by simp only [Arm64.Memory.perm, head]
    simp only [Arm64.Memory.allPerm, permission, ih _ (cellsOnRange_tail same)]

theorem noLazy_cells_eq (left right : Arm64.Memory) (address : BitVec 64) (bytes : Nat)
    (same : CellsOnRange left right address bytes) :
    left.allNoLazyFree address bytes = right.allNoLazyFree address bytes := by
  induction bytes generalizing address with
  | zero => rfl
  | succ bytes ih =>
    have head := same 0 (by omega)
    simp only [BitVec.add_zero] at head
    have lazy : left.isLazyFree address = right.isLazyFree address := by simp only [Arm64.Memory.isLazyFree, head]
    simp only [Arm64.Memory.allNoLazyFree, lazy, ih _ (cellsOnRange_tail same)]

theorem canRead_cells_eq (left right : Arm64.Memory) (address : BitVec 64) (bytes : Nat)
    (same : CellsOnRange left right address bytes) : left.canRead address bytes = right.canRead address bytes := by
  unfold Arm64.Memory.canRead
  rw [allPerm_cells_eq left right _ address bytes same, noLazy_cells_eq left right address bytes same]

theorem canWrite_cells_eq (left right : Arm64.Memory) (address : BitVec 64) (bytes : Nat)
    (same : CellsOnRange left right address bytes) : left.canWrite address bytes = right.canWrite address bytes :=
  allPerm_cells_eq left right _ address bytes same

theorem canExec_cells_eq (left right : Arm64.Memory) (address : BitVec 64) (bytes : Nat)
    (same : CellsOnRange left right address bytes) : left.canExec address bytes = right.canExec address bytes :=
  allPerm_cells_eq left right _ address bytes same

theorem readSized_cells_eq (left right : Arm64.Memory) (address : BitVec 64) (size : Arm64.MemWidth)
    (signed : Bool) (same : CellsOnRange left right address size.bytes) :
    left.readSized size signed address = right.readSized size signed address := by
  have byte (i : Nat) (bound : i < size.bytes) :
      left.read8 (address + BitVec.ofNat 64 i) = right.read8 (address + BitVec.ofNat 64 i) :=
    read8_of_cell _ (same i bound)
  cases size with
  | B8 =>
    have b0 := byte 0 (by decide)
    simp only [BitVec.add_zero] at b0
    simp only [Arm64.Memory.readSized]
    rw [b0]
  | H16 =>
    have b0 := byte 0 (by decide)
    have b1 := byte 1 (by decide)
    simp only [Arm64.Memory.readSized, Arm64.Memory.read16]
    rw [b0, b1]
  | W32 =>
    have b0 := byte 0 (by decide)
    have b1 := byte 1 (by decide)
    have b2 := byte 2 (by decide)
    have b3 := byte 3 (by decide)
    simp only [Arm64.Memory.readSized, Arm64.Memory.read32]
    rw [b0, b1, b2, b3]
  | X64 =>
    have b0 := byte 0 (by decide)
    have b1 := byte 1 (by decide)
    have b2 := byte 2 (by decide)
    have b3 := byte 3 (by decide)
    have b4 := byte 4 (by decide)
    have b5 := byte 5 (by decide)
    have b6 := byte 6 (by decide)
    have b7 := byte 7 (by decide)
    simp only [Arm64.Memory.readSized, Arm64.Memory.read64]
    rw [b0, b1, b2, b3, b4, b5, b6, b7]

theorem sameCells_write8 {footprint : BitVec 64 → Prop} {left right : Arm64.Memory}
    (same : SameCellsOn footprint left right) (address : BitVec 64) (value : BitVec 8) :
    SameCellsOn footprint (left.write8 address value) (right.write8 address value) := by
  intro p hp
  have cell := same p hp
  by_cases target : p = address
  · subst p
    simp only [Arm64.Memory.write8, Arm64.Memory.rawPerm, cell]
  · simp only [Arm64.Memory.write8, if_neg target, cell]

theorem sameCells_writeSized {footprint : BitVec 64 → Prop} {left right : Arm64.Memory}
    (same : SameCellsOn footprint left right) (size : Arm64.MemWidth) (address : BitVec 64) (value : BitVec 64) :
    SameCellsOn footprint (left.writeSized size address value) (right.writeSized size address value) := by
  cases size <;> simp only [Arm64.Memory.writeSized, Arm64.Memory.write64,
    Arm64.Memory.write32, Arm64.Memory.write16]
  all_goals repeat' apply sameCells_write8
  all_goals exact same

end Crypto.ARM64.Imported
