import Proofs.RISCV64.FrameEntry
import Proofs.RISCV64.InitialHash
import Proofs.RISCV64.FeedForward
import Proofs.ARM64.ImportedHashInitFrame

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (address_delta fold_cells_frame region_store_delta
  write64_cells_outside wordVector)

def CellFrame (after before : Memory) (base : Addr) (bytes : Nat) : Prop :=
  ∀ p, bytes ≤ (p - base).toNat → after.cells p = before.cells p

theorem CellFrame.trans {a b c : Memory} {base : Addr} {bytes : Nat}
    (ab : CellFrame a b base bytes) (bc : CellFrame b c base bytes) :
    CellFrame a c base bytes := fun p hp => (ab p hp).trans (bc p hp)

theorem CellFrame.enclose {a b : Memory} {base : Addr} {off small large : Nat}
    (h : CellFrame a b (base + BitVec.ofNat 64 off) small) (fit : off + small ≤ large) :
    CellFrame a b base large :=
  fun p hp => h p (region_store_delta base p off large small fit hp)

theorem CellFrame.offset {a b : Memory} {base : Addr} {off width : Nat}
    (h : CellFrame a b base width) (j : Nat) (outside : width ≤ off + j)
    (small : off + j < 2^64) :
    a.cells (base + BitVec.ofNat 64 off + BitVec.ofNat 64 j) =
      b.cells (base + BitVec.ofNat 64 off + BitVec.ofNat 64 j) := by
  apply h
  rwa [BitVec.add_assoc, ← BitVec.ofNat_add, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem read8_same {a b : Memory} (p : Addr) (h : a.cells p = b.cells p) :
    a.read8 p = b.read8 p := by
  simp only [Arm64.Memory.read8, h]

theorem read64_same {a b : Memory} (p : Addr)
    (h : ∀ i : Fin 8, a.cells (p + BitVec.ofNat 64 i.val) = b.cells (p + BitVec.ofNat 64 i.val)) :
    a.read64 p = b.read64 p := by
  unfold Arm64.Memory.read64
  have read (i : Fin 8) := read8_same _ (h i)
  rw [read ⟨0, by decide⟩, read ⟨1, by decide⟩, read ⟨2, by decide⟩,
    read ⟨3, by decide⟩, read ⟨4, by decide⟩, read ⟨5, by decide⟩,
    read ⟨6, by decide⟩, read ⟨7, by decide⟩]

theorem ImageLoaded.of_cells {base : Addr} {a b : Memory}
    (before : ImageLoaded base b)
    (h : ∀ i, i < image.size → a.cells (base + BitVec.ofNat 64 i) = b.cells (base + BitVec.ofNat 64 i)) :
    ImageLoaded base a := fun i hi => (read8_same _ (h i hi)).trans (before i hi)

theorem cleared_frame (m : Memory) (p : Addr) : CellFrame (cleared m p) m p 128 := by
  intro q h
  unfold cleared
  apply fold_cells_frame
  intro a i hi
  have hi' := List.mem_range.mp hi
  apply write64_cells_outside
  exact region_store_delta p q (8*i) 128 8 (by omega) h

theorem cleared_zero (m : Memory) (p : Addr) (i : Fin 128) :
    (cleared m p).read8 (p + BitVec.ofNat 64 i.val) = 0 := by
  let state : Arm64.State := { mem := m, sp := p - 288#64 }
  have sp : state.sp + 288#64 = p := BitVec.sub_add_cancel p 288#64
  have mem : state.mem = m := rfl
  have same : Crypto.ARM64.Imported.zeroPadMemory state = cleared m p := by
    unfold Crypto.ARM64.Imported.zeroPadMemory cleared
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
    simp only [sp, mem]
    rfl
  simpa only [same, sp] using Crypto.ARM64.Imported.zeroPadMemory_byte state i

private def copyFixed (m : Memory) (src dst : Addr) : Memory :=
  (List.range 4).foldl (fun before i =>
    before.write64 (dst + BitVec.ofNat 64 (8*i)) (m.read64 (src + BitVec.ofNat 64 (8*i)))) m

theorem copyInitialHash_frame (m : Memory) (src dst : Addr) :
    CellFrame (copyInitialHash m src dst) m dst 32 := by
  intro p hp
  unfold copyInitialHash
  apply fold_cells_frame
  intro before i hi
  have hi' := List.mem_range.mp hi
  apply write64_cells_outside
  exact region_store_delta dst p (8*i) 32 8 (by omega) hp

attribute [local irreducible] Arm64.Memory.read64 Arm64.Memory.write64

set_option maxHeartbeats 3000000 in
private theorem copy_fixed (m : Memory) (src dst : Addr)
    (apart : ∀ i : Fin 32, 32 ≤ (src + BitVec.ofNat 64 i.val - dst).toNat) :
    copyInitialHash m src dst = copyFixed m src dst := by
  let fixed (a : Memory) (i : Nat) :=
    a.write64 (dst + BitVec.ofNat 64 (8*i)) (m.read64 (src + BitVec.ofNat 64 (8*i)))
  let copying (a : Memory) (i : Nat) :=
    a.write64 (dst + BitVec.ofNat 64 (8*i)) (a.read64 (src + BitVec.ofNat 64 (8*i)))
  have frame (a : Memory) (i : Nat) (hi : i < 4) :
      CellFrame (fixed a i) a dst 32 :=
    fun p hp => write64_cells_outside _ _ _ _ (region_store_delta dst p (8*i) 32 8 (by omega) hp)
  have go (xs : List Nat) (a : Memory) (slots : ∀ i ∈ xs, i < 4) (kept : CellFrame a m dst 32) :
      xs.foldl copying a = xs.foldl fixed a := by
    induction xs generalizing a with
    | nil => rfl
    | cons i xs ih =>
      have hi := slots i List.mem_cons_self
      have same : a.read64 (src + BitVec.ofNat 64 (8*i)) = m.read64 (src + BitVec.ofNat 64 (8*i)) := by
        apply read64_same
        intro j
        apply kept
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact apart ⟨8*i+j.val, by have := j.isLt; omega⟩
      have one : copying a i = fixed a i := by simp only [copying, fixed, same]
      simp only [List.foldl_cons, one]
      exact ih _ (fun j hj => slots j (List.mem_cons_of_mem _ hj)) ((frame a i hi).trans kept)
  exact go (List.range 4) m (fun _ => List.mem_range.mp) (fun _ _ => rfl)

theorem copyInitialHash_words (m : Memory) (src dst : Addr)
    (apart : ∀ i : Fin 32, 32 ≤ (src + BitVec.ofNat 64 i.val - dst).toNat) :
    wordVector 8 (copyInitialHash m src dst) dst = wordVector 8 m src := by
  rw [copy_fixed _ _ _ apart]
  let state : Arm64.State := { mem := m, sp := dst - 256#64, pc := src - 732#64 }
  have sp : state.sp + 256#64 = dst := BitVec.sub_add_cancel dst 256#64
  have pc : state.pc + 732#64 = src := BitVec.sub_add_cancel src 732#64
  have mem : state.mem = m := rfl
  have same : Crypto.ARM64.Imported.initialHashMemory state = copyFixed m src dst := by
    unfold Crypto.ARM64.Imported.initialHashMemory copyFixed
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
    simp only [sp, pc, mem]
  simpa only [same, sp, pc, mem] using Crypto.ARM64.Imported.initialHashMemory_words state

end Crypto.RISCV64
