import Proofs.RISCV64.CallEntry
import Proofs.ARM64.ImportedPaddingFinish
import Proofs.ARM64.ImportedZeroPad
import Mathlib.Tactic.IntervalCases

namespace Crypto.RISCV64

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Crypto.ARM64.Imported (write64_byte write64_cells_outside bv_add_sub_add_left)

private theorem read64_write64 (m : Memory) (p v : Addr) :
    (m.write64 p v).read64 p = v := by
  unfold Arm64.Memory.read64
  have digit (i : Fin 8) := write64_byte m p v i
  rw [digit ⟨0, by decide⟩, digit ⟨1, by decide⟩, digit ⟨2, by decide⟩, digit ⟨3, by decide⟩,
    digit ⟨4, by decide⟩, digit ⟨5, by decide⟩, digit ⟨6, by decide⟩, digit ⟨7, by decide⟩]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  repeat' first
    | rw [BitVec.getLsbD_append]
    | rw [BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp (config := { decide := true })

private theorem slot_store_other (m : Memory) (p : Addr) (a b : Nat) (v : Addr)
    (apart : ∀ i : Fin 8, 8 ≤
      (BitVec.ofNat 64 b + BitVec.ofNat 64 i.val - BitVec.ofNat 64 a).toNat) :
    (m.write64 (p + BitVec.ofNat 64 a) v).read64 (p + BitVec.ofNat 64 b) =
      m.read64 (p + BitVec.ofNat 64 b) := by
  apply read64_same
  intro i
  apply write64_cells_outside
  rw [BitVec.add_assoc, bv_add_sub_add_left]
  exact apart i

private theorem spill_slot (s : CPU) (base : Addr) (reg : Reg) (off : Nat)
    (present : (reg, off) ∈ savedSlots)
    (shape : ∀ pair ∈ savedSlots, pair = (reg, off) ∨
      ∀ i : Fin 8, 8 ≤ (BitVec.ofNat 64 off + BitVec.ofNat 64 i.val - BitVec.ofNat 64 pair.2).toNat) :
    (spilled s base).read64 (base + BitVec.ofNat 64 off) = s.reg reg := by
  let store (m : Memory) (slot : Reg × Nat) :=
    m.write64 (base + BitVec.ofNat 64 slot.2) (s.reg slot.1)
  let address := base + BitVec.ofNat 64 off
  have transfer (l : List (Reg × Nat)) (m : Memory)
      (h : ∀ pair ∈ l, pair = (reg, off) ∨
        ∀ i : Fin 8, 8 ≤ (BitVec.ofNat 64 off + BitVec.ofNat 64 i.val - BitVec.ofNat 64 pair.2).toNat)
      (found : (reg, off) ∈ l ∨ m.read64 address = s.reg reg) :
      (l.foldl store m).read64 address = s.reg reg := by
    induction l generalizing m with
    | nil => simpa using found
    | cons slot tail ih =>
      have remain (pair : Reg × Nat) (hh : pair ∈ tail) := h pair (List.mem_cons_of_mem _ hh)
      apply ih _ remain
      rcases h slot List.mem_cons_self with same | apart
      · right
        subst slot
        exact read64_write64 _ _ _
      · have keep : (store m slot).read64 address = m.read64 address :=
          slot_store_other _ _ _ _ _ apart
        rw [keep]
        rcases found with found | ready
        · rcases List.mem_cons.mp found with eq | next
          · subst slot
            have clash := apart ⟨0, by decide⟩
            simp at clash
          · exact Or.inl next
        · exact Or.inr ready
  exact transfer savedSlots s.mem shape (.inl present)

theorem spilled_registers (s : CPU) (frame : Addr) :
    savedStackAt (spilled s frame) frame = savedRegisters s := by
  apply Vector.ext
  intro i hi
  interval_cases i
  · exact spill_slot s frame 8 416 (by decide) (by decide)
  · exact spill_slot s frame 9 424 (by decide) (by decide)
  · exact spill_slot s frame 18 432 (by decide) (by decide)
  · exact spill_slot s frame 19 440 (by decide) (by decide)
  · exact spill_slot s frame 20 448 (by decide) (by decide)
  · exact spill_slot s frame 21 456 (by decide) (by decide)
  · exact spill_slot s frame 22 464 (by decide) (by decide)
  · exact spill_slot s frame 23 472 (by decide) (by decide)

theorem savedStack_of_cells (m m' : Memory) (base : Addr)
    (cells : ∀ i : Fin 8, ∀ d : Fin 8,
      m.cells (base + BitVec.ofNat 64 (416+8*i.val) + BitVec.ofNat 64 d.val) =
        m'.cells (base + BitVec.ofNat 64 (416+8*i.val) + BitVec.ofNat 64 d.val)) :
    savedStackAt m base = savedStackAt m' base := by
  have same (i : Fin 8) :
      m.read64 (base + BitVec.ofNat 64 (416+8*i.val)) =
        m'.read64 (base + BitVec.ofNat 64 (416+8*i.val)) :=
    read64_same _ (cells i)
  apply Vector.ext
  intro i hi
  interval_cases i
  · exact same ⟨0, by decide⟩
  · exact same ⟨1, by decide⟩
  · exact same ⟨2, by decide⟩
  · exact same ⟨3, by decide⟩
  · exact same ⟨4, by decide⟩
  · exact same ⟨5, by decide⟩
  · exact same ⟨6, by decide⟩
  · exact same ⟨7, by decide⟩

end Crypto.RISCV64
