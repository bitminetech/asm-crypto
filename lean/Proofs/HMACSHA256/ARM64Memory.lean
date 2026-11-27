import Proofs.ARM64.ImportedPaddingSuffix

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

abbrev Addr := BitVec 64

/-- Little-endian words written in increasing address order. -/
def writeWords (m : Arm64.Memory) (base : Addr) (word : Nat → Addr) : Nat → Arm64.Memory
  | 0 => m
  | n + 1 => (writeWords m base word n).write64 (base + BitVec.ofNat 64 (8 * n)) (word n)

@[simp] theorem writeWords_perm (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n : Nat) (p : Addr) : (writeWords m base word n).perm p = m.perm p := by
  induction n <;> simp_all [writeWords, Arm64.Memory.write64, perm_write8]

@[simp] theorem writeWords_canWrite (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n : Nat) (p : Addr) (width : Nat) :
    (writeWords m base word n).canWrite p width = m.canWrite p width := by
  induction n <;> simp_all [writeWords]

theorem writeWords_canRead (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n : Nat) (p : Addr) (width : Nat) (read : m.canRead p width = true) :
    (writeWords m base word n).canRead p width = true := by
  induction n with
  | zero => exact read
  | succ n ih => exact canRead_write64 _ _ _ _ _ ih

theorem writeWords_outside (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n : Nat) (p : Addr) (outside : 8 * n ≤ (p - base).toNat) :
    (writeWords m base word n).cells p = m.cells p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have apart : 8 ≤ (p - (base + BitVec.ofNat 64 (8 * n))).toNat := by
      by_contra! close
      let d := (p - (base + BitVec.ofNat 64 (8 * n))).toNat
      have address : base + BitVec.ofNat 64 (8 * n + d) = p := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        exact address_reconstruct _ _
      have dBound : 8 * n + d < 2 ^ 64 := by
        have cap := (p - base).isLt
        change d < 8 at close
        omega
      have dist : (p - base).toNat = 8 * n + d := by
        rw [← address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt dBound]
      change d < 8 at close
      omega
    exact (write64_cells_outside _ _ _ _ apart).trans (ih (by omega))

theorem writeWords_byte (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n i : Nat) (k : Fin 8) (index : i < n) (extent : 8 * n < 2 ^ 64) :
    (writeWords m base word n).read8 ((base + BitVec.ofNat 64 (8 * i)) +
      BitVec.ofNat 64 k.val) = (word i).extractLsb' (8 * k.val) 8 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i = n
    · subst i
      exact write64_byte _ _ _ _
    · have before : i < n := by omega
      have apart (j : Fin 8) : (base + BitVec.ofNat 64 (8 * i)) + BitVec.ofNat 64 k.val ≠
          (base + BitVec.ofNat 64 (8 * n)) + BitVec.ofNat 64 j.val := by
        intro eq
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_right_inj] at eq
        have smallK := k.isLt
        have smallJ := j.isLt
        have eqNat := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * i + k.val < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 8 * n + j.val < 2 ^ 64)] at eqNat
        omega
      change ((writeWords m base word n).write64 (base + BitVec.ofNat 64 (8 * n))
        (word n)).read8 _ = _
      rw [read8_write64_outside_ne _ _ _ _ apart]
      exact ih before (by omega)

theorem read64_byte (m : Arm64.Memory) (base : Addr) (k : Fin 8) :
    (m.read64 base).extractLsb' (8 * k.val) 8 = m.read8 (base + BitVec.ofNat 64 k.val) := by
  obtain ⟨k, hk⟩ := k
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases k <;> interval_cases i <;>
    simp only [Arm64.Memory.read64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  all_goals simp (config := { decide := true })

theorem writeWords_word (m : Arm64.Memory) (base : Addr) (word : Nat → Addr)
    (n i : Nat) (index : i < n) (extent : 8 * n < 2 ^ 64) :
    (writeWords m base word n).read64 (base + BitVec.ofNat 64 (8 * i)) = word i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let byte : Fin 8 := ⟨j / 8, by omega⟩
  have octet := writeWords_byte m base word n i byte index extent
  rw [← read64_byte] at octet
  have bit := congrArg (fun b : BitVec 8 => b.getLsbD (j % 8)) octet
  simp only [BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 8), decide_true,
    Bool.true_and] at bit
  have bitIndex : 8 * byte.val + j % 8 = j := by dsimp [byte]; omega
  rwa [bitIndex] at bit

theorem read64_eq_of_cells {m n : Arm64.Memory} (base : Addr)
    (same : ∀ i : Fin 8, m.cells (base + BitVec.ofNat 64 i.val) =
      n.cells (base + BitVec.ofNat 64 i.val)) : m.read64 base = n.read64 base := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let byte : Fin 8 := ⟨j / 8, by omega⟩
  have hbyte : m.read8 (base + BitVec.ofNat 64 byte.val) =
      n.read8 (base + BitVec.ofNat 64 byte.val) := by
    unfold Arm64.Memory.read8
    rw [same byte]
  rw [← read64_byte, ← read64_byte] at hbyte
  have bit := congrArg (fun octet : BitVec 8 => octet.getLsbD (j % 8)) hbyte
  simp only [BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 8), decide_true,
    Bool.true_and] at bit
  have position : 8 * byte.val + j % 8 = j := by dsimp [byte]; omega
  rwa [position] at bit

/-- Convert the word-sized XOR in the native loop to the corresponding byte. -/
theorem maskedByte (m : Arm64.Memory) (base : Addr) (mask : Addr) (k : Fin 8) :
    (m.read64 base ^^^ mask).extractLsb' (8 * k.val) 8 =
      m.read8 (base + BitVec.ofNat 64 k.val) ^^^ mask.extractLsb' (8 * k.val) 8 := by
  rw [BitVec.extractLsb'_xor, read64_byte]

end Crypto.HMACSHA256.ARM64
