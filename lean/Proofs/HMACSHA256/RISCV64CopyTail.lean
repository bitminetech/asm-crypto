import Proofs.HMACSHA256.RISCV64Copy

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.ARM64.Imported (address_delta bv_add_sub_add_left cells_write8_outside read8_write8)
open Crypto.HMACSHA256.ARM64 (writeWords_byte writeWords_outside read64_byte)

def byteCycles (message : Bool) (s : CPU) : Nat → Option CPU
  | 0 => some s
  | n + 1 => (byteCycles message s n).bind
      (if message then runByteCycle entry 0xf0 else runByteCycle key 0x6a)

structure ByteCopyPrefix (start out : CPU) (length copied : Nat) : Prop where
  pc : out.pc = start.pc
  source : out.reg 30#5 = start.reg 30#5 + BitVec.ofNat 64 copied
  dest : out.reg 29#5 = start.reg 29#5 + BitVec.ofNat 64 copied
  count : out.reg 6#5 = BitVec.ofNat 64 (length - copied)
  bytes : ∀ i, i < copied →
    out.mem.read8 (start.reg 29#5 + BitVec.ofNat 64 i) =
      start.mem.read8 (start.reg 30#5 + BitVec.ofNat 64 i)
  frame : ∀ p, copied ≤ (p - start.reg 29#5).toNat → out.mem.cells p = start.mem.cells p
  preserved : ∀ r, r ≠ 6#5 → r ≠ 29#5 → r ≠ 30#5 → r ≠ 31#5 → out.reg r = start.reg r

theorem byte_copy_iterations (message : Bool) (s : CPU) (length copied : Nat)
    (lengthReg : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (byteBound : copied ≤ length) :
    ∃ out, byteCycles message s copied = some out ∧ ByteCopyPrefix s out length copied := by
  induction copied with
  | zero =>
    exact ⟨s, rfl, ⟨rfl, by simp, by simp, by simpa using lengthReg, fun _ h => by omega,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
  | succ n ih =>
    obtain ⟨mid, prevRun, prev⟩ := ih (by omega)
    have nonempty : mid.reg 6#5 ≠ 0#64 := by
      rw [prev.count]
      intro eq
      have number := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length - n < 2 ^ 64)] at number
      change length - n = 0 at number
      omega
    have next : (if message then runByteCycle entry 0xf0 else runByteCycle key 0x6a) mid =
        some (byteCopy mid) := by
      cases message
      · simpa only [Bool.false_eq_true, if_false, nonempty] using (byte_copies mid).2
      · simpa only [if_true, nonempty] using (byte_copies mid).1
    have originalByte : mid.mem.read8 (mid.reg 30#5) =
        s.mem.read8 (s.reg 30#5 + BitVec.ofNat 64 n) := by
      rw [prev.source]
      unfold Arm64.Memory.read8
      rw [prev.frame _ (Nat.le_trans (by omega) (apart n (by omega)))]
    refine ⟨byteCopy mid, ?_, ⟨prev.pc, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [byteCycles, prevRun, Option.bind_some, next]
    · have address : (byteCopy mid).reg 30#5 = mid.reg 30#5 + 1#64 := by
        simp (config := { decide := true }) [byteCopy, advanceCopy]
      rw [address, prev.source]
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    · have address : (byteCopy mid).reg 29#5 = mid.reg 29#5 + 1#64 := by
        simp (config := { decide := true }) [byteCopy, advanceCopy]
      rw [address, prev.dest]
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    · have remaining : (byteCopy mid).reg 6#5 = mid.reg 6#5 - 1#64 := by
        simp (config := { decide := true }) [byteCopy, advanceCopy]
      rw [remaining, prev.count]
      have eq : length - n = (length - (n + 1)) + 1 := by omega
      nth_rw 1 [eq]
      simp only [BitVec.ofNat_add, BitVec.add_sub_cancel]
    · intro i hi
      change (mid.mem.write8 (mid.reg 29#5) (mid.mem.read8 (mid.reg 30#5))).read8 _ = _
      rw [prev.dest, originalByte, read8_write8]
      by_cases last : i = n
      · subst i
        simp
      · have different : s.reg 29#5 + BitVec.ofNat 64 i ≠ s.reg 29#5 + BitVec.ofNat 64 n := by
          intro eq
          have bits := (BitVec.add_right_inj _).mp eq
          have nums := congrArg BitVec.toNat bits
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at nums
          exact last nums
        rw [if_neg different]
        exact prev.bytes i (by omega)
    · intro p outside
      change (mid.mem.write8 (mid.reg 29#5) (mid.mem.read8 (mid.reg 30#5))).cells p = _
      have different : p ≠ mid.reg 29#5 := by
        intro eq
        rw [eq, prev.dest, address_delta, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at outside
        omega
      rw [cells_write8_outside _ _ _ _ different]
      exact prev.frame p (by omega)
    · intro r c d src tmp
      unfold byteCopy advanceCopy
      rw [reg_write, reg_put, if_neg c]
      by_cases zero : r = 0
      · subst r
        exact (reg_zero _).symm
      · rw [if_neg zero, reg_put, if_neg zero, if_neg d, reg_put,
          if_neg zero, if_neg src, reg_put, if_neg zero, if_neg tmp]
        exact prev.preserved r c d src tmp

/-- The final zero count exits without another read or write. -/
theorem byte_copy_done (message : Bool) (s : CPU) (length : Nat)
    (lengthReg : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat) :
    ∃ out, byteCycles message s (length + 1) = some out ∧
      out.pc = s.pc + 20#64 ∧ out.reg 6#5 = 0#64 ∧
      (∀ i, i < length → out.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 i) =
        s.mem.read8 (s.reg 30#5 + BitVec.ofNat 64 i)) ∧
      (∀ p, length ≤ (p - s.reg 29#5).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ r, r ≠ 6#5 → r ≠ 29#5 → r ≠ 30#5 → r ≠ 31#5 → out.reg r = s.reg r) := by
  obtain ⟨mid, ran, p⟩ := byte_copy_iterations message s length length lengthReg lengthBound apart (by omega)
  have empty : mid.reg 6#5 = 0#64 := by rw [p.count, Nat.sub_self]
  let out := { mid with pc := mid.pc + 20#64 }
  have next : (if message then runByteCycle entry 0xf0 else runByteCycle key 0x6a) mid = some out := by
    cases message
    · simpa only [Bool.false_eq_true, if_false, if_pos empty, out] using (byte_copies mid).2
    · simpa only [if_true, if_pos empty, out] using (byte_copies mid).1
  refine ⟨out, ?_, congrArg (· + 20#64) p.pc, empty, p.bytes, p.frame, p.preserved⟩
  simp only [byteCycles, ran, Option.bind_some, next]

private theorem prefix_dist (base : Addr) (i off : Nat)
    (before : i < off) (bound : off < 2 ^ 64) :
    (base + BitVec.ofNat 64 i - (base + BitVec.ofNat 64 off)).toNat = 2 ^ 64 - off + i := by
  rw [bv_add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt bound]
  exact Nat.mod_eq_of_lt (by omega)

theorem complete_copy (message : Bool) (s : CPU) (length : Nat)
    (lengthReg : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat) :
    ∃ atTail out, wordCycles message s (length / 8 + 1) = some atTail ∧
      byteCycles message atTail (length % 8 + 1) = some out ∧
      out.pc = s.pc + 42#64 ∧ out.reg 6#5 = 0#64 ∧
      (∀ i, i < length → out.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 i) =
        s.mem.read8 (s.reg 30#5 + BitVec.ofNat 64 i)) ∧
      (∀ p, length ≤ (p - s.reg 29#5).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ r, r ≠ 6#5 → r ≠ 29#5 → r ≠ 30#5 → r ≠ 31#5 → out.reg r = s.reg r) := by
  obtain ⟨tail, start, tailPC, rem, src, dst, memory, stack⟩ :=
    word_copy_to_tail message s length lengthReg lengthBound apart
  let split := 8 * (length / 8)
  have sum : split + length % 8 = length := by dsimp [split]; omega
  have lengthOfTail (i : Nat) (bound : i < length % 8) :
      length % 8 ≤ (tail.reg 30#5 + BitVec.ofNat 64 i - tail.reg 29#5).toNat := by
    rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add]
    have check := apart (split + i) (by omega)
    have off : split ≤ (s.reg 30#5 + BitVec.ofNat 64 (split + i) - s.reg 29#5).toNat := by omega
    rw [copy_offset_distance _ _ _ off]
    omega
  obtain ⟨out, ran, pc, done, bytes, frame, restore⟩ :=
    byte_copy_done message tail (length % 8) rem (by omega) lengthOfTail
  refine ⟨tail, out, start, ran, ?_, done, ?_, ?_, fun r c d src tmp => (restore r c d src tmp).trans (stack r c d src tmp)⟩
  · rw [pc, tailPC, BitVec.add_assoc]
    rfl
  · intro i inside
    by_cases before : i < split
    · have apart' : length % 8 ≤
          (s.reg 29#5 + BitVec.ofNat 64 i - tail.reg 29#5).toNat := by
        rw [dst, prefix_dist _ _ split before (by omega)]
        omega
      have stays : out.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 i) =
          tail.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 i) := by
        unfold Arm64.Memory.read8
        rw [frame _ apart']
      let byte : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩
      have index : i / 8 < length / 8 := by dsimp [split] at before; omega
      have ea : 8 * (i / 8) + byte.val = i := by dsimp [byte]; omega
      rw [stays, memory]
      have wrote := writeWords_byte s.mem (s.reg 29#5)
        (fun j => s.mem.read64 (s.reg 30#5 + BitVec.ofNat 64 (8 * j)))
        (length / 8) (i / 8) byte index (by dsimp [split] at sum; omega)
      change _ = (s.mem.read64 (s.reg 30#5 + BitVec.ofNat 64 (8 * (i / 8)))).extractLsb'
        (8 * byte.val) 8 at wrote
      rw [read64_byte] at wrote
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, ea] using wrote
    · let j := i - split
      have small : j < length % 8 := by dsimp [j]; omega
      have eq : split + j = i := by dsimp [j]; omega
      have wrote := bytes j small
      simp only [dst, src, BitVec.add_assoc, ← BitVec.ofNat_add] at wrote
      change out.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 (split + j)) =
        tail.mem.read8 (s.reg 30#5 + BitVec.ofNat 64 (split + j)) at wrote
      rw [eq] at wrote
      rw [wrote]
      unfold Arm64.Memory.read8
      rw [memory, writeWords_outside _ _ _ _ _]
      exact Nat.le_trans (by omega) (apart i inside)
  · intro p h
    have hTail : length % 8 ≤ (p - tail.reg 29#5).toNat := by
      rw [dst, copy_offset_distance _ _ split (by omega)]
      omega
    have before := frame p hTail
    rw [memory] at before
    exact before.trans (writeWords_outside _ _ _ _ _ (by omega))

end Crypto.HMACSHA256.RISCV64
