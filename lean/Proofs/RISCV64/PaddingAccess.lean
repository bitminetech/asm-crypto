import Proofs.RISCV64.CallRegions
import Proofs.RISCV64.TailAccess

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (lengthOffset paddingBlockCount)

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem copy_accesses (base : Addr) (s start : CPU) (data : ByteArray)
    (input : InputPrepared base s data start) (a : Access)
    (found : a ∈ dataTrace (tailCode (data.size % 64)) start) : CallData base s data.size a := by
  have inside := tail_accesses start _ input.cursor a found
  cases a with
  | fetch => exact inside.elim
  | read addr w =>
    cases w with
    | byte =>
      change InRegion (start.reg 28) (data.size % 64) addr .byte at inside
      rw [input.tail, inputTail] at inside
      exact .inr (.inr (.inl (inside.enclose (by have := Nat.div_add_mod data.size 64; omega) (Nat.mod_one _))))
    | word => exact inside.elim
    | double => exact inside.elim
  | write addr w =>
    cases w with
    | byte =>
      change InRegion (start.reg 29) (data.size % 64) addr .byte at inside
      rw [input.pad] at inside
      exact .inl (inside.enclose (start := 288)
        (by have := Nat.mod_lt data.size (by decide : 0 < 64); omega) (Nat.mod_one _))
    | word => exact inside.elim
    | double => exact inside.elim

private theorem marker_data (s : CPU) (rem : Nat) : dataTrace (markerCode rem) s =
    [.write (s.reg 29 + s.reg 7) .byte] := by
  have no (t : CPU) : dataTrace (oneBlock :: if rem < 56 then [] else [twoBlocks]) t = [] := by
    by_cases h : rem < 56 <;> simp only [h, if_true, if_false] <;> rfl
  rw [markerCode, dataTrace_append, no, List.append_nil]
  simp (config := { decide := true }) [marker, dataTrace, Op.accesses, Instruction.step]

theorem marker_accesses (base : Addr) (s t : CPU) (size : Nat)
    (rem : t.reg 7 = BitVec.ofNat 64 (size % 64)) (padding : t.reg 29 = entryStack s + 288)
    (a : Access) (found : a ∈ dataTrace (markerCode (size % 64)) t) : CallData base s size a := by
  rw [marker_data] at found
  obtain rfl := List.mem_singleton.mp found
  have inside : InRegion (entryStack s + BitVec.ofNat 64 288) 128 (t.reg 29 + t.reg 7) .byte := by
    exact ⟨size % 64, by change size%64+1 ≤ 128; have := Nat.mod_lt size (by decide : 0 < 64); omega,
      Nat.mod_one _, by rw [rem, padding]; rfl⟩
  exact .inl (inside.enclose (by decide) (Nat.mod_one _))

private def lengthSetup : List Instruction := lengthSuffix.take 3

private theorem length_end (s : CPU) :
    (run lengthSetup s).reg 30 = (s.reg 16 <<< (6 : Nat)) + s.reg 29 := by
  simp (config := { decide := true }) [lengthSetup, lengthSuffix, run, Instruction.step]

private theorem digit_data (s : CPU) (shift : BitVec 6) (off : Addr) :
    dataTrace (storeDigit shift off) s = [.write (s.reg 30 + off) .byte] ∧
      (run (storeDigit shift off) s).reg 30 = s.reg 30 := by
  simp (config := { decide := true }) [storeDigit, dataTrace, Op.accesses, run, Instruction.step]

private theorem length_data (s : CPU) : dataTrace lengthSuffix s =
    (List.range 8).map (fun i => .write ((s.reg 16 <<< (6 : Nat)) + s.reg 29 - 8 + BitVec.ofNat 64 i) .byte) := by
  let final : List Instruction := [⟨.store .byte 5 30 (-1), 4⟩]
  have split : lengthSuffix = lengthSetup ++ (storeDigit 56 (-8) ++ (storeDigit 48 (-7) ++
      (storeDigit 40 (-6) ++ (storeDigit 32 (-5) ++ (storeDigit 24 (-4) ++ (storeDigit 16 (-3) ++
      (storeDigit 8 (-2) ++ final))))))) := rfl
  have last (t : CPU) : dataTrace final t = [.write (t.reg 30 + -1) .byte] := rfl
  have empty : checkedFixedAccess lengthSetup [] = true := by decide
  simp only [split, dataTrace_append, empty_dataTrace empty, List.nil_append,
    (digit_data _ _ _).1, (digit_data _ _ _).2, last, length_end, List.range_succ,
    List.range_zero, List.nil_append,
    List.cons_append, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem length_accesses (base : Addr) (s t : CPU) (data : ByteArray)
    (padding : t.reg 29 = entryStack s + 288) (count : t.reg 16 = BitVec.ofNat 64 (paddingBlockCount data))
    (a : Access) (found : a ∈ dataTrace lengthSuffix t) : CallData base s data.size a := by
  rw [length_data] at found
  obtain ⟨i, bound, rfl⟩ := List.mem_map.mp found
  have iFits := List.mem_range.mp bound
  have go : (t.reg 16 <<< (6 : Nat)) - 8 = BitVec.ofNat 64 (lengthOffset (data.size % 64)) := by
    rw [count]
    by_cases short : data.size % 64 < 56 <;> simp [paddingBlockCount, lengthOffset, short]
  have endFits := Crypto.ARM64.Imported.lengthOffset_bounds (data.size % 64)
    (Nat.mod_lt _ (by decide : 0 < 64))
  have fits : lengthOffset (data.size % 64)+i+1 ≤ 128 := by omega
  have offset : (t.reg 16 <<< (6 : Nat)) + -8 = BitVec.ofNat 64 (lengthOffset (data.size % 64)) :=
    by simpa only [BitVec.sub_eq_add_neg] using go
  have addr : ((t.reg 16 <<< (6 : Nat)) + t.reg 29 - 8 + BitVec.ofNat 64 i) =
      (entryStack s + BitVec.ofNat 64 288) + BitVec.ofNat 64 (lengthOffset (data.size % 64) + i) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_comm (t.reg 16 <<< (6 : Nat)) (t.reg 29),
      BitVec.add_assoc (t.reg 29) (t.reg 16 <<< (6 : Nat)), offset,
      BitVec.add_assoc, ← BitVec.ofNat_add, padding]
    rfl
  have inside : InRegion (entryStack s + BitVec.ofNat 64 288) 128 _ .byte :=
    ⟨_, fits, Nat.mod_one _, addr⟩
  exact .inl (inside.enclose (by decide) (Nat.mod_one _))

theorem iv_accesses (base : Addr) (s t : CPU) (size : Nat)
    (pc : t.pc = base + 0xc8) (stack : t.reg 2 = entryStack s)
    (a : Access) (found : a ∈ dataTrace initialHashCode t) : CallData base s size a := by
  let head := initialHashCode.take 2
  let body := initialHashCode.drop 2
  have split : initialHashCode = head ++ body := (List.take_append_drop 2 initialHashCode).symm
  rw [split, dataTrace_append, empty_dataTrace (code := head) (by decide), List.nil_append] at found
  have check : checkedFixedAccess body [⟨false, 5, 32⟩, ⟨true, 2, 480⟩] = true := by decide
  obtain ⟨r, list, inside⟩ := fixed_accesses check found
  have src : (run head t).reg 5 = base + BitVec.ofNat 64 initialHashOffset := by
    simp (config := { decide := true }) [head, run, initialHashCode, Instruction.step, pc, initialHashOffset, BitVec.add_assoc]
  have sp : (run head t).reg 2 = entryStack s := (run_reg_unchanged t head 2 (by decide)).trans stack
  rcases List.mem_cons.mp list with same | other
  · subst r
    cases a with
    | fetch => exact inside.elim
    | read addr w =>
      have read : InRegion (base + BitVec.ofNat 64 initialHashOffset) 32 addr w := by
        simpa only [src] using inside.2
      exact .inr (.inr (.inr (read.enclose (by decide +kernel) (by cases w <;> decide))))
    | write => exact (Bool.false_ne_true inside.1).elim
  · have same : r = ⟨true, 2, 480⟩ := List.mem_singleton.mp other
    subst r
    cases a with
    | fetch => exact inside.elim
    | read => exact (Bool.false_ne_true inside.1.symm).elim
    | write => exact .inl (by simpa only [sp] using inside.2)

end Crypto.RISCV64
