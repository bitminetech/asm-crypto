import Proofs.HMACSHA256.X86Frame
import Proofs.HMACSHA256.ARM64Memory
import Proofs.X86_64.Caller

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.ARM64.Imported (read8_of_cell write64_cells_outside address_delta)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

def savedBase (s : Cpu) : Val := s.regs.get .rsp - 48#64

def savedOffset (i : Fin 6) : Nat := 8 * (5 - i.val)

def pushedMemory (s : Cpu) (n : Nat) : Mem :=
  match n with
  | 0 => s.mem
  | i + 1 =>
    if valid : i < 6 then (pushedMemory s i).writeSize .q
      (savedBase s + BitVec.ofNat 64 (savedOffset ⟨i, valid⟩)) (s.regs.get (savedReg ⟨i, valid⟩))
    else pushedMemory s i

theorem frame_saved_memory (r : HmacRoutine) (s : Cpu) :
    (enteredFrame r s).mem = pushedMemory s 6 := by
  have base1 : savedBase s + 40#64 = s.regs.get .rsp - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have base2 : savedBase s + 32#64 = s.regs.get .rsp - 8#64 - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have base3 : savedBase s + 24#64 = s.regs.get .rsp - 8#64 - 8#64 - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have base4 : savedBase s + 16#64 = s.regs.get .rsp - 8#64 - 8#64 - 8#64 - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have base5 : savedBase s + 8#64 = s.regs.get .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have base6 : savedBase s + 0#64 = s.regs.get .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 := by
    simp only [savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  unfold enteredFrame reserveFrame
  change (List.foldl saveRegister s [(.rbx, 1), (.rbp, 1), (.r12, 2), (.r13, 2), (.r14, 2), (.r15, 2)]).mem = _
  simp (config := {decide := true}) only [List.foldl_cons, List.foldl_nil, saveRegister, pushedMemory,
    dif_pos (by decide : 5 < 6), dif_pos (by decide : 4 < 6), dif_pos (by decide : 3 < 6),
    dif_pos (by decide : 2 < 6), dif_pos (by decide : 1 < 6), dif_pos (by decide : 0 < 6),
    Regs.get_set_same, Regs.get_set_ne, savedOffset, savedReg]
  change _ = (s.mem.writeSize .q (savedBase s + 40#64) (s.regs.get .rbx)
    |>.writeSize .q (savedBase s + 32#64) (s.regs.get .rbp)
    |>.writeSize .q (savedBase s + 24#64) (s.regs.get .r12)
    |>.writeSize .q (savedBase s + 16#64) (s.regs.get .r13)
    |>.writeSize .q (savedBase s + 8#64) (s.regs.get .r14)
    |>.writeSize .q (savedBase s + 0#64) (s.regs.get .r15))
  rw [base1, base2, base3, base4, base5, base6]

theorem store64_outside (m : Mem) (dst value p : Val) (outside : 8 ≤ (p - dst).toNat) :
    (m.writeSize .q dst value).read p = m.read p := by
  have same : (byteView (m.writeSize .q dst value)).cells p = (byteView m).cells p := by
    rw [byteView_write64]
    exact write64_cells_outside _ _ _ _ outside
  rw [← byteView_read (m.writeSize .q dst value) p, ← byteView_read m p]
  exact read8_of_cell p same

theorem frame_saved_outside (r : HmacRoutine) (s : Cpu) (p : Val)
    (outside : 48 ≤ (p - savedBase s).toNat) : (enteredFrame r s).mem.read p = s.mem.read p := by
  rw [frame_saved_memory]
  have frame (n : Nat) : (pushedMemory s n).read p = s.mem.read p := by
    induction n with
    | zero => rfl
    | succ n ih =>
      unfold pushedMemory
      split
      next bound =>
        let i : Fin 6 := ⟨n, bound⟩
        have width : savedOffset i + 8 ≤ 48 := by dsimp [savedOffset]; omega
        rw [store64_outside, ih]
        rw [← BitVec.sub_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : savedOffset i < 2 ^ 64)]
        have limit := (p - savedBase s).isLt
        omega
      next _ => exact ih
  exact frame 6

private theorem slots_separate (i j : Fin 6) (diff : i ≠ j) (left : Fin 8) :
    8 ≤ (BitVec.ofNat 64 (savedOffset i + left.val) - BitVec.ofNat 64 (savedOffset j)).toNat := by
  have distinct : i.val ≠ j.val := fun e => diff (Fin.ext e)
  have li := i.isLt
  have lj := j.isLt
  have lb := left.isLt
  simp only [savedOffset, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem frame_saved_word (r : HmacRoutine) (s : Cpu) (i : Fin 6) :
    (enteredFrame r s).mem.readSize .q (savedBase s + BitVec.ofNat 64 (savedOffset i)) = s.regs.get (savedReg i) := by
  rw [frame_saved_memory]
  have words (n : Nat) (written : i.val < n) :
      (pushedMemory s n).readSize .q (savedBase s + BitVec.ofNat 64 (savedOffset i)) = s.regs.get (savedReg i) := by
    induction n with
    | zero => omega
    | succ n ih =>
      unfold pushedMemory
      split
      next bound =>
        let j : Fin 6 := ⟨n, bound⟩
        by_cases same : i = j
        · subst i
          exact read64_write64 _ _ _
        · have diff : i.val ≠ n := fun eq => same (Fin.ext eq)
          refine (Mem.readN_congr _ _ _ 8 ?_).trans (ih (by omega))
          intro k hk
          apply store64_outside
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Crypto.ARM64.Imported.bv_add_sub_add_left]
          exact slots_separate i j same ⟨k, hk⟩
      next _ => exact ih (by have := i.isLt; omega)
  exact words 6 i.isLt

theorem entered_frame_direction (r : HmacRoutine) (s : Cpu) :
    (enteredFrame r s).flags.df = s.flags.df := by cases r <;> rfl

end Crypto.HMACSHA256.X86_64
