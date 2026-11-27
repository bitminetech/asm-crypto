import Proofs.HMACSHA256.RISCV64Ranges
import Proofs.HMACSHA256.Pad

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_outside writeWords_byte read64_eq_of_cells maskedByte)

def padWord (source : Reg) (loadWidth : Nat) (disp : Addr) : List Op := [
  .scalar ⟨.load .double 31#5 source disp, loadWidth⟩,
  .scalar ⟨.xor 31#5 31#5 28#5, 4⟩,
  .scalar ⟨.store .double 31#5 29#5 disp, 4⟩]

def padCode (source : Reg) (loadWidth : Nat) : Nat → List Op
  | 0 => []
  | n + 1 => padCode source loadWidth n ++ padWord source loadWidth (BitVec.ofNat 64 (8 * n))

private theorem entry_pad_decoded :
    decodeRange entry 0x80 24 = some (padCode 2#5 2 8) := by decide +kernel

theorem finish_pad_decoded :
    decodeRange finish 0x54 24 = some (padCode 9#5 4 8) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4500000 in
set_option linter.unusedSimpArgs false in
theorem pad_range_allowed (outer : Bool) (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base (if outer then finish else entry) +
      (if outer then 0x54#64 else 0x80#64))
    (codeAligned : (routineAddress base (if outer then finish else entry)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (if outer then finish else entry))
      (if outer then finish else entry).image.size = true)
    (readAligned : (s.reg (if outer then 9#5 else 2#5)).toNat % 8 = 0)
    (writeAligned : (s.reg 29#5).toNat % 8 = 0)
    (readable : s.mem.canRead (s.reg (if outer then 9#5 else 2#5)) 64 = true)
    (writable : s.mem.canWrite (s.reg 29#5) 64 = true) :
    RangeAllowed (if outer then finish else entry) base (if outer then 0x54 else 0x80) 24 s := by
  cases outer <;> simp only [Bool.false_eq_true, if_false, if_true] at pc codeAligned exec readAligned readable ⊢
  · refine ⟨_, entry_pad_decoded, ?_⟩
    simp only [padCode, padWord, List.cons_append, List.nil_append]
    hmac_range_permissions pc codeAligned exec readAligned readable writeAligned writable
  · refine ⟨_, finish_pad_decoded, ?_⟩
    simp only [padCode, padWord, List.cons_append, List.nil_append]
    hmac_range_permissions pc codeAligned exec readAligned readable writeAligned writable

private theorem padWord_eval (state : CPU) (source : Reg) (loadWidth : Nat) (disp : Addr) :
    runOps (padWord source loadWidth disp) state =
      let value := state.mem.read64 (state.reg source + disp) ^^^ state.reg 28#5
      { state.put 31#5 value with
        pc := state.pc + BitVec.ofNat 64 (loadWidth + 8)
        mem := state.mem.write64 (state.reg 29#5 + disp) value } := by
  simp (config := { decide := true }) [padWord, runOps, Op.step, Instruction.step, Width.load,
    Width.store, BitVec.ofNat_add, BitVec.add_assoc]
  simp [CPU.advance, CPU.put, CPU.write, Vector.set_set, BitVec.add_assoc]

private theorem reg_of_state (s : CPU) (pc : Addr) (mem : Memory) (r : Reg) :
    (CPU.mk pc s.regs mem).reg r = s.reg r := rfl

private def padValue (s : CPU) (source : Reg) (n : Nat) : Addr :=
  s.mem.read64 (s.reg source + BitVec.ofNat 64 (8 * n)) ^^^ s.reg 28#5

private structure PadPrefix (start out : CPU) (source : Reg) (loadWidth count : Nat) : Prop where
  memory : out.mem = writeWords start.mem (start.reg 29#5) (padValue start source) count
  registers : ∀ r, r ≠ 31#5 → out.reg r = start.reg r
  pc : out.pc = start.pc + BitVec.ofNat 64 (count * (loadWidth + 8))

private theorem padCode_run (s : CPU) (source : Reg) (loadWidth count : Nat)
    (keepSource : source ≠ 31#5) (bound : count ≤ 8)
    (separate : ∀ i : Fin 64, 64 ≤
      (s.reg source + BitVec.ofNat 64 i.val - s.reg 29#5).toNat) :
    PadPrefix s (runOps (padCode source loadWidth count) s) source loadWidth count := by
  induction count with
  | zero => exact ⟨rfl, fun _ _ => rfl, by simp [padCode, runOps]⟩
  | succ n ih =>
    let mid := runOps (padCode source loadWidth n) s
    have prev := ih (by omega)
    have m : mid.mem = writeWords s.mem (s.reg 29#5) (padValue s source) n := prev.memory
    have r (reg : Reg) (h : reg ≠ 31#5) : mid.reg reg = s.reg reg := prev.registers reg h
    have pc : mid.pc = s.pc + BitVec.ofNat 64 (n * (loadWidth + 8)) := prev.pc
    have sourceWord : mid.mem.read64 (mid.reg source + BitVec.ofNat 64 (8 * n)) =
        s.mem.read64 (s.reg source + BitVec.ofNat 64 (8 * n)) := by
      rw [r source keepSource]
      apply read64_eq_of_cells
      intro i
      rw [m, BitVec.add_assoc, ← BitVec.ofNat_add]
      apply writeWords_outside
      have away := separate ⟨8 * n + i.val, by have := i.isLt; omega⟩
      exact Nat.le_trans (by omega) away
    have exec : runOps (padCode source loadWidth (n + 1)) s =
        runOps (padWord source loadWidth (BitVec.ofNat 64 (8 * n))) mid := by
      simp only [padCode, runOps, List.foldl_append, mid]
    rw [exec, padWord_eval]
    refine ⟨?_, ?_, ?_⟩
    · change mid.mem.write64 (mid.reg 29#5 + BitVec.ofNat 64 (8 * n))
        (mid.mem.read64 (mid.reg source + BitVec.ofNat 64 (8 * n)) ^^^ mid.reg 28#5) = _
      rw [r 29#5 (by decide), r 28#5 (by decide), sourceWord, m]
      rfl
    · intro reg keep
      by_cases zero : reg = 0#5
      · subst reg
        exact (reg_zero _).trans (reg_zero _).symm
      · rw [reg_of_state, reg_put]
        have nz : reg ≠ (0 : Reg) := zero
        simp only [nz, keep, if_false]
        exact r reg keep
    · change mid.pc + BitVec.ofNat 64 (loadWidth + 8) =
        s.pc + BitVec.ofNat 64 ((n + 1) * (loadWidth + 8))
      rw [pc, Nat.succ_mul]
      simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem pad_run (s : CPU) (outer : Bool)
    (sep : ∀ i : Fin 64, 64 ≤
      (s.reg (if outer then 9#5 else 2#5) + BitVec.ofNat 64 i.val - s.reg 29#5).toNat) :
    ∃ out, (if outer then runRange finish 0x54 24 s else runRange entry 0x80 24 s) = some out ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 29#5 + BitVec.ofNat 64 i.val) =
        s.mem.read8 (s.reg (if outer then 9#5 else 2#5) + BitVec.ofNat 64 i.val) ^^^
          (s.reg 28#5).extractLsb' (8 * (i.val % 8)) 8) ∧
      (∀ p, 64 ≤ (p - s.reg 29#5).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ r, r ≠ 31#5 → out.reg r = s.reg r) ∧
      out.pc = s.pc + (if outer then 96#64 else 80#64) ∧
      (∀ p, out.mem.perm p = s.mem.perm p) ∧
      (∀ p n, s.mem.canRead p n = true → out.mem.canRead p n = true) := by
  let src : Reg := if outer then 9#5 else 2#5
  let width : Nat := if outer then 4 else 2
  let out := runOps (padCode src width 8) s
  have exec : (if outer then runRange finish 0x54 24 s else runRange entry 0x80 24 s) =
      some out := by
    cases outer <;> simp [src, width, out, runRange, entry_pad_decoded, finish_pad_decoded]
  have sourceKeeps : src ≠ 31#5 := by cases outer <;> decide
  have post := padCode_run s src width 8 sourceKeeps (by decide) sep
  have memory : out.mem = writeWords s.mem (s.reg 29#5) (padValue s src) 8 := post.memory
  refine ⟨out, exec, ?_, ?_, post.registers, ?_,
    fun p => by rw [memory]; exact Crypto.HMACSHA256.ARM64.writeWords_perm _ _ _ _ _,
    fun p n readable => by rw [memory]; exact Crypto.HMACSHA256.ARM64.writeWords_canRead _ _ _ _ _ _ readable⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have addr : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    rw [memory]
    have wrote := writeWords_byte s.mem (s.reg 29#5) (padValue s src) 8 (i.val / 8)
      byte lt (by decide)
    unfold padValue at wrote
    rw [maskedByte] at wrote
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, addr] using wrote
  · intro p h
    rw [memory]
    exact writeWords_outside _ _ _ 8 p h
  · cases outer <;> exact post.pc

end Crypto.HMACSHA256.RISCV64
