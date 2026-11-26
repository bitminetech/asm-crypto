import Proofs.RISCV64.CounterLoop
import Proofs.ARM64.ImportedCompression

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (index_shift_two compress_eq_rounds)
open Crypto.Reference.WordModel (addH specRoundStep)

private theorem round_linear : roundBody.all Instruction.linear = true := by decide +kernel

private theorem round_latch_execution (base : Addr) (s : CPU) (pc : s.pc = base + 0x284) :
    ImageExecution base s (latch 64#64 (-186)) (run (latch 64#64 (-186)) s) :=
  latch_execution base s 0x284 64 (-186) pc
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem round_latch_state (base : Addr) (s : CPU) (t : Fin 64)
    (pc : s.pc = base + 0x284)
    (counter : s.reg 15 = BitVec.ofNat 64 t.val) :
    let out := run (latch 64#64 (-186)) s
    out.pc = (if t.val + 1 < 64 then base + 0x1d0 else base + 0x28e) ∧
      out.reg 15 = BitVec.ofNat 64 (t.val + 1) ∧ out.reg 2 = s.reg 2 ∧
      out.reg 10 = s.reg 10 ∧ out.mem = s.mem ∧ working out = working s := by
  have small := t.isLt
  obtain ⟨exit, index, mem, keep⟩ := latch_state s 64 (-186) t.val (by omega) (by decide) counter
  have position : (run (latch 64#64 (-186)) s).pc =
      (if t.val + 1 < 64 then base + 0x1d0 else base + 0x28e) := by
    rw [exit, pc]
    split <;> simp (config := { decide := true }) [BitVec.add_assoc]
  refine ⟨position, index, keep 2 (by decide) (by decide), keep 10 (by decide) (by decide), mem, ?_⟩
  simp only [working, keep _ (by decide : (8 : Reg) ≠ 5) (by decide : (8 : Reg) ≠ 15),
    keep _ (by decide : (9 : Reg) ≠ 5) (by decide : (9 : Reg) ≠ 15),
    keep _ (by decide : (18 : Reg) ≠ 5) (by decide : (18 : Reg) ≠ 15),
    keep _ (by decide : (19 : Reg) ≠ 5) (by decide : (19 : Reg) ≠ 15),
    keep _ (by decide : (20 : Reg) ≠ 5) (by decide : (20 : Reg) ≠ 15),
    keep _ (by decide : (21 : Reg) ≠ 5) (by decide : (21 : Reg) ≠ 15),
    keep _ (by decide : (22 : Reg) ≠ 5) (by decide : (22 : Reg) ≠ 15),
    keep _ (by decide : (23 : Reg) ≠ 5) (by decide : (23 : Reg) ≠ 15)]

def roundCycle : List Instruction := roundBody ++ latch 64#64 (-186)

def roundCode : Nat → List Instruction
  | 0 => []
  | n + 1 => roundCode n ++ roundCycle

private theorem round_code_no_return (n : Nat) (i : Instruction) (hi : i ∈ roundCode n) :
    i.op ≠ .ret := by
  induction n with
  | zero => simp [roundCode] at hi
  | succ n ih =>
    rcases List.mem_append.mp hi with older | single
    · exact ih older
    · have checked : roundCycle.all (fun j => !(j.op == .ret)) = true := by decide +kernel
      have this := List.all_eq_true.mp checked i single
      simpa using this

private theorem round_cycle (base : Addr) (s : CPU) (t : Fin 64)
    (pc : s.pc = base + 0x1d0) (counter : s.reg 15 = BitVec.ofNat 64 t.val) :
    let out := run roundCycle s
    ImageExecution base s roundCycle out ∧
      out.pc = (if t.val + 1 < 64 then base + 0x1d0 else base + 0x28e) ∧
      out.reg 15 = BitVec.ofNat 64 (t.val + 1) ∧ out.reg 2 = s.reg 2 ∧
      out.reg 10 = s.reg 10 ∧ out.mem = s.mem ∧
      working out = Crypto.ARM64.Round.fipsRound (working s)
        (s.mem.read32 (s.reg 10 + BitVec.ofNat 64 (4 * t.val)))
        (s.mem.read32 (s.reg 2 + BitVec.ofNat 64 (4 * t.val))) := by
  dsimp only [roundCycle]
  rw [run_append]
  obtain ⟨mem, sp, k, idx, advance⟩ := round_frame s
  have middle : (run roundBody s).pc = base + 0x284 := by
    rw [advance, pc, BitVec.add_assoc]; rfl
  obtain ⟨pc', index, stack, table, memory, work⟩ :=
    round_latch_state base (run roundBody s) t middle (idx.trans counter)
  have straight := ImageExecution.linear_run base s roundBody 0x1d0 pc
    (by decide) roundBody_decoded round_linear
  refine ⟨straight.append (round_latch_execution base _ middle) ?_,
    pc', index, stack.trans sp, table.trans k, memory.trans mem, ?_⟩
  · intro i hi hr
    have this := List.all_eq_true.mp round_linear i hi
    simp [Instruction.linear, hr] at this
  · rw [work, round_value, tableAddress, tableAddress, counter, index_shift_two t]

private theorem round_prefix (base : Addr) (s : CPU) (W : Vector Word 64)
    (pc : s.pc = base + 0x1d0) (counter : s.reg 15 = 0)
    (constants : ∀ i : Fin 64,
      s.mem.read32 (s.reg 10 + BitVec.ofNat 64 (4 * i.val)) = Crypto.Reference.WordModel.K[i.val]!)
    (schedule : ∀ i : Fin 64,
      s.mem.read32 (s.reg 2 + BitVec.ofNat 64 (4 * i.val)) = W[i.val]!)
    (n : Nat) (bound : n ≤ 64) :
    let out := run (roundCode n) s
    ImageExecution base s (roundCode n) out ∧
      out.pc = (if n < 64 then base + 0x1d0 else base + 0x28e) ∧
      out.reg 15 = BitVec.ofNat 64 n ∧ out.reg 2 = s.reg 2 ∧
      out.reg 10 = s.reg 10 ∧ out.mem = s.mem ∧
      working out = Fin.foldl n (fun work i => specRoundStep W i.val work) (working s) := by
  induction n with
  | zero =>
    simpa [roundCode, run] using And.intro (ImageExecution.nil (base := base) s)
      (And.intro pc (And.intro counter (show s.reg 2 = s.reg 2 ∧ s.reg 10 = s.reg 10 ∧
        s.mem = s.mem ∧ working s = working s from ⟨rfl, rfl, rfl, rfl⟩)))
  | succ n ih =>
    have small : n < 64 := by omega
    obtain ⟨prior, loopPC, idx, sp, k, mem, before⟩ := ih (by omega)
    let mid := run (roundCode n) s
    obtain ⟨cycle, afterPC, afterIdx, afterSp, afterK, afterMem, afterWork⟩ :=
      round_cycle base mid ⟨n, small⟩ (by simpa only [if_pos small] using loopPC) idx
    dsimp only [roundCode]
    rw [run_append]
    refine ⟨prior.append cycle (round_code_no_return n), afterPC, afterIdx,
      afterSp.trans sp, afterK.trans k, afterMem.trans mem, ?_⟩
    rw [afterWork, before, mem, sp, k, constants ⟨n, small⟩, schedule ⟨n, small⟩, Fin.foldl_succ_last]
    rfl

/-- Execution of all 64 rounds from the linked loop entry. The input working
hash and the supplied 16-word block are arbitrary. The supplied block's
schedule and K must already occupy their designated tables. -/
theorem rounds_compress (base : Addr) (s : CPU) (M : Vector Word 16)
    (pc : s.pc = base + 0x1d0) (counter : s.reg 15 = 0)
    (constants : ∀ i : Fin 64,
      s.mem.read32 (s.reg 10 + BitVec.ofNat 64 (4 * i.val)) = Crypto.Reference.WordModel.K[i.val]!)
    (schedule : ∀ i : Fin 64,
      s.mem.read32 (s.reg 2 + BitVec.ofNat 64 (4 * i.val)) = (Crypto.Reference.WordModel.schedule M)[i.val]!) :
    ∃ out, ImageExecution base s (roundCode 64) out ∧ out.pc = base + 0x28e ∧
      out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧ out.mem = s.mem ∧
      addH (working s) (working out) = Crypto.Reference.WordModel.compress (working s) M := by
  obtain ⟨exec, exit, _, stack, table, same, work⟩ :=
    round_prefix base s (Crypto.Reference.WordModel.schedule M) pc counter constants schedule 64 (by decide)
  exact ⟨run (roundCode 64) s, exec, by simpa using exit, stack, table, same,
    (congrArg (addH (working s)) work).trans (compress_eq_rounds _ M)⟩

end Crypto.RISCV64
