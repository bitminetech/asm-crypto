import Proofs.HMACSHA256.RISCV64Pad

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

def padWordEvents (width : Nat) (pc src dst disp : Addr) : List (List Access) :=
  [[.fetch pc width, .read (src + disp) .double],
   [.fetch (pc + BitVec.ofNat 64 width) 4],
   [.fetch (pc + BitVec.ofNat 64 (width + 4)) 4, .write (dst + disp) .double]]

def padEvents (width : Nat) (pc src dst : Addr) : Nat → List (List Access)
  | 0 => []
  | n + 1 => padEvents width pc src dst n ++
    padWordEvents width (pc + BitVec.ofNat 64 (n * (width + 8))) src dst (BitVec.ofNat 64 (8 * n))

private theorem run_events_append (a b : List Op) (s : CPU) :
    runOpsEvents (a ++ b) s = runOpsEvents a s ++ runOpsEvents b (runOps a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons op rest ih =>
    change _ :: runOpsEvents (rest ++ b) (op.step s) = _
    rw [ih]
    rfl

private theorem pad_word_events (s : CPU) (source : Reg) (width : Nat) (disp : Addr) :
    runOpsEvents (padWord source width disp) s =
      padWordEvents width s.pc (s.reg source) (s.reg 29#5) disp := by
  simp (config := {decide := true}) [padWord, padWordEvents, runOpsEvents,
    Op.accesses, Op.width, Crypto.RISCV64.Op.accesses, Op.step, Instruction.step,
    Width.load, BitVec.ofNat_add, BitVec.add_assoc]

private theorem pad_word_pc (s : CPU) (source : Reg) (width : Nat) (disp : Addr) :
    (runOps (padWord source width disp) s).pc = s.pc + BitVec.ofNat 64 (width + 8) := by
  simp [padWord, runOps, Op.step, Instruction.step, Width.load, Width.store,
    CPU.advance, CPU.put, CPU.write, BitVec.ofNat_add, BitVec.add_assoc]

private theorem pad_word_register (s : CPU) (source : Reg) (width : Nat) (disp : Addr)
    (r : Reg) (keep : r ≠ 31#5) : (runOps (padWord source width disp) s).reg r = s.reg r := by
  have keep' : r ≠ (31 : Reg) := keep
  by_cases zero : r = 0
  · rw [zero, reg_zero, reg_zero]
  have nz : r ≠ 0#5 := zero
  simp (config := { decide := true }) [padWord, runOps, Op.step, Instruction.step,
    Width.load, Width.store, reg_put, nz, keep]

theorem pad_code_events (s : CPU) (source : Reg) (width count : Nat) (keep : source ≠ 31#5) :
    runOpsEvents (padCode source width count) s =
      padEvents width s.pc (s.reg source) (s.reg 29#5) count := by
  have steps (n : Nat) :
      (runOps (padCode source width n) s).pc = s.pc + BitVec.ofNat 64 (n * (width + 8)) ∧
      ∀ r, r ≠ 31#5 → (runOps (padCode source width n) s).reg r = s.reg r := by
    induction n with
    | zero => simp [padCode, runOps]
    | succ n ih =>
      simp only [padCode, runOps, List.foldl_append]
      let mid := runOps (padCode source width n) s
      change (runOps (padWord source width _) mid).pc = _ ∧
        ∀ r, r ≠ 31#5 → (runOps (padWord source width _) mid).reg r = s.reg r
      refine ⟨?_, fun r kept => (pad_word_register mid source width _ r kept).trans (ih.2 r kept)⟩
      rw [pad_word_pc, ih.1, Nat.succ_mul]
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [padCode, run_events_append, ih, pad_word_events]
    rw [(steps n).1, (steps n).2 source keep, (steps n).2 29#5 (by decide)]
    rfl

set_option maxRecDepth 8192 in
/-- The entire ipad or opad trace depends only on the initial fetch address
and the two public buffer addresses. -/
theorem pad_execution_observes (outer : Bool) (base : Addr) (s out : CPU)
    (run : (if outer then runRange finish 0x54 24 s else runRange entry 0x80 24 s) = some out)
    (loaded : (if outer then finish else entry).Loaded
      (routineAddress base (if outer then finish else entry)) s.mem.read8)
    (readonly : RoutineReadOnly (if outer then finish else entry) base s.mem)
    (allowed : RangeAllowed (if outer then finish else entry) base (if outer then 0x54 else 0x80) 24 s) :
    ProgramExecution base s
      (padEvents (if outer then 4 else 2) s.pc (s.reg (if outer then 9#5 else 2#5)) (s.reg 29#5) 8) out := by
  cases outer <;> simp only [Bool.false_eq_true, if_false, if_true] at run loaded readonly allowed ⊢
  · have dec : decodeRange entry 0x80 24 = some (padCode 2#5 2 8) := by decide +kernel
    rw [← pad_code_events s 2#5 2 8 (by decide)]
    exact run_range_observes (.inl rfl) run loaded readonly allowed dec |>.1
  · rw [← pad_code_events s 9#5 4 8 (by decide)]
    exact run_range_observes (.inr (.inr rfl)) run loaded readonly allowed finish_pad_decoded |>.1

end Crypto.HMACSHA256.RISCV64
