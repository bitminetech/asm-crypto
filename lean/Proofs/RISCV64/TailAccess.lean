import Proofs.RISCV64.FixedAccess

namespace Crypto.RISCV64

private theorem tail_body_accesses (s : CPU) :
    dataTrace (copyByte ++ [tailBack]) s = [.read (s.reg 28 + s.reg 30) .byte, .write (s.reg 29 + s.reg 30) .byte] ∧
    (run (copyByte ++ [tailBack]) s).reg 30 = s.reg 30 + 1 ∧
    (run (copyByte ++ [tailBack]) s).reg 28 = s.reg 28 ∧ (run (copyByte ++ [tailBack]) s).reg 29 = s.reg 29 := by
  simp (config := { decide := true }) [copyByte, tailBack, run, dataTrace, Op.accesses, Instruction.step]
  all_goals simp (config := { decide := true }) [CPU.reg, CPU.put, CPU.advance, CPU.write]

attribute [local irreducible] run dataTrace Instruction.step

private theorem tail_cycle_accesses (s : CPU) :
    dataTrace tailCycle s = [.read (s.reg 28 + s.reg 30) .byte, .write (s.reg 29 + s.reg 30) .byte] ∧
    (run tailCycle s).reg 30 = s.reg 30 + 1 ∧
    (run tailCycle s).reg 28 = s.reg 28 ∧ (run tailCycle s).reg 29 = s.reg 29 := by
  have keep (r : Reg) : (tailGuard.step s).reg r = s.reg r :=
    tailGuard.reg_unchanged s r (by simp [tailGuard, Op.destination])
  have splitRun : run tailCycle s = run (copyByte ++ [tailBack]) (tailGuard.step s) := by
    simp only [run, tailCycle, List.foldl_cons]
  have noAccess : tailGuard.op.accesses s = [] := rfl
  have splitTrace : dataTrace tailCycle s = dataTrace (copyByte ++ [tailBack]) (tailGuard.step s) := by
    simp only [tailCycle, dataTrace, noAccess, List.nil_append]
  obtain ⟨trace, count, src, dst⟩ := tail_body_accesses (tailGuard.step s)
  exact ⟨splitTrace.trans (trace.trans (by simp only [keep])),
    (congrArg (CPU.reg · 30) splitRun).trans (count.trans (congrArg (· + 1) (keep 30))),
    (congrArg (CPU.reg · 28) splitRun).trans (src.trans (keep 28)),
    (congrArg (CPU.reg · 29) splitRun).trans (dst.trans (keep 29))⟩

def TailData (input padding : Addr) (size : Nat) : Access → Prop
  | .read addr .byte => InRegion input size addr .byte
  | .write addr .byte => InRegion padding size addr .byte
  | _ => False

private theorem TailData.enlarge {a : Access} {src dst : Addr} {n m : Nat}
    (inside : TailData src dst n a) (bound : n ≤ m) : TailData src dst m a := by
  cases a with
  | fetch => exact inside
  | read addr w | write addr w =>
    cases w <;> first
      | exact inside
      | obtain ⟨off, size, aligned, location⟩ := inside
        exact ⟨off, Nat.le_trans size bound, aligned, location⟩

private theorem tail_prefix_accesses (s : CPU) (n : Nat) (index : s.reg 30 = 0) :
    let out := run (tailPrefix n) s
    out.reg 30 = BitVec.ofNat 64 n ∧ out.reg 28 = s.reg 28 ∧ out.reg 29 = s.reg 29 ∧
    (∀ a ∈ dataTrace (tailPrefix n) s, TailData (s.reg 28) (s.reg 29) n a) := by
  induction n with
  | zero =>
    simpa [tailPrefix, run, dataTrace] using index
  | succ n ih =>
    obtain ⟨cursor, src, dst, before⟩ := ih
    obtain ⟨observed, next, src', dst'⟩ := tail_cycle_accesses (run (tailPrefix n) s)
    simp only [tailPrefix, run_append, dataTrace_append]
    refine ⟨?_, src'.trans src, dst'.trans dst, ?_⟩
    · rw [next, cursor, BitVec.ofNat_add]; rfl
    · intro a found
      rcases List.mem_append.mp found with early | late
      · exact (before a early).enlarge (Nat.le_succ _)
      · rw [observed, src, dst, cursor] at late
        simp only [List.mem_cons, List.not_mem_nil, or_false] at late
        rcases late with eq | eq <;> subst a
        all_goals exact ⟨n, Nat.le_refl _, Nat.mod_one _, rfl⟩

theorem tail_accesses (s : CPU) (n : Nat) (index : s.reg 30 = 0)
    (a : Access) (found : a ∈ dataTrace (tailCode n) s) : TailData (s.reg 28) (s.reg 29) n a := by
  rw [tailCode, dataTrace_append, empty_dataTrace (code := [tailGuard]) (by decide), List.append_nil] at found
  exact (tail_prefix_accesses s n index).2.2.2 a found

end Crypto.RISCV64
