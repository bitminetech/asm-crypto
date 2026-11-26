import Proofs.RISCV64.Block
import Proofs.RISCV64.BlockControl

namespace Crypto.RISCV64

private def loopRegisters : List Reg := [1, 2, 10, 11, 12, 13, 14, 16]

private def skipsLoopRegs (i : Instruction) : Bool :=
  loopRegisters.all fun r => i.op.destination != some r

private theorem skips_reg {i : Instruction} {r : Reg}
    (h : skipsLoopRegs i = true) (hr : r ∈ loopRegisters) :
    i.op.destination ≠ some r := by
  have eq := List.all_eq_true.mp h r hr
  simpa using eq

private theorem loadSkips (n : Nat) : ∀ i ∈ loadCode n, skipsLoopRegs i = true := by
  induction n with
  | zero => simp [loadCode]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with before | one
    · exact ih i before
    · have checked : loadCycle.all skipsLoopRegs = true := by decide +kernel
      exact List.all_eq_true.mp checked i one

private theorem expansionSkips (n : Nat) : ∀ i ∈ expansionCode n, skipsLoopRegs i = true := by
  induction n with
  | zero => simp [expansionCode]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with before | one
    · exact ih i before
    · have checked : expansionCycle.all skipsLoopRegs = true := by decide +kernel
      exact List.all_eq_true.mp checked i one

private theorem roundSkips (n : Nat) : ∀ i ∈ roundCode n, skipsLoopRegs i = true := by
  induction n with
  | zero => simp [roundCode]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with before | one
    · exact ih i before
    · have checked : roundCycle.all skipsLoopRegs = true := by decide +kernel
      exact List.all_eq_true.mp checked i one

private theorem hashSkips : loadHashBody.all skipsLoopRegs = true := by decide +kernel
private theorem feedSkips : feedForward.all skipsLoopRegs = true := by decide +kernel

private theorem preserve_control {base : Addr} {s a b c d out : CPU}
    (load : ImageExecution base s (loadCode 16) a)
    (expand : ImageExecution base a (expansionCode 48) b)
    (start : ImageExecution base b loadHashBody c)
    (round : ImageExecution base c (roundCode 64) d)
    (feed : ImageExecution base d feedForward out)
    (r : Reg) (hr : r ∈ loopRegisters) : out.reg r = s.reg r := by
  exact (feed.register_unchanged r (fun i hi => skips_reg (List.all_eq_true.mp feedSkips i hi) hr)).trans
    ((round.register_unchanged r (fun i hi => skips_reg (roundSkips _ i hi) hr)).trans
      ((start.register_unchanged r (fun i hi => skips_reg (List.all_eq_true.mp hashSkips i hi) hr)).trans
        ((expand.register_unchanged r (fun i hi => skips_reg (expansionSkips _ i hi) hr)).trans
          (load.register_unchanged r (fun i hi => skips_reg (loadSkips _ i hi) hr)))))

/-- A complete nonempty block iteration from the outer latch. The block
pointer advances by 64, the counter decrements exactly once and the stack
outside the W and H arrays retains its original cells. -/
theorem block_iteration (base : Addr) (s : CPU)
    (pc : s.pc = base + 0xf2) (nonempty : s.reg 13#5 ≠ 0)
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ i, i < image.size → 288 ≤ (base + BitVec.ofNat 64 i - s.reg 2).toNat)
    (inputApart : ∀ i : Fin 16, ∀ d : Fin 4,
      288 ≤ (s.reg 12 + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 d.val - s.reg 2).toNat) :
    ∃ entered afterLoad afterExpansion startRounds endRounds compressed out,
      ImageExecution base s [blockGuard, startWords] entered ∧
      ImageExecution base entered (loadCode 16) afterLoad ∧
      ImageExecution base afterLoad (expansionCode 48) afterExpansion ∧
      ImageExecution base afterExpansion loadHashBody startRounds ∧
      ImageExecution base startRounds (roundCode 64) endRounds ∧
      ImageExecution base endRounds feedForward compressed ∧
      ImageExecution base compressed advanceBlock out ∧ out.pc = base + 0xf2 ∧
      out.reg 12 = s.reg 12 + 64 ∧ out.reg 13 = s.reg 13 - 1 ∧
      out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧ out.reg 11 = s.reg 11 ∧
      out.reg 14 = s.reg 14 ∧ out.reg 16 = s.reg 16 ∧ out.reg 1 = s.reg 1 ∧
      storedHash out = SHS.SHA256.compress (storedHash s) (blockWords s.mem (s.reg 12)) ∧
      (∀ p, 288 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  let head := blockGuard.step s
  obtain ⟨guardPath, atInit, headMem, headRegs⟩ := block_guard base s pc
  have enterPC : head.pc = base + 0xf6 := by simpa only [if_neg nonempty] using atInit
  let entered := startWords.step head
  obtain ⟨initPath, atLoad, zero, initMem⟩ := initialize_words base head enterPC
  have mem : entered.mem = s.mem := initMem.trans headMem
  have enteredReg (r : Reg) (hr : r ≠ 15) : entered.reg r = s.reg r := by
    have first : head.reg r = s.reg r := by
      unfold CPU.reg
      change (if r = 0 then 0 else head.regs[r.toNat]) = _
      rw [headRegs]
    have second : entered.reg r = head.reg r := by
      apply startWords.reg_unchanged
      exact fun h => hr (Option.some.inj h.symm)
    exact second.trans first
  have stack := enteredReg 2 (by decide)
  have payload := enteredReg 12 (by decide)
  obtain ⟨a, b, c, d, compressed, load, expand, start, rounds, feed, atEnd, value, sp, frame⟩ :=
    block_compression base entered atLoad zero (mem ▸ loaded)
      ((enteredReg 10 (by decide)).trans constants)
      (fun j hj => by rw [stack]; have := codeApart j hj; omega)
      (fun i j => by rw [payload, stack]; have := inputApart i j; omega)
  let out := run advanceBlock compressed
  obtain ⟨advance, back, finalMem, ptr, left⟩ := next_block base compressed atEnd
  have saved (r : Reg) (hr : r ∈ loopRegisters) (h : r ≠ 15) : compressed.reg r = s.reg r :=
    (preserve_control load expand start rounds feed r hr).trans (enteredReg r h)
  have tailKeeps (r : Reg) (hr : r ≠ 12) (hs : r ≠ 13) : out.reg r = compressed.reg r := by
    apply run_reg_unchanged
    intro i hi
    simp only [advanceBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact fun h => hr (Option.some.inj h.symm)
    · exact fun h => hs (Option.some.inj h.symm)
    · simp [Op.destination]
  have unchanged (r : Reg) (hr : r ∈ loopRegisters) (h1 : r ≠ 12) (h2 : r ≠ 13)
      (h3 : r ≠ 15) : out.reg r = s.reg r :=
    (tailKeeps r h1 h2).trans (saved r hr h3)
  have final : out.mem = compressed.mem := finalMem
  have hash : storedHash out =
      SHS.SHA256.compress (storedHash s) (blockWords s.mem (s.reg 12)) := by
    change storedHash out = SHS.SHA256.compress (storedHash s) (blockWords s.mem (s.reg 12))
    have old : storedHash entered = storedHash s := by simp only [storedHash, mem, stack]
    have after : storedHash out = storedHash compressed := by
      simp only [storedHash, final, tailKeeps 2 (by decide) (by decide)]
    rw [after, value, old, mem, payload]
  refine ⟨entered, a, b, c, d, compressed, out,
    guardPath.append initPath ?_, load, expand, start, rounds, feed, advance, back, ?_, ?_,
    unchanged 2 (by decide) (by decide) (by decide) (by decide),
    unchanged 10 (by decide) (by decide) (by decide) (by decide),
    unchanged 11 (by decide) (by decide) (by decide) (by decide),
    unchanged 14 (by decide) (by decide) (by decide) (by decide),
    unchanged 16 (by decide) (by decide) (by decide) (by decide),
    unchanged 1 (by decide) (by decide) (by decide) (by decide), hash, ?_⟩
  · intro i hi
    obtain rfl := List.mem_singleton.mp hi
    decide
  · rw [ptr, saved 12 (by decide) (by decide)]
  · rw [left, saved 13 (by decide) (by decide)]
  · intro p hp
    rw [final, frame p (by rw [stack]; exact hp), mem]

end Crypto.RISCV64
