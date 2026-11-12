import Proofs.ARM64.ImportedOuterLoop

/-!
Complete recorded outer-block loop, including the final zero-count branch.
The theorem covers n=0 and arbitrary counts below 2^64 and counts exactly
3,100 words per block plus the terminating branch. Fetching and whole-call
reference/baseline composition remain separate obligations.
-/
namespace Crypto.ARM64.Imported

def outerLoopCode (n : Nat) :=
  (List.replicate n blockIterationCode).flatten ++ blockSkipCode

theorem OuterFrame.setPC (s : Arm64.State) (pc : BitVec 64) : OuterFrame s (s.setPC pc) := by
  constructor
  · simp only [nonMemory, controlStable_pc]
  · exact nv_set_pc s pc
  · exact reg_set_pc s pc .x0
  · exact reg_set_pc s pc .x1
  · exact reg_set_pc s pc .x4
  · exact reg_set_pc s pc .x6

theorem outer_loop (s : Arm64.State) (ready : BlockReady s)
    (n : Nat) (bound : n < 2 ^ 64) (hc : s.readReg64 .x3 = BitVec.ofNat 64 n)
    (hr : ∀ (i : Fin n) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin n) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat) :
    ∃ out, runWords (outerLoopCode n) s = some out ∧ OuterFrame s out ∧
      out.pc = s.pc + 340#64 ∧ out.readReg64 .x2 = s.readReg64 .x2 + BitVec.ofNat 64 (64 * n) ∧
      out.readReg64 .x3 = 0#64 ∧
      savedHash out = Fin.foldl n
        (fun H (i : Fin n) => SHS.SHA256.compress H
          (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)))) (savedHash s) ∧
      BlockReady out ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  obtain ⟨mid, he, frame, pc, ptr, count, hash, readyMid, outside, readable⟩ :=
    outer_loop_prefix s ready n bound hc hr sep n (by omega)
  have zero : mid.readReg64 .x3 = 0#64 := by simpa only [Nat.sub_self] using count
  have skip := block_skip mid zero
  have cycles := (runCycles_words blockIterationCode n s).symm.trans he
  have whole := runWords_append_success cycles skip
  let out := mid.setPC (mid.pc + 340#64)
  refine ⟨out, whole, frame.trans (OuterFrame.setPC _ _), ?_, ?_, ?_, hash,
    readyMid.transport rfl rfl (reg_set_pc _ _ .x0), outside, readable⟩
  · change mid.pc + 340#64 = _
    rw [pc]
  · exact (reg_set_pc _ _ .x2).trans ptr
  · exact (reg_set_pc _ _ .x3).trans zero

set_option maxRecDepth 16384 in
theorem block_iteration_code_length : blockIterationCode.length = 3100 := by
  simp only [blockIterationCode, List.length_append, block_code_length]
  decide +kernel

theorem outer_loop_code_length (n : Nat) : (outerLoopCode n).length = 3100 * n + 1 := by
  have skip : blockSkipCode.length = 1 := by decide +kernel
  simp only [outerLoopCode, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate_nat, block_iteration_code_length, skip, Nat.mul_comm]

end Crypto.ARM64.Imported
