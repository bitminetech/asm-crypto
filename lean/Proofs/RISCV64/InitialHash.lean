import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

private def copyHashPair (i : Nat) : List Instruction :=
  [⟨.load .double 6 5 (BitVec.ofNat 64 (8*i)), 4⟩,
   ⟨.store .double 6 2 (BitVec.ofNat 64 (256 + 8*i)), 2⟩]

def initialHashCode : List Instruction :=
  [⟨.auipc 5 0, 4⟩, ⟨.addi 5 5 0x458, 4⟩] ++
    copyHashPair 0 ++ copyHashPair 1 ++ copyHashPair 2 ++ copyHashPair 3 ++
    [⟨.auipc 10 0, 4⟩, ⟨.addi 10 10 0x338, 4⟩, ⟨.addi 14 0 0, 2⟩]

private theorem initial_loaded_decode : decodeSeq 0xc8 13 = some initialHashCode := by decide +kernel

def copyInitialHash (m : Memory) (src dst : Addr) : Memory :=
  (List.range 4).foldl (fun before i =>
    before.write64 (dst + BitVec.ofNat 64 (8*i)) (before.read64 (src + BitVec.ofNat 64 (8*i)))) m

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem initial_tables (base : Addr) (s : CPU) (pc : s.pc = base + 0xc8) :
    let out := run initialHashCode s
    ImageExecution base s initialHashCode out ∧ out.pc = base + 0xf2 ∧
      out.reg 10 = base + BitVec.ofNat 64 constantsOffset ∧ out.reg 14 = 0 ∧
      out.reg 2 = s.reg 2 ∧
      out.mem = copyInitialHash s.mem (base + BitVec.ofNat 64 initialHashOffset) (s.reg 2 + 256) := by
  have linear : initialHashCode.all Instruction.linear = true := by decide
  refine ⟨ImageExecution.linear_run base s _ 0xc8 pc (by decide) initial_loaded_decode linear, ?_, ?_⟩
  · rw [linear_end_pc _ _ linear, pc, BitVec.add_assoc]; rfl
  · simp (config := { decide := true }) [initialHashCode, copyHashPair, run,
      Instruction.step, Width.load, Width.store, copyInitialHash, List.range_succ,
      constantsOffset, initialHashOffset, pc, BitVec.add_assoc]

end Crypto.RISCV64
