import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

def headerBody : List Instruction :=
  [⟨.load .double 5 10 8, 4⟩, ⟨.load .double 6 10 16, 4⟩, ⟨.add 12 10 5, 4⟩]

def lengthBody : List Instruction :=
  [⟨.andi 7 6 63, 4⟩, ⟨.srli 13 6 6, 4⟩, ⟨.slli 28 13 6, 4⟩,
   ⟨.add 28 28 12, 2⟩, ⟨.addi 29 2 288, 4⟩, ⟨.addi 30 0 0, 2⟩]

private theorem header_decoded : decodeSeq 0x12 3 = some headerBody := by decide +kernel
private theorem length_decoded : decodeSeq 0x3e 6 = some lengthBody := by decide +kernel

theorem header_loaded (base : Addr) (s : CPU) (pc : s.pc = base + 0x12) :
    let out := run headerBody s
    ImageExecution base s headerBody out ∧ out.pc = base + 0x1e ∧ out.mem = s.mem ∧
      out.reg 6 = s.mem.read64 (s.reg 10 + 16) ∧
      out.reg 12 = s.reg 10 + s.mem.read64 (s.reg 10 + 8) := by
  refine ⟨ImageExecution.linear_run base s _ 0x12 pc (by decide) header_decoded (by decide), ?_⟩
  simp (config := { decide := true }) [run, headerBody, Instruction.step, Width.load, pc, BitVec.add_assoc]

private theorem rem64 (count : Addr) :
    count &&& 63#64 = BitVec.ofNat 64 (count.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change count.toNat &&& (2^6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem blocks64 (count : Addr) :
    count >>> (6 : Nat) = BitVec.ofNat 64 (count.toNat / 64) := by
  apply BitVec.eq_of_toNat_eq
  have h := count.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega)]

private theorem tail64 (count : Addr) :
    (BitVec.ofNat 64 (count.toNat / 64) <<< (6 : Nat)) =
      BitVec.ofNat 64 (count.toNat / 64 * 64) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lengths_loaded (base : Addr) (s : CPU) (pc : s.pc = base + 0x3e) :
    let out := run lengthBody s
    let length := (s.reg 6).toNat
    ImageExecution base s lengthBody out ∧ out.pc = base + 0x52 ∧ out.mem = s.mem ∧
      out.reg 7 = BitVec.ofNat 64 (length % 64) ∧
      out.reg 13 = BitVec.ofNat 64 (length / 64) ∧
      out.reg 28 = s.reg 12 + BitVec.ofNat 64 (length / 64 * 64) ∧
      out.reg 29 = s.reg 2 + 288 ∧ out.reg 30 = 0 := by
  have linear : lengthBody.all Instruction.linear = true := by decide
  refine ⟨ImageExecution.linear_run base s _ 0x3e pc (by decide) length_decoded linear, ?_, ?_⟩
  · rw [linear_end_pc _ s linear, pc, BitVec.add_assoc]
    rfl
  · simp (config := { decide := true }) [run, lengthBody, Instruction.step,
      rem64, blocks64, tail64, BitVec.add_comm]

end Crypto.RISCV64
