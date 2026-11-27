import Proofs.HMACSHA256.RISCV64Setup
import Proofs.HMACSHA256.Callee

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.ARM64.Imported (memoryBytes32 address_delta)

theorem key_call_decoded :
    decodeRange key 0x80 3 = some [
      .scalar ⟨.add 10#5 0#5 9#5, 2⟩,
      .scalar ⟨.add 11#5 0#5 18#5, 2⟩,
      .jal 1#5 0xfffffffffffff0ec#64] := by decide +kernel

def longKeyCall (s : CPU) : CPU :=
  let st := (s.put 10#5 (s.reg 9#5)).put 11#5 (s.reg 18#5)
  setPC (st.put 1#5 (s.pc + 8#64)) (s.pc + 0xfffffffffffff0f0#64)

theorem key_call (s : CPU) : runRange key 0x80 3 s = some (longKeyCall s) := by
  unfold runRange
  rw [key_call_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, longKeyCall, setPC, zero, BitVec.add_assoc]
  rfl

set_option maxRecDepth 8192 in
/-- Execute the linked long-key call, then use the existing RV64 SHA-256
baseline to establish the complete key block with its trailing zeros. -/
theorem long_key_after_clear (s : CPU) (input : ByteList) (long : 64 < input.bytes.size)
    (base : Addr) (extent : Nat) (entry : CallerEntry base (longKeyCall s) input extent)
    (zeros : ∀ i : Fin 64, 32 ≤ i.val →
      s.mem.read8 (s.reg 18#5 + BitVec.ofNat 64 i.val) = 0#8)
    (stackApart : ∀ i : Fin 64, 32 ≤ i.val →
      ¬(callerStack (longKeyCall s)).Contains (s.reg 18#5 + BitVec.ofNat 64 i.val)) :
    ∃ out, runRange key 0x80 3 s = some (longKeyCall s) ∧
      runUntilReturn base (longKeyCall s) (callSteps input.bytes.size) = some out ∧
      CallResult (longKeyCall s) out input ∧ FrameResult (longKeyCall s) out ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 18#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) := by
  obtain ⟨out, run, result, frame, _⟩ := sha256_callee base (longKeyCall s) input extent entry
  have dstBits : (longKeyCall s).reg 11#5 = s.reg 18#5 := by
    unfold longKeyCall
    rw [setPC_reg, reg_put, if_neg (by decide : (11#5 : Reg) ≠ 0),
      if_neg (by decide : (11#5 : Reg) ≠ 1#5), reg_put,
      if_neg (by decide : (11#5 : Reg) ≠ 0), if_pos rfl]
  have dst : (longKeyCall s).reg 11 = s.reg 18#5 := dstBits
  refine ⟨out, key_call s, run, result, frame, ?_⟩
  intro i
  rw [hmacKey_long_byte input long entry.length]
  by_cases front : i.val < 32
  · rw [if_pos front]
    let j : Fin 32 := ⟨i.val, front⟩
    have value := congrArg (fun digest : Vector (BitVec 8) 32 => digest[j.val]) result.digest
    have written : out.mem.read8 ((longKeyCall s).reg 11 + BitVec.ofNat 64 i.val) =
        ((sha256 input).2[j.val]).toBitVec := by
      simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map] using value
    have bound : j.val < (EthLib.Base.packBytes (sha256 input).2).size := by
      change j.val < (sha256 input).2.toArray.size
      rw [(sha256 input).2.size_toArray]
      exact j.isLt
    rw [getElem!_pos (EthLib.Base.packBytes (sha256 input).2) i.val bound, ← dst]
    exact written
  · rw [if_neg front]
    let p := s.reg 18#5 + BitVec.ofNat 64 i.val
    have outside : ¬ (callerOutput (longKeyCall s)).Contains p := by
      intro inside
      change ((longKeyCall s).reg 11).toNat ≤ p.toNat ∧
        p.toNat < ((longKeyCall s).reg 11).toNat + 32 at inside
      rw [dst] at inside
      have delta : (p - s.reg 18#5).toNat = i.val := by
        rw [show p - s.reg 18#5 = BitVec.ofNat 64 i.val from address_delta _ _,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      rw [BitVec.toNat_sub] at delta
      have baseBound := (s.reg 18#5).isLt
      omega
    have unchanged := frame p (stackApart i (by omega)) outside
    unfold Arm64.Memory.read8
    rw [unchanged]
    exact zeros i (by omega)

end Crypto.HMACSHA256.RISCV64
