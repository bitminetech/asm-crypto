import Proofs.HMACSHA256.RISCV64CopyTail
import Proofs.HMACSHA256.Reference

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_outside read64_eq_of_cells)
open Crypto.ARM64.Imported (address_delta)

theorem key_address_decoded :
    decodeRange key 0x40 6 = some [
      .scalar ⟨.load .double 6#5 9#5 16#64, 4⟩,
      .scalar ⟨.addi 5#5 0#5 64#64, 4⟩,
      .scalar ⟨.branch .ltu 5#5 6#5 56#64, 4⟩,
      .scalar ⟨.load .double 30#5 9#5 8#64, 4⟩,
      .scalar ⟨.add 30#5 30#5 9#5, 2⟩,
      .scalar ⟨.add 29#5 0#5 18#5, 2⟩] := by decide +kernel

def shortKeyState (s : CPU) : CPU :=
  let keyAddr := s.reg 9#5
  let st := s.put 6#5 (s.mem.read64 (keyAddr + 16#64))
  let st := st.put 5#5 64#64
  let st := st.put 30#5 (keyAddr + s.mem.read64 (keyAddr + 8#64))
  let st := st.put 29#5 (s.reg 18#5)
  st.advance 20

theorem key_address_short (s : CPU)
    (short : (s.mem.read64 (s.reg 9#5 + 16#64)).toNat ≤ 64) :
    runRange key 0x40 6 s = some (shortKeyState s) := by
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  have branch : ¬64 < (s.mem.read64 (16#64 + s.reg 9#5)).toNat := by
    rw [BitVec.add_comm]
    omega
  unfold runRange
  rw [key_address_decoded]
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, Branch.taken,
    BitVec.ult, Width.load, zero, branch, shortKeyState, BitVec.add_comm]
  simp [CPU.advance, CPU.put, Vector.set_set, BitVec.add_assoc]

/-- Follow the short-key helper body through zeroing, the public length test,
and the word and byte copy loops. The result contains the complete K0 block. -/
theorem short_key_body (s : CPU) (input : ByteList) (short : input.bytes.size ≤ 64)
    (offsetAt : s.mem.read64 (s.reg 9#5 + 8#64) = BitVec.ofNat 64 input.offset)
    (countAt : s.mem.read64 (s.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size)
    (inputAt : ∀ i, i < input.bytes.size →
      s.mem.read8 (s.reg 9#5 + BitVec.ofNat 64 (input.offset + i)) = input.bytes[i]!.toBitVec)
    (headerApart : ∀ pos : Addr, pos = s.reg 9#5 + 8#64 ∨ pos = s.reg 9#5 + 16#64 →
      ∀ i : Fin 8, 64 ≤ (pos + BitVec.ofNat 64 i.val - s.reg 18#5).toNat)
    (bytesApart : ∀ i, i < input.bytes.size →
      64 ≤ (s.reg 9#5 + BitVec.ofNat 64 (input.offset + i) - s.reg 18#5).toNat) :
    ∃ cleared prepared atTail out,
      runRange key 0x20 8 s = some cleared ∧
      runRange key 0x40 6 cleared = some prepared ∧
      wordCycles false prepared (input.bytes.size / 8 + 1) = some atTail ∧
      byteCycles false atTail (input.bytes.size % 8 + 1) = some out ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 18#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, 64 ≤ (p - s.reg 18#5).toNat → out.mem.cells p = s.mem.cells p) ∧
      out.pc = s.pc + 94#64 ∧ out.reg 2#5 = s.reg 2#5 ∧
      prepared.pc = s.pc + 52#64 ∧ prepared.reg 30#5 = s.reg 9#5 + BitVec.ofNat 64 input.offset ∧
      prepared.reg 29#5 = s.reg 18#5 ∧ prepared.reg 6#5 = BitVec.ofNat 64 input.bytes.size ∧
      cleared.mem.read64 (cleared.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size := by
  let cleared : CPU := { s with
    pc := s.pc + 32#64
    mem := writeWords s.mem (s.reg 18#5) (fun _ => 0#64) 8 }
  have zeroed : runRange key 0x20 8 s = some cleared := key_zero s
  obtain ⟨z, zrun, zeroBytes, zeroFrame⟩ := key_zero_byte s
  have se : z = cleared := Option.some.inj (zrun.symm.trans zeroed)
  subst z
  have memory : cleared.mem = writeWords s.mem (s.reg 18#5) (fun _ => 0#64) 8 := rfl
  have loadHeader (p : Addr) (part : p = s.reg 9#5 + 8#64 ∨ p = s.reg 9#5 + 16#64) :
      cleared.mem.read64 p = s.mem.read64 p := by
    apply read64_eq_of_cells
    intro i
    rw [memory]
    exact writeWords_outside _ _ _ 8 _ (headerApart _ part i)
  have readOffset : cleared.mem.read64 (cleared.reg 9#5 + 8#64) = BitVec.ofNat 64 input.offset :=
    (loadHeader _ (Or.inl rfl)).trans offsetAt
  have readCount : cleared.mem.read64 (cleared.reg 9#5 + 16#64) = BitVec.ofNat 64 input.bytes.size :=
    (loadHeader _ (Or.inr rfl)).trans countAt
  have lengthSmall : input.bytes.size < 2 ^ 64 := by omega
  have stillShort : (cleared.mem.read64 (cleared.reg 9#5 + 16#64)).toNat ≤ 64 := by
    rw [readCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall]
    exact short
  let prepared := shortKeyState cleared
  have src : prepared.reg 30#5 = s.reg 9#5 + BitVec.ofNat 64 input.offset := by
    simp (config := { decide := true }) [prepared, shortKeyState, readOffset]
    rfl
  have dst : prepared.reg 29#5 = s.reg 18#5 := by
    simp (config := { decide := true }) [prepared, shortKeyState]
    rfl
  have length : prepared.reg 6#5 = BitVec.ofNat 64 input.bytes.size := by
    simp (config := { decide := true }) [prepared, shortKeyState, readCount]
  have apart (i : Nat) (hi : i < input.bytes.size) :
      input.bytes.size ≤ (prepared.reg 30#5 + BitVec.ofNat 64 i - prepared.reg 29#5).toNat := by
    rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact short.trans (bytesApart i hi)
  obtain ⟨atTail, out, words, tail, pc, _, bytes, frame, sp⟩ :=
    complete_copy false prepared input.bytes.size length lengthSmall apart
  have prepSP : prepared.reg 2#5 = s.reg 2#5 := by
    simp (config := { decide := true }) [prepared, shortKeyState]
    rfl
  have pcShort : out.pc = s.pc + 94#64 := by
    rw [pc]
    change s.pc + 32#64 + 20#64 + 42#64 = _
    simp only [BitVec.add_assoc] <;> rfl
  refine ⟨cleared, prepared, atTail, out, zeroed, key_address_short _ stillShort, words, tail, ?_, ?_,
    pcShort, (sp _ (by decide) (by decide) (by decide) (by decide)).trans prepSP, ?_, src, dst, length, readCount⟩
  · intro i
    rw [hmacKey_short_byte input short i]
    by_cases existsByte : i.val < input.bytes.size
    · rw [if_pos existsByte]
      have copied := bytes i.val existsByte
      rw [src, dst, BitVec.add_assoc, ← BitVec.ofNat_add] at copied
      rw [copied]
      change cleared.mem.read8 (s.reg 9#5 + BitVec.ofNat 64 (input.offset + i.val)) = _
      unfold Arm64.Memory.read8
      rw [zeroFrame _ (bytesApart i.val existsByte)]
      exact inputAt i.val existsByte
    · rw [if_neg existsByte]
      have outside : input.bytes.size ≤
          (s.reg 18#5 + BitVec.ofNat 64 i.val - prepared.reg 29#5).toNat := by
        rw [dst, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
        omega
      unfold Arm64.Memory.read8
      rw [frame _ outside]
      exact zeroBytes i
  · intro p outside
    have h : input.bytes.size ≤ (p - prepared.reg 29#5).toNat := by
      rw [dst]
      exact short.trans outside
    exact (frame p h).trans (zeroFrame p outside)
  · change s.pc + 32#64 + 20#64 = _
    rw [BitVec.add_assoc]
    rfl

end Crypto.HMACSHA256.RISCV64
