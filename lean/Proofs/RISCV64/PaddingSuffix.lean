import Proofs.RISCV64.Execution
import Proofs.ARM64.ImportedPaddingSuffix

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (lengthOffset)

def marker : List Instruction :=
  [⟨.add 31 29 7, 4⟩, ⟨.addi 5 0 128, 4⟩, ⟨.store .byte 5 31 0, 4⟩,
   ⟨.addi 16 0 1, 2⟩, ⟨.addi 5 0 56, 4⟩]

def oneBlock : Instruction := ⟨.branch .ltu 7 5 6, 4⟩
def twoBlocks : Instruction := ⟨.addi 16 0 2, 2⟩

def markerCode (rem : Nat) : List Instruction :=
  marker ++ oneBlock :: if rem < 56 then [] else [twoBlocks]

private theorem marker_decoded : decodeSeq 0x6a 5 = some marker := by decide +kernel
private theorem oneBlock_decoded : decodeAt 0x7c = some oneBlock := by decide +kernel
private theorem twoBlocks_decoded : decodeAt 0x80 = some twoBlocks := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem marker_loaded (base : Addr) (s : CPU) (rem : Nat) (rb : rem < 64)
    (pc : s.pc = base + 0x6a) (remaining : s.reg 7#5 = BitVec.ofNat 64 rem) :
    ∃ out, ImageExecution base s (markerCode rem) out ∧ out.pc = base + 0x82 ∧
      out.reg 16#5 = (if rem < 56 then 1#64 else 2#64) ∧
      out.reg 6#5 = s.reg 6#5 ∧ out.reg 29#5 = s.reg 29#5 ∧
      out.mem = s.mem.write8 (s.reg 29#5 + BitVec.ofNat 64 rem) 128 := by
  let mid := run marker s
  have linear : marker.all Instruction.linear = true := by decide
  have path := ImageExecution.linear_run base s marker 0x6a pc (by decide) marker_decoded linear
  have branchPC : mid.pc = base + 0x7c := by
    rw [linear_end_pc _ _ linear, pc, BitVec.add_assoc]; rfl
  have state : mid.reg 5#5 = 56#64 ∧ mid.reg 16#5 = 1#64 ∧
      mid.reg 6#5 = s.reg 6#5 ∧ mid.reg 7#5 = BitVec.ofNat 64 rem ∧ mid.reg 29#5 = s.reg 29#5 ∧
      mid.mem = s.mem.write8 (s.reg 29#5 + BitVec.ofNat 64 rem) 128 := by
    simp (config := { decide := true }) [mid, run, marker, Instruction.step, Width.store, remaining]
  obtain ⟨limit, count, size, rem', stack, wrote⟩ := state
  have taken : Branch.taken .ltu (mid.reg 7#5) (mid.reg 5#5) = decide (rem < 56) := by
    unfold Branch.taken
    rw [rem', limit, BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  have edge : decodeAt (mid.pc - base).toNat = some oneBlock := by
    rw [offset_eq branchPC (by decide)]
    exact oneBlock_decoded
  have noReturn (i : Instruction) (here : i ∈ marker) : i.op ≠ .ret :=
    Instruction.linear_ne_return (List.all_eq_true.mp linear i here)
  by_cases h : rem < 56
  · let out := oneBlock.step mid
    have move : out = { mid with pc := base + 0x82 } := by
      simp [out, oneBlock, Instruction.step, taken, h, branchPC, BitVec.add_assoc]
    have branch : ImageExecution base mid [oneBlock] out := .cons edge (by simp) (.nil _)
    refine ⟨out, ?_, ?_⟩
    · simpa only [markerCode, if_pos h] using path.append branch noReturn
    · rw [move, if_pos h]
      exact ⟨rfl, count, size, stack, wrote⟩
  · let afterBranch := oneBlock.step mid
    have step : afterBranch = mid.advance 4 := by simp [afterBranch, oneBlock, Instruction.step, taken, h]
    have extraPC : afterBranch.pc = base + 0x80 := by rw [step, pc_advance, branchPC, BitVec.add_assoc]; rfl
    let out := twoBlocks.step afterBranch
    have branch : ImageExecution base mid [oneBlock, twoBlocks] out :=
      .cons edge (by simp [oneBlock]) <|
        .cons (by rw [offset_eq extraPC (by decide)]; exact twoBlocks_decoded) (by simp) (.nil _)
    refine ⟨out, ?_, ?_⟩
    · simpa only [markerCode, if_neg h] using path.append branch noReturn
    · simp (config := { decide := true }) [out, twoBlocks, Instruction.step,
        step, branchPC, size, stack, wrote, h, BitVec.add_assoc]
      rfl

def storeDigit (shift : BitVec 6) (offset : Addr) : List Instruction :=
  [⟨.srli 31 5 shift, 4⟩, ⟨.store .byte 31 30 offset, 4⟩]

def lengthSuffix : List Instruction :=
  [⟨.slli 5 6 3, 4⟩, ⟨.slli 30 16 6, 4⟩, ⟨.add 30 30 29, 2⟩] ++
    storeDigit 56 (-8) ++ storeDigit 48 (-7) ++ storeDigit 40 (-6) ++ storeDigit 32 (-5) ++
    storeDigit 24 (-4) ++ storeDigit 16 (-3) ++ storeDigit 8 (-2) ++ [⟨.store .byte 5 30 (-1), 4⟩]

private theorem lengthSuffix_decoded : decodeSeq 0x82 18 = some lengthSuffix := by decide +kernel

def writeLength (m : Memory) (base : Addr) (nBits : Addr) : Memory :=
  (List.range 8).foldl (fun acc i =>
    acc.write8 (base + BitVec.ofNat 64 i) (nBits.extractLsb' (8 * (7-i)) 8)) m

private theorem word_end (s : CPU) (rem : Nat)
    (count : s.reg 16#5 = (if rem < 56 then 1#64 else 2#64)) :
    (s.reg 16#5 <<< (6 : Nat)) + s.reg 29#5 =
      (s.reg 29#5 + BitVec.ofNat 64 (lengthOffset rem)) + 8 := by
  rw [count]
  by_cases h : rem < 56 <;>
    simp (config := { decide := true }) [h, lengthOffset, BitVec.add_assoc] <;>
    apply BitVec.add_comm

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem length_suffix_loaded (base : Addr) (s : CPU) (rem : Nat)
    (pc : s.pc = base + 0x82) (count : s.reg 16#5 = if rem < 56 then 1#64 else 2#64) :
    let out := run lengthSuffix s
    ImageExecution base s lengthSuffix out ∧ out.pc = base + 0xc8 ∧
      out.mem = writeLength s.mem (s.reg 29#5 + BitVec.ofNat 64 (lengthOffset rem)) (s.reg 6#5 <<< (3 : Nat)) := by
  have linear : lengthSuffix.all Instruction.linear = true := by decide
  refine ⟨ImageExecution.linear_run base s _ 0x82 pc (by decide) lengthSuffix_decoded linear, ?_, ?_⟩
  · rw [linear_end_pc _ _ linear, pc, BitVec.add_assoc]; rfl
  · simp (config := { decide := true }) [run, lengthSuffix, storeDigit, Instruction.step,
      Width.store, writeLength, List.range_succ, word_end s rem count, BitVec.add_assoc,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
    simp only [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64),
      BitVec.setWidth_shiftLeft_of_le (by decide : 8 ≤ 64)]

end Crypto.RISCV64
