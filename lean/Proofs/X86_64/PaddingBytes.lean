import Proofs.X86_64.PaddingSuffix
import Proofs.X86_64.PhaseSwitch
import Proofs.ARM64.ImportedPaddingReference

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (lengthOffset)

private theorem bswap64 (v : Val) : Value.bswap .q v = Arm64.rev64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Value.bswap, Value.byteRev, Value.trunc_q, Size.bytes, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Arm64.rev64]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_or,BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  all_goals
    simp only [← BitVec.getLsbD_eq_getElem]
    repeat' first | rw [BitVec.getLsbD_append] | rw [BitVec.getLsbD_extractLsb']
    simp (config := {decide := true})

theorem suffix_count (s : Cpu) (r : Nat) :
    (suffixMemory s r).readSize .q (s.regs.get .rsp+440) = BitVec.ofNat 64 (padBlocks r) := by
  unfold suffixMemory padBase
  by_cases h : r < 56
  · simp only [lengthOffset,if_pos h,BitVec.add_assoc]
    exact (stack_read_other _ _ 440#64 344#64 _ (by decide +kernel)).trans (read64_write64 _ _ _)
  · simp only [lengthOffset,if_neg h,BitVec.add_assoc]
    exact (stack_read_other _ _ 440#64 408#64 _ (by decide +kernel)).trans (read64_write64 _ _ _)

theorem suffix_frame (s : Cpu) (r : Nat) (small : r < 64) (p : Val)
    (outside : 128 ≤ (p-padBase s).toNat) (count : 8 ≤ (p-(s.regs.get .rsp+440)).toNat) :
    (suffixMemory s r).read p = s.mem.read p := by
  have len := Crypto.ARM64.Imported.lengthOffset_bounds r small
  have marker : p ≠ padBase s+BitVec.ofNat 64 r := by
    intro e
    rw [e,Crypto.ARM64.Imported.address_delta,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at outside
    omega
  rw [suffixMemory,counter_frame _ _ _ _ (Crypto.ARM64.Imported.region_store_delta _ _ _ 128 8 len.2 outside),
    counter_frame _ _ _ _ count,markedMemory,Mem.read_write_ne _ _ _ _ marker]

theorem suffix_byte (s : Cpu) (r : Nat) (small : r < 64) (i : Fin 128) :
    (suffixMemory s r).read (padBase s+BitVec.ofNat 64 i.val) =
      if lengthOffset r ≤ i.val ∧ i.val < lengthOffset r + 8 then
        (s.regs.get .rcx <<< 3).extractLsb' (8*(7-(i.val-lengthOffset r))) 8
      else if i.val = r then 128 else s.mem.read (padBase s+BitVec.ofNat 64 i.val) := by
  have len := Crypto.ARM64.Imported.lengthOffset_bounds r small
  by_cases inside : lengthOffset r ≤ i.val ∧ i.val < lengthOffset r+8
  · rw [if_pos inside]
    let k : Fin 8 := ⟨i.val-lengthOffset r,by omega⟩
    have addr : padBase s+BitVec.ofNat 64 i.val = (padBase s+BitVec.ofNat 64 (lengthOffset r))+BitVec.ofNat 64 k.val := by
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      exact congrArg _ (congrArg (BitVec.ofNat 64) (by dsimp [k]; omega))
    rw [suffixMemory,← byteView_read,byteView_write64,addr,Crypto.ARM64.Imported.write64_byte,bswap64]
    exact Crypto.ARM64.Imported.rev64_byte _ k
  · have unchanged : ∀ b : Fin 8, padBase s+BitVec.ofNat 64 i.val ≠
        (padBase s+BitVec.ofNat 64 (lengthOffset r))+BitVec.ofNat 64 b.val := by
      intro b eq
      rw [BitVec.add_assoc,← BitVec.ofNat_add] at eq
      have eq' := (Crypto.ARM64.Imported.byte128_address_inj (padBase s) i
        ⟨lengthOffset r+b.val,by have := b.isLt; omega⟩).mp eq
      change i.val = lengthOffset r+b.val at eq'
      have := b.isLt
      omega
    rw [if_neg inside,suffixMemory,← byteView_read,byteView_write64,Crypto.ARM64.Imported.read8_write64_outside_ne _ _ _ _ unchanged,
      byteView_read,counter_frame]
    · rw [markedMemory]
      by_cases e : i.val = r
      · rw [if_pos e,e,Mem.read_write_same]
      · rw [if_neg e,Mem.read_write_ne]
        exact fun eq => e ((Crypto.ARM64.Imported.byte128_address_inj _ i ⟨r,by omega⟩).mp eq)
    · unfold padBase
      rw [BitVec.add_assoc,stack_delta]
      have finite : ∀ j : Fin 128, 8 ≤ (288+BitVec.ofNat 64 j.val-440).toNat := by decide +kernel
      exact finite i

end Crypto.X86_64
