import Proofs.ARM64.ImportedZeroPad
import Proofs.ARM64.ImportedPaddingSetup
import Proofs.ARM64.ImportedTailLoops

/-!
The complete zero/setup/tail-copy prefix initializes all 128 padding bytes to
exactly the message tail followed by zeros, independently of old stack bytes.
Register values, PC, non-memory state, outside cells and read/write permissions
are retained for composition with the marker/length suffix. Fetch binding,
reference padding equivalence and whole-function equal remain separate.
-/
namespace Crypto.ARM64.Imported

theorem zeroRegisters_read {a b : Arm64.State} (h : zeroRegisters b = zeroRegisters a)
    (i : BitVec 5) (hi : i ≠ 16#5) : b.readReg64 (.gpr i) = a.readReg64 (.gpr i) := by
  have result := congrFun h i
  simpa only [zeroRegisters, if_neg hi] using result

def tailPointer (s : Arm64.State) : BitVec 64 :=
  s.readReg64 .x2 + ((s.readReg64 .x15 >>> 6) <<< 6)

def prepareTailCode (rem : Nat) := zeroPadCode ++ (paddingSetupCode ++ tailCopyCode rem)

theorem prepare_tail (s : Arm64.State)
    (hw : ∀ i : Fin 16, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (hb : ∀ i : Fin 128, s.mem.canWrite ((s.sp + 288#64) + BitVec.ofNat 64 i.val) 1 = true)
    (hr : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      s.mem.canRead (tailPointer s + BitVec.ofNat 64 i.val) 1 = true)
    (sep : ∀ i : Fin ((s.readReg64 .x15).toNat % 64),
      128 ≤ (tailPointer s + BitVec.ofNat 64 i.val - (s.sp + 288#64)).toNat) :
    ∃ out, runWords (prepareTailCode ((s.readReg64 .x15).toNat % 64)) s = some out ∧
      nonMemory out = nonMemory s ∧ nonvolatile out = nonvolatile s ∧
      out.pc = s.pc + 76#64 ∧
      out.readReg64 .x0 = s.readReg64 .x0 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      out.readReg64 .x2 = s.readReg64 .x2 ∧
      out.readReg64 .x3 = s.readReg64 .x15 >>> 6 ∧
      out.readReg64 .x6 = BitVec.ofNat 64 ((s.readReg64 .x15).toNat % 64) ∧
      out.readReg64 .x15 = s.readReg64 .x15 ∧ out.readReg64 .x16 = s.sp + 288#64 ∧
      out.readReg64 .x17 = BitVec.ofNat 64 ((s.readReg64 .x15).toNat % 64) ∧
      (∀ i : Fin 128, out.mem.read8 ((s.sp + 288#64) + BitVec.ofNat 64 i.val) =
        if i.val < (s.readReg64 .x15).toNat % 64 then
          s.mem.read8 (tailPointer s + BitVec.ofNat 64 i.val) else 0#8) ∧
      (∀ p, 128 ≤ (p - (s.sp + 288#64)).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  let rem := (s.readReg64 .x15).toNat % 64
  have hrem : rem < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨zeroed, hz, postZero⟩ := exists_of_map_some _ _ _ (zero_padding s hw)
  simp only [Prod.mk.injEq] at postZero
  obtain ⟨zstable, zregs, zmem, zpc, znv, z16⟩ := postZero
  have z0 := zeroRegisters_read zregs 0#5 (by decide)
  have z1 := zeroRegisters_read zregs 1#5 (by decide)
  have z2 := zeroRegisters_read zregs 2#5 (by decide)
  have z15 := zeroRegisters_read zregs 15#5 (by decide)
  have zshift := congrArg (fun x : BitVec 64 => x >>> 6) z15
  obtain ⟨setup, hp, postSetup⟩ := exists_of_map_some _ _ _ (padding_setup zeroed)
  simp only [Prod.mk.injEq] at postSetup
  obtain ⟨pstable, ppc, pnv, p0, p1, p2, p3, p5, p6, p15, p16, p17⟩ := postSetup
  have pmem := congrArg Arm64.State.mem pstable
  change setup.mem = zeroed.mem at pmem
  have source : setup.readReg64 .x5 = tailPointer s := by rw [p5, z2, z15]; rfl
  have target : setup.readReg64 .x16 = s.sp + 288#64 := p16.trans z16
  have remainder : setup.readReg64 .x17 = BitVec.ofNat 64 rem := by
    rw [p17, z15]
    apply BitVec.toNat_inj.mp
    rw [remainder_mask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64)]
  have reads (i : Fin rem) : setup.mem.canRead (setup.readReg64 .x5 + BitVec.ofNat 64 i.val) 1 = true := by
    rw [pmem, zmem, source]
    exact zeroPadMemory_readable s _ _ (hr i)
  have writes (i : Fin 128) : setup.mem.canWrite (setup.readReg64 .x16 + BitVec.ofNat 64 i.val) 1 = true := by
    rw [pmem, zmem, target, zeroPadMemory_writable]
    exact hb i
  have outside (i : Fin rem) :
      128 ≤ (setup.readReg64 .x5 + BitVec.ofNat 64 i.val - setup.readReg64 .x16).toNat := by
    rw [source, target]; exact sep i
  obtain ⟨out, hc, cm, cregs, cnv, cpc, c6, copied, _, _, _, frame, readable, writable⟩ :=
    tail_copy_loop setup rem hrem p6 remainder reads writes outside
  have znm := congrArg nonMemory zstable
  have pnm := congrArg nonMemory pstable
  have nonmem : nonMemory out = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem] using cm.trans (pnm.trans znm)
  have tail := runWords_append_success hp hc
  have whole := runWords_append_success hz tail
  refine ⟨out, whole, nonmem, cnv.trans (pnv.trans znv), ?_, ?_, ?_, ?_, ?_, c6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cpc, ppc, zpc]
    simp only [BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)
  · exact (copyRegisters_read cregs 0#5 (by decide)).trans (p0.trans z0)
  · exact (copyRegisters_read cregs 1#5 (by decide)).trans (p1.trans z1)
  · exact (copyRegisters_read cregs 2#5 (by decide)).trans (p2.trans z2)
  · exact (copyRegisters_read cregs 3#5 (by decide)).trans (p3.trans zshift)
  · exact (copyRegisters_read cregs 15#5 (by decide)).trans (p15.trans z15)
  · exact (copyRegisters_read cregs 16#5 (by decide)).trans target
  · exact (copyRegisters_read cregs 17#5 (by decide)).trans remainder
  · intro i
    by_cases hi : i.val < rem
    · rw [if_pos hi]
      have cp := copied i.val hi
      rw [target, source, pmem, zmem] at cp
      have cell := zeroPadMemory_outside s (tailPointer s + BitVec.ofNat 64 i.val) (sep ⟨i.val, hi⟩)
      have byte := congrArg (fun c => match c with | some (_, b) => b | none => 0#8) cell
      exact cp.trans byte
    · rw [if_neg hi]
      have small : i.val < 2 ^ 64 := by have := i.isLt; omega
      have dist : rem ≤ ((s.sp + 288#64) + BitVec.ofNat 64 i.val - setup.readReg64 .x16).toNat := by
        rw [target, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        omega
      have cell := frame _ dist
      have byte := congrArg (fun c => match c with | some (_, b) => b | none => 0#8) cell
      change out.mem.read8 _ = setup.mem.read8 _ at byte
      rw [pmem, zmem] at byte
      exact byte.trans (zeroPadMemory_byte s i)
  · intro p hp
    have dist : rem ≤ (p - setup.readReg64 .x16).toNat := by rw [target]; omega
    have keep := frame p dist
    rw [pmem, zmem] at keep
    exact keep.trans (zeroPadMemory_outside s p hp)
  · intro a n read
    exact readable a n (by rw [pmem, zmem]; exact zeroPadMemory_readable s a n read)
  · intro a n
    rw [writable, pmem, zmem, zeroPadMemory_writable]

end Crypto.ARM64.Imported
