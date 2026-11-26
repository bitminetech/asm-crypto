import Proofs.RISCV64.HashPhases
import Proofs.RISCV64.Digest
import Proofs.RISCV64.Return

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (memoryBytes32 paddingBlockCount paddedSpecBlock)

/-- From initialized message and padding layouts, the linked routine
hashes both phases, emits the exact digest and executes the return. -/
theorem hash_to_return (base : Addr) (s : CPU) (data : ByteArray)
    (size : data.size < 2^61) (pc : s.pc = base + 0xf2) (messagePhase : s.reg 14 = 0)
    (messageCount : s.reg 13 = BitVec.ofNat 64 (data.size / 64))
    (paddingCount : s.reg 16 = BitVec.ofNat 64 (paddingBlockCount data))
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ j, j < image.size → 288 ≤ (base + BitVec.ofNat 64 j - s.reg 2).toNat)
    (inputApart : PhaseInputApart s (data.size / 64))
    (outputApart : ∀ i : Fin 8, ∀ d : Fin 4,
      32 ≤ (s.reg 2 + BitVec.ofNat 64 (256+4*i.val) + BitVec.ofNat 64 d.val - s.reg 11).toNat)
    (initial : storedHash s = Crypto.Reference.WordModel.H0_256)
    (messageWords : ∀ i : Fin (data.size / 64),
      blockWords s.mem (s.reg 12 + BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data i.val)
    (paddingWords : ∀ i : Fin (paddingBlockCount data),
      blockWords s.mem (s.reg 2 + 288 + BitVec.ofNat 64 (64*i.val)) =
        paddedSpecBlock data (data.size / 64 + i.val)) :
    ∃ msgMid msgExit switch padInit padMid padExit finished written out,
      BlockPathPrefix base s (data.size / 64) msgMid ∧
      ImageExecution base msgMid [blockGuard] msgExit ∧
      ImageExecution base msgExit [phaseGuard] switch ∧
      ImageExecution base switch paddingPhase padInit ∧
      BlockPathPrefix base padInit (paddingBlockCount data) padMid ∧
      ImageExecution base padMid [blockGuard] padExit ∧
      ImageExecution base padExit [phaseGuard] finished ∧
      ImageExecution base finished digestCode written ∧
      ImageExecution base written returnCode out ∧
      out.pc = s.reg 1 &&& ~~~(1 : Addr) ∧ out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 + 480 ∧
      memoryBytes32 out.mem (s.reg 11) = (Crypto.Reference.digest data).map UInt8.toBitVec ∧
      savedRegisters out = savedStack written ∧ written.reg 2 = s.reg 2 ∧ written.mem = out.mem ∧
      (∀ p, 288 ≤ (p - s.reg 2).toNat → 32 ≤ (p - s.reg 11).toNat →
        out.mem.cells p = s.mem.cells p) := by
  obtain ⟨msg, msgExit, switch, pad, padMid, padExit, finished, message, branchOut, dispatch,
    switched, padding, padBranch, epilogue, position, stack, dst, ra, result, phaseFrame⟩ :=
      hash_phases base s data size pc messagePhase messageCount paddingCount loaded constants
        codeApart inputApart initial messageWords paddingWords
  obtain ⟨written, output, returnPC, outputStack, _, bytes, writeFrame⟩ :=
    digest_written base finished position (fun i d => by rw [stack, dst]; exact outputApart i d)
  obtain ⟨returned, exit, status, finalStack, ram, saved⟩ := return_loaded base written returnPC
  have savedRA : written.reg 1 = finished.reg 1 := by
    apply output.register_unchanged
    intro i hi
    have check : digestCode.all (fun j => !(j.op.destination == some 1)) = true := by decide +kernel
    simpa using List.all_eq_true.mp check i hi
  refine ⟨msg, msgExit, switch, pad, padMid, padExit, finished, written, _, message, branchOut,
    dispatch, switched, padding, padBranch, epilogue, output, returned, ?_, status, ?_, ?_, saved, outputStack.trans stack, ram.symm, ?_⟩
  · rw [exit, savedRA, ra]
  · rw [finalStack, outputStack, stack]
  · rw [ram, ← dst, bytes, result]
  · intro p sp output
    rw [ram]
    exact (writeFrame p (by rw [dst]; exact output)).trans (phaseFrame p sp)

end Crypto.RISCV64
