import Proofs.RISCV64.PhaseReference
import Proofs.RISCV64.RegisterFrame

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (digestBytes paddingBlockCount paddedSpecBlock paddedSpecFold
  reference_digest_bytes address_delta)
open SHS.Equiv.SHA256.Padding.Layout (implPaddedBytes)

private theorem reg_eq_of_regs {s t : CPU} (h : s.regs = t.regs) (r : Reg) :
    s.reg r = t.reg r := by
  unfold CPU.reg
  rw [h]

private theorem hash_same {s t : CPU} (mem : s.mem = t.mem) (sp : s.reg 2 = t.reg 2) :
    storedHash s = storedHash t := congrArg₂ (fun m p => Crypto.ARM64.Imported.wordVector 8 m (p + 256)) mem sp

private theorem pad_address (s : CPU) (data : ByteArray)
    (b : Fin (paddingBlockCount data)) (w : Fin 16) (d : Fin 4) :
    288 ≤ (s.reg 2 + 288 + BitVec.ofNat 64 (64*b.val) + BitVec.ofNat 64 (4*w.val) +
      BitVec.ofNat 64 d.val - s.reg 2).toNat := by
  have blocks : paddingBlockCount data ≤ 2 := by unfold paddingBlockCount; split <;> omega
  have hb := b.isLt
  have hw := w.isLt
  have hd := d.isLt
  have small : 288 + 64*b.val + 4*w.val + d.val < 2^64 := by omega
  have eq : s.reg 2 + 288 + BitVec.ofNat 64 (64*b.val) + BitVec.ofNat 64 (4*w.val) +
      BitVec.ofNat 64 d.val = s.reg 2 + BitVec.ofNat 64 (288 + 64*b.val + 4*w.val + d.val) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  rw [eq, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

private theorem switchKeeps (s : CPU) (r : Reg) (hr : r ≠ 12) (hc : r ≠ 13) (hp : r ≠ 14) :
    (run paddingPhase s).reg r = s.reg r := by
  apply run_reg_unchanged
  intro i hi
  simp only [paddingPhase, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact fun h => hp (Option.some.inj h.symm)
  · exact fun h => hr (Option.some.inj h.symm)
  · exact fun h => hc (Option.some.inj h.symm)
  · simp [Op.destination]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
/-- Execute the message phase, switch to the stack padding, and execute the
padding phase. The required layouts identify the input bytes before hashing. -/
theorem hash_phases (base : Addr) (s : CPU) (data : ByteArray)
    (size : data.size < 2^61) (pc : s.pc = base + 0xf2) (messagePhase : s.reg 14 = 0)
    (messageCount : s.reg 13 = BitVec.ofNat 64 (data.size / 64))
    (paddingCount : s.reg 16 = BitVec.ofNat 64 (paddingBlockCount data))
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ j, j < image.size → 288 ≤ (base + BitVec.ofNat 64 j - s.reg 2).toNat)
    (inputApart : PhaseInputApart s (data.size / 64))
    (initial : storedHash s = SHS.SHA256.H0_256)
    (messageWords : ∀ i : Fin (data.size / 64),
      blockWords s.mem (s.reg 12 + BitVec.ofNat 64 (64*i.val)) = paddedSpecBlock data i.val)
    (paddingWords : ∀ i : Fin (paddingBlockCount data),
      blockWords s.mem (s.reg 2 + 288 + BitVec.ofNat 64 (64*i.val)) =
        paddedSpecBlock data (data.size / 64 + i.val)) :
    ∃ msgMid msgExit switch padInit padMid padExit out,
      BlockPathPrefix base s (data.size / 64) msgMid ∧
      ImageExecution base msgMid [blockGuard] msgExit ∧
      ImageExecution base msgExit [phaseGuard] switch ∧
      ImageExecution base switch paddingPhase padInit ∧
      BlockPathPrefix base padInit (paddingBlockCount data) padMid ∧
      ImageExecution base padMid [blockGuard] padExit ∧
      ImageExecution base padExit [phaseGuard] out ∧ out.pc = base + 0x300 ∧
      out.reg 2 = s.reg 2 ∧ out.reg 11 = s.reg 11 ∧ out.reg 1 = s.reg 1 ∧
      digestBytes (storedHash out) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec ∧
      (∀ p, 288 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨msg, msgExit, message, h, branchOut, atDispatch, preMem, preRegs⟩ :=
    block_phase base s _ (by omega) pc messageCount loaded constants codeApart inputApart
  obtain ⟨dispatch, switchPC, dispatchMem, dispatchRegs⟩ := phase_guard base msgExit atDispatch
  let switch := phaseGuard.step msgExit
  have phase0 : msgExit.reg 14#5 = 0 := (reg_eq_of_regs preRegs 14).trans (h.phase.trans messagePhase)
  have enters : switch.pc = base + 0x2f8 := by simpa only [if_pos phase0] using switchPC
  obtain ⟨switched, padPC, newMem, ptr, remaining, positive⟩ := switch_to_padding base switch enters
  let pad := run paddingPhase switch
  have oldRegs : switch.regs = msg.regs := dispatchRegs.trans preRegs
  have oldMemory : switch.mem = msg.mem := dispatchMem.trans preMem
  have oldSP : switch.reg 2 = s.reg 2 := (reg_eq_of_regs oldRegs 2).trans h.stack
  have stack : pad.reg 2 = s.reg 2 :=
    (switchKeeps switch 2 (by decide) (by decide) (by decide)).trans oldSP
  have start : pad.reg 12 = s.reg 2 + 288 := ptr.trans (congrArg (· + 288) oldSP)
  have entire : pad.mem = msg.mem := newMem.trans oldMemory
  have remain : pad.reg 13 = BitVec.ofNat 64 (paddingBlockCount data) :=
    remaining.trans ((reg_eq_of_regs oldRegs 16).trans (h.paddingCount.trans paddingCount))
  have k : pad.reg 10 = base + BitVec.ofNat 64 constantsOffset :=
    (switchKeeps switch 10 (by decide) (by decide) (by decide)).trans
      ((reg_eq_of_regs oldRegs 10).trans (h.constants.trans constants))
  have frame (p : Addr) (outside : 288 ≤ (p-s.reg 2).toNat) : pad.mem.cells p = s.mem.cells p := by
    rw [entire, h.cells p outside]
  have padLoaded : ImageLoaded base pad.mem := by
    intro j hj
    unfold Arm64.Memory.read8
    rw [frame _ (codeApart j hj)]
    exact loaded j hj
  have within : PhaseInputApart pad (paddingBlockCount data) := by
    intro b w i
    rw [start, stack]
    exact pad_address s data b w i
  have countBound : paddingBlockCount data < 2^64 := by unfold paddingBlockCount; split <;> decide
  obtain ⟨padMid, padExit, padding, facts, padBranch, dispatchPC, padMem, padRegs⟩ :=
    block_phase base pad _ countBound padPC remain padLoaded k
      (fun j hj => by rw [stack]; exact codeApart j hj) within
  obtain ⟨epilogue, digestPC, outMem, outRegs⟩ := phase_guard base padExit dispatchPC
  let out := phaseGuard.step padExit
  have phase1 : padExit.reg 14#5 ≠ 0 := by
    have phase1 : padExit.reg 14#5 = 1 := (reg_eq_of_regs padRegs 14).trans (facts.phase.trans positive)
    rw [phase1]
    decide
  have newHash : storedHash pad = phaseHash s (data.size / 64) :=
    (hash_same entire (stack.trans h.stack.symm)).trans h.hash
  have finalHash : storedHash out = phaseHash pad (paddingBlockCount data) :=
    (hash_same (outMem.trans padMem) (reg_eq_of_regs (outRegs.trans padRegs) 2)).trans facts.hash
  have padWords (b : Fin (paddingBlockCount data)) :
      blockWords pad.mem (pad.reg 12 + BitVec.ofNat 64 (64*b.val)) =
        paddedSpecBlock data (data.size / 64 + b.val) := by
    rw [start, ← paddingWords]
    apply Vector.ext
    intro w hw
    simp only [blockWords, Vector.getElem_ofFn]
    exact byteWord_eq_of_cells _ (fun i => frame _ (pad_address s data b ⟨w,hw⟩ i))
  have finalRegs : out.regs = padMid.regs := outRegs.trans padRegs
  have dst : pad.reg 11 = s.reg 11 :=
    (switchKeeps switch 11 (by decide) (by decide) (by decide)).trans
      ((reg_eq_of_regs oldRegs 11).trans h.output)
  have ra : pad.reg 1 = s.reg 1 :=
    (switchKeeps switch 1 (by decide) (by decide) (by decide)).trans
      ((reg_eq_of_regs oldRegs 1).trans h.returnAddress)
  refine ⟨msg, msgExit, switch, pad, padMid, padExit, out, message, branchOut, dispatch,
    switched, padding, padBranch, epilogue, by simpa only [if_neg phase1] using digestPC,
    (reg_eq_of_regs finalRegs 2).trans (facts.stack.trans stack),
    (reg_eq_of_regs finalRegs 11).trans (facts.output.trans dst),
    (reg_eq_of_regs finalRegs 1).trans (facts.returnAddress.trans ra), ?_, ?_⟩
  · rw [finalHash, phase_hash_reference s pad data initial newHash messageWords padWords]
    exact (reference_digest_bytes data size).symm
  · intro p hp
    have finalMem : out.mem = padMid.mem := outMem.trans padMem
    rw [finalMem]
    exact (facts.cells p (by rw [stack]; exact hp)).trans (frame p hp)

end Crypto.RISCV64
