import Proofs.ARM64.Execution
import Proofs.ARM64.Decode
import Proofs.ARM64.ImportedMemory

/-!
Memory-fetch glue for the imported program. The loaded-code fetch proof follows
ProofLib/Invariant.lean at the pinned Google DeepMind revision (Apache-2.0),
using kernel-checked address algebra and four byte permissions here. No upstream
ISA source is changed. ImportedWholeCallFetch composes these fetch rules for the full call.
-/
namespace Crypto.ARM64.Imported

theorem codeLoaded_iff {prog : Arm64.Program} {m : Arm64.Memory} :
    prog.CodeLoaded m ↔
      prog.base.toNat % 4 = 0 ∧ prog.base.toNat + prog.code.length ≤ 2 ^ 64 ∧
      ∀ (i : Nat) (hi : i < prog.code.length),
        m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
        m.perm (prog.base + BitVec.ofNat 64 i) = some Arm64.Perm.rx ∧
        m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false := by
  unfold Arm64.Program.CodeLoaded
  rfl

theorem loaded_fetch_of_fetch {prog : Arm64.Program} {m : Arm64.Memory}
    {pc : BitVec 64} {instruction : Arm64.Instr}
    (loaded : prog.CodeLoaded m) (fetched : prog.fetch pc = some instruction) :
    prog.fetchMem m pc = some instruction := by
  obtain ⟨hbase, hlen, hcode⟩ := codeLoaded_iff.mp loaded
  unfold Arm64.Program.fetch at fetched
  unfold Arm64.Program.fetchMem
  split at fetched
  · contradiction
  rename_i hext
  simp only [hext]
  generalize hoff : (pc - prog.base).toNat = off at fetched
  have hpc : pc = prog.base + BitVec.ofNat 64 off := by
    rw [← hoff]
    exact (address_reconstruct prog.base pc).symm
  unfold Arm64.Program.readWordOff at fetched
  split at fetched
  · contradiction
  rename_i hal
  split at fetched
  rotate_left
  · contradiction
  rename_i b0 b1 b2 b3 tl hdrop
  have hlen4 : off + 4 ≤ prog.code.length := by
    have := congrArg List.length hdrop
    simp at this
    omega
  have hb : ∀ k (hk : k < 4), m.read8 (pc + BitVec.ofNat 64 k) = prog.code[off + k] ∧
      m.perm (pc + BitVec.ofNat 64 k) = some Arm64.Perm.rx ∧
      m.isLazyFree (pc + BitVec.ofNat 64 k) = false := by
    intro k hk
    have e : pc + BitVec.ofNat 64 k = prog.base + BitVec.ofNat 64 (off + k) := by
      rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
    rw [e]
    exact hcode _ (by omega)
  have hget : ∀ k (hk : k < 4), prog.code[off + k] =
      (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
    intro k hk
    simp only [← hdrop, List.getElem_drop]
  have hpcn : pc.toNat = prog.base.toNat + off := by
    rw [hpc, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hal' : ¬pc.toNat % 4 ≠ 0 := by omega
  simp only [hal', ↓reduceIte]
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have hx : m.canExec pc 4 = true := by
    have x0 := h0.2.1
    have x1 := h1.2.1
    have x2 := h2.2.1
    have x3 := h3.2.1
    simp only [BitVec.add_zero] at x0
    simp [Arm64.Memory.canExec, Arm64.Memory.allPerm, BitVec.add_assoc,
      x0, x1, x2, x3, Arm64.Perm.rx]
  rw [hx]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hr : m.read32 pc = b3 ++ b2 ++ b1 ++ b0 := by
    have g0 := hget 0 (by decide)
    have g1 := hget 1 (by decide)
    have g2 := hget 2 (by decide)
    have g3 := hget 3 (by decide)
    simp only [Arm64.Memory.read32]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
    rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0.1, g0,
      show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1.1, g1,
      show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2.1, g2,
      show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3.1, g3]
  rw [hr]
  exact fetched

theorem evalInst_permitted (base : BitVec 64) (instruction : Arm64.Instr)
    (allowed : permittedInstruction instruction = true) (s : Arm64.State) :
    (program base).evalInst instruction s = Arm64.execInstWithSvc Arm64.noSyscalls instruction s := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at allowed <;> rfl

theorem recorded_step {base : BitVec 64} {s : Arm64.State} {instruction : Arm64.Instr}
    (loaded : (program base).CodeLoaded s.mem)
    (fetched : (program base).fetch s.pc = some instruction)
    (running : s.status = .Running) (allowed : permittedInstruction instruction = true) :
    Arm64.Step (program base) s (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
  rw [← evalInst_permitted base instruction allowed s]
  exact Arm64.Step.exec running (loaded_fetch_of_fetch loaded fetched)

end Crypto.ARM64.Imported
