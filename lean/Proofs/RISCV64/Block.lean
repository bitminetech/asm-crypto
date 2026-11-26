import Proofs.RISCV64.InputWords
import Proofs.RISCV64.Compression
import Proofs.RISCV64.RegisterFrame
import Proofs.ARM64.ImportedCellFrame

namespace Crypto.RISCV64

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

open Crypto.ARM64.Imported (wordVector)

private theorem load_preserves_constants (s : CPU) (n : Nat) :
    (run (loadCode n) s).reg 10 = s.reg 10 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loadCode, run_append, run_reg_unchanged (run (loadCode n) s) loadCycle 10]
    · exact ih
    · have check : loadCycle.all (fun i => !(i.op.destination == some 10)) = true := by decide
      intro i hi
      simpa using List.all_eq_true.mp check i hi

private theorem expansion_preserves_constants (s : CPU) (n : Nat) :
    (run (expansionCode n) s).reg 10 = s.reg 10 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [expansionCode, run_append, run_reg_unchanged (run (expansionCode n) s) expansionCycle 10]
    · exact ih
    · have check : expansionCycle.all (fun i => !(i.op.destination == some 10)) = true := by decide
      intro i hi
      simpa using List.all_eq_true.mp check i hi

private theorem hash_frame (s t : CPU) (stack : t.reg 2 = s.reg 2)
    (frame : ∀ p, 256 ≤ (p - s.reg 2).toNat → t.mem.cells p = s.mem.cells p) :
    storedHash t = storedHash s := by
  unfold storedHash
  rw [stack]
  exact Crypto.ARM64.Imported.hash_snapshot_of_frame _ _ _ frame

private theorem image_frame (base : Addr) (s t : CPU) (loaded : ImageLoaded base s.mem)
    (apart : ∀ i, i < image.size → 256 ≤ (base + BitVec.ofNat 64 i - s.reg 2).toNat)
    (frame : ∀ p, 256 ≤ (p - s.reg 2).toNat → t.mem.cells p = s.mem.cells p) :
    ImageLoaded base t.mem := by
  intro i hi
  unfold Arm64.Memory.read8
  rw [frame _ (apart i hi)]
  exact loaded i hi

attribute [local irreducible] run loadCode expansionCode SHS.SHA256.compress SHS.SHA256.schedule

/-- One block of RV64 SHA-256 from the first input-word load to the end of
feed-forward. The message and initial chaining value are arbitrary. -/
theorem block_compression (base : Addr) (s : CPU)
    (pc : s.pc = base + 0xf8) (index : s.reg 15 = 0)
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ i, i < image.size → 256 ≤ (base + BitVec.ofNat 64 i - s.reg 2).toNat)
    (inputApart : ∀ i : Fin 16, ∀ d : Fin 4,
      256 ≤ (s.reg 12 + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 d.val - s.reg 2).toNat) :
    ∃ afterLoad afterExpansion startRounds endRounds out,
      ImageExecution base s (loadCode 16) afterLoad ∧
      ImageExecution base afterLoad (expansionCode 48) afterExpansion ∧
      ImageExecution base afterExpansion loadHashBody startRounds ∧
      ImageExecution base startRounds (roundCode 64) endRounds ∧
      ImageExecution base endRounds feedForward out ∧ out.pc = base + 0x2ee ∧
      storedHash out = SHS.SHA256.compress (storedHash s) (blockWords s.mem (s.reg 12)) ∧
      out.reg 2 = s.reg 2 ∧
      (∀ p, 288 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  let words := blockWords s.mem (s.reg 12)
  let first := run (loadCode 16) s
  obtain ⟨input, loadPC, next, loadSP, _, firstWords, firstFrame⟩ :=
    load_words base s pc index inputApart
  let second := run (expansionCode 48) first
  obtain ⟨expansion, expPC, expSP, schedule, expFrame⟩ :=
    expansion_loaded base first words loadPC next firstWords
  have frame (p : Addr) (h : 256 ≤ (p - s.reg 2).toNat) : second.mem.cells p = s.mem.cells p :=
    (expFrame p (by rw [show first.reg 2 = s.reg 2 from loadSP]; exact h)).trans (firstFrame p h)
  have k : second.reg 10 = s.reg 10 :=
    (expansion_preserves_constants first 48).trans (load_preserves_constants s 16)
  obtain ⟨start, finish, out, loadHash, rounds, feed, exit, value, stack, preserve⟩ :=
    compression_loaded base second words expPC (image_frame base s second loaded codeApart frame)
      (k.trans constants) schedule
  have old : storedHash second = storedHash s := hash_frame s second (expSP.trans loadSP) frame
  refine ⟨first, second, start, finish, out, input, expansion, loadHash, rounds, feed, exit,
    value.trans (congrArg (SHS.SHA256.compress · words) old), stack.trans (expSP.trans loadSP), ?_⟩
  intro p outside
  have sameSP : second.reg 2 = s.reg 2 := expSP.trans loadSP
  exact (preserve p (by rw [sameSP]; exact outside)).trans (frame p (by omega))

end Crypto.RISCV64
