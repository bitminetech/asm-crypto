import Proofs.RISCV64.Iteration

namespace Crypto.RISCV64

/-- Seven execution segments of one block, each following the linked bytes.
Keeping segment boundaries explicit permits composition without evaluating
the several thousand instructions of a block in the kernel. -/
def BlockPath (base : Addr) (s out : CPU) : Prop :=
  ∃ entered afterLoad afterExpansion startRounds endRounds compressed,
    ImageExecution base s [blockGuard, startWords] entered ∧
    ImageExecution base entered (loadCode 16) afterLoad ∧
    ImageExecution base afterLoad (expansionCode 48) afterExpansion ∧
    ImageExecution base afterExpansion loadHashBody startRounds ∧
    ImageExecution base startRounds (roundCode 64) endRounds ∧
    ImageExecution base endRounds feedForward compressed ∧
    ImageExecution base compressed advanceBlock out

inductive BlockPathPrefix (base : Addr) : CPU → Nat → CPU → Prop where
  | nil (s : CPU) : BlockPathPrefix base s 0 s
  | step {s mid out : CPU} {n : Nat}
      (before : BlockPathPrefix base s n mid) (next : BlockPath base mid out) :
      BlockPathPrefix base s (n + 1) out

def phaseHash (s : CPU) (n : Nat) : Vector Word 8 :=
  Fin.foldl n (fun h i => SHS.SHA256.compress h
    (blockWords s.mem (s.reg 12 + BitVec.ofNat 64 (64*i.val)))) (storedHash s)

def PhaseInputApart (s : CPU) (n : Nat) : Prop :=
  ∀ b : Fin n, ∀ w : Fin 16, ∀ d : Fin 4,
    288 ≤ (s.reg 12 + BitVec.ofNat 64 (64*b.val) + BitVec.ofNat 64 (4*w.val) +
      BitVec.ofNat 64 d.val - s.reg 2).toNat

structure PhaseState (base : Addr) (s out : CPU) (total done : Nat) : Prop where
  pc : out.pc = base + 0xf2
  count : out.reg 13 = BitVec.ofNat 64 (total - done)
  input : out.reg 12 = s.reg 12 + BitVec.ofNat 64 (64*done)
  stack : out.reg 2 = s.reg 2
  constants : out.reg 10 = s.reg 10
  output : out.reg 11 = s.reg 11
  phase : out.reg 14 = s.reg 14
  paddingCount : out.reg 16 = s.reg 16
  returnAddress : out.reg 1 = s.reg 1
  hash : storedHash out = phaseHash s done
  cells : ∀ p, 288 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p

attribute [local irreducible] SHS.SHA256.compress

private theorem phase_input (s t : CPU) (total done : Nat) (small : done < total)
    (apart : PhaseInputApart s total) (ptr : t.reg 12 = s.reg 12 + BitVec.ofNat 64 (64*done))
    (frame : ∀ p, 288 ≤ (p - s.reg 2).toNat → t.mem.cells p = s.mem.cells p) :
    blockWords t.mem (t.reg 12) = blockWords s.mem (s.reg 12 + BitVec.ofNat 64 (64*done)) := by
  rw [ptr]
  apply Vector.ext
  intro i hi
  simp only [blockWords, Vector.getElem_ofFn]
  exact byteWord_eq_of_cells _ (fun d => frame _ (apart ⟨done,small⟩ ⟨i,hi⟩ d))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem phase_prefix (base : Addr) (s : CPU) (total done : Nat)
    (safe : total < 2^64) (bound : done ≤ total)
    (pc : s.pc = base + 0xf2) (left : s.reg 13 = BitVec.ofNat 64 total)
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ j, j < image.size → 288 ≤ (base + BitVec.ofNat 64 j - s.reg 2).toNat)
    (apart : PhaseInputApart s total) :
    ∃ out, BlockPathPrefix base s done out ∧ PhaseState base s out total done := by
  induction done with
  | zero =>
    refine ⟨s, .nil _, ⟨pc, left, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩⟩
    · simp
    · simp [phaseHash]
  | succ n ih =>
    have small : n < total := by omega
    obtain ⟨mid, prefixPath, h⟩ := ih (by omega)
    have nonzero : mid.reg 13#5 ≠ 0 := by
      change mid.reg 13 ≠ (0 : Addr)
      rw [h.count]
      intro eq
      have := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      change total - n = 0 at this
      omega
    have nextLoaded (j : Nat) (hj : j < image.size) :
        mid.mem.read8 (base + BitVec.ofNat 64 j) = image[j]!.toBitVec := by
      unfold Arm64.Memory.read8
      rw [h.cells _ (codeApart j hj)]
      exact loaded j hj
    obtain ⟨entered, a, b, c, d, compressed, out, enter, load, expand, loadH, rounds, feed, advance,
        back, ptr, count, sp, k, output, phase, pad, ret, hash, frame⟩ :=
      block_iteration base mid h.pc nonzero nextLoaded (h.constants.trans constants)
        (fun j hj => by rw [h.stack]; exact codeApart j hj)
        (fun i j => by rw [h.input, h.stack]; exact apart ⟨n,small⟩ i j)
    refine ⟨out, .step prefixPath ⟨entered, a, b, c, d, compressed, enter,
      load, expand, loadH, rounds, feed, advance⟩,
      ⟨back, ?_, ?_, sp.trans h.stack, k.trans h.constants, output.trans h.output,
        phase.trans h.phase, pad.trans h.paddingCount, ret.trans h.returnAddress, ?_, ?_⟩⟩
    · rw [count, h.count]
      have pos : total - n = total - (n+1) + 1 := by omega
      rw [pos, BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ (1#64)
    · rw [ptr, h.input, BitVec.add_assoc]
      have next : 64*(n+1) = 64*n + 64 := by omega
      rw [next, BitVec.ofNat_add]
      rfl
    · rw [hash, h.hash, phase_input s mid total n small apart h.input h.cells]
      simp only [phaseHash, Fin.foldl_succ_last, Fin.val_last, Fin.val_castSucc]
    · intro p hp
      exact (frame p (by rw [h.stack]; exact hp)).trans (h.cells p hp)

/-- Hash every block of a message or padding phase and take the verified
zero-counter edge to the phase dispatch. -/
theorem block_phase (base : Addr) (s : CPU) (n : Nat)
    (safe : n < 2^64) (pc : s.pc = base + 0xf2) (left : s.reg 13 = BitVec.ofNat 64 n)
    (loaded : ImageLoaded base s.mem)
    (constants : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (codeApart : ∀ j, j < image.size → 288 ≤ (base + BitVec.ofNat 64 j - s.reg 2).toNat)
    (apart : PhaseInputApart s n) :
    ∃ mid out, BlockPathPrefix base s n mid ∧ PhaseState base s mid n n ∧
      ImageExecution base mid [blockGuard] out ∧ out.pc = base + 0x2f6 ∧
      out.mem = mid.mem ∧ out.regs = mid.regs := by
  obtain ⟨mid, prefixPath, h⟩ := phase_prefix base s n n safe (by omega) pc left loaded constants codeApart apart
  obtain ⟨exit, position, ram, regs⟩ := block_guard base mid h.pc
  have zero : mid.reg 13#5 = 0 := by
    change mid.reg 13 = (0 : Addr)
    rw [h.count, Nat.sub_self]
    rfl
  exact ⟨mid, _, prefixPath, h, exit, by simpa only [if_pos zero] using position, ram, regs⟩

end Crypto.RISCV64
