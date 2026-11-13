import Proofs.ARM64.ImportedBlock
import Proofs.ARM64.ImportedOuterControl

/-!
Composition of the recorded block gate, 3,095-word compression path and advance.
The loop invariant proves the FIPS compression fold for every number of blocks
below 2^64, retaining source/constants, permissions and the modeled state frame.
BlockReady contains only input memory/layout/register facts; it assumes no
execution result.
-/
namespace Crypto.ARM64.Imported

structure BlockReady (s : Arm64.State) : Prop where
  aligned : s.spAligned = true
  workspaceRead : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true
  workspaceWrite : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true
  hashRead : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true
  hashWrite : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true
  constantsRead : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true
  constantsValue : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!
  constantsOutside : ∀ (i : Fin 64) (b : Fin 4),
    288 ≤ (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat

theorem BlockReady.transport {s out : Arm64.State} (h : BlockReady s)
    (mem : out.mem = s.mem) (sp : out.sp = s.sp)
    (x0 : out.readReg64 .x0 = s.readReg64 .x0) : BlockReady out := by
  constructor
  · simpa only [Arm64.State.spAligned, sp] using h.aligned
  · intro i; rw [mem, sp]; exact h.workspaceRead i
  · intro i; rw [mem, sp]; exact h.workspaceWrite i
  · intro i; rw [mem, sp]; exact h.hashRead i
  · intro i; rw [mem, sp]; exact h.hashWrite i
  · intro i; rw [mem, x0]; exact h.constantsRead i
  · intro i; rw [mem, x0]; exact h.constantsValue i
  · intro i b; rw [x0, sp]; exact h.constantsOutside i b

theorem BlockReady.of_stable {s out : Arm64.State} (h : BlockReady s)
    (st : stable out = stable s) (x0 : out.readReg64 .x0 = s.readReg64 .x0) : BlockReady out := by
  have mem := congrArg Arm64.State.mem st
  have sp := congrArg Arm64.State.sp st
  exact h.transport mem sp x0

theorem BlockReady.of_core {s out : Arm64.State} (h : BlockReady s)
    (f : CoreFrame s out) : BlockReady out := h.transport f.mem f.sp f.x0

def savedHash (s : Arm64.State) := wordVector 8 s.mem (s.sp + 256#64)

theorem block_preserves_ready (s : Arm64.State) (ready : BlockReady s)
    (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outside : ∀ (i : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) :
    ∃ out, runWords blockCode s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 320#64 ∧ out.readReg64 .x5 = 64#64 ∧
      savedHash out = SHS.SHA256.compress (savedHash s) (sourceBlock s) ∧
      BlockReady out ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) := by
  obtain ⟨out, he, hf, pc, counter, hash, frame, readable, wsWrite, hWrite⟩ :=
    block_compression_source s ready.aligned hc hr ready.workspaceRead ready.workspaceWrite
      (by intro i b; have := outside i b; omega) ready.constantsRead ready.constantsValue
      (by intro i b; have := ready.constantsOutside i b; omega) ready.hashRead ready.hashWrite
  refine ⟨out, he, hf, pc, counter, hash, ?_, frame, readable⟩
  constructor
  · rw [hf.aligned]; exact ready.aligned
  · intro i; rw [hf.sp]; exact readable _ _ (ready.workspaceRead i)
  · exact wsWrite
  · intro i; rw [hf.sp]; exact readable _ _ (ready.hashRead i)
  · exact hWrite
  · intro i; rw [hf.x0]; exact readable _ _ (ready.constantsRead i)
  · intro i
    rw [hf.x0]
    exact (read32_of_cells _ (fun b => frame _ (ready.constantsOutside i b))).trans (ready.constantsValue i)
  · intro i b; rw [hf.x0, hf.sp]; exact ready.constantsOutside i b

structure OuterFrame (s out : Arm64.State) : Prop where
  state : nonMemory out = nonMemory s
  nv : nonvolatile out = nonvolatile s
  x0 : out.readReg64 .x0 = s.readReg64 .x0
  x1 : out.readReg64 .x1 = s.readReg64 .x1
  x4 : out.readReg64 .x4 = s.readReg64 .x4
  x6 : out.readReg64 .x6 = s.readReg64 .x6

theorem OuterFrame.refl (s : Arm64.State) : OuterFrame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem OuterFrame.trans {a b c : Arm64.State} (h : OuterFrame a b) (k : OuterFrame b c) :
    OuterFrame a c := ⟨k.state.trans h.state, k.nv.trans h.nv,
      k.x0.trans h.x0, k.x1.trans h.x1, k.x4.trans h.x4, k.x6.trans h.x6⟩
theorem OuterFrame.sp {s out : Arm64.State} (h : OuterFrame s out) : out.sp = s.sp := by
  have result := congrArg Arm64.State.sp h.state
  exact result

theorem CoreFrame.outer {s out : Arm64.State} (h : CoreFrame s out) : OuterFrame s out := by
  obtain ⟨hs, nv, x0, x1, _, _, x4, x6⟩ := h
  have state := congrArg nonMemory hs
  exact ⟨by simpa only [nonMemory_controlStable] using state, nv, x0, x1, x4, x6⟩

theorem DataFrame.outer {s out : Arm64.State} (h : DataFrame s out) : OuterFrame s out :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

def blockIterationCode := blockGateCode ++ (blockCode ++ blockAdvanceCode)

theorem block_iteration (s : Arm64.State) (ready : BlockReady s)
    (hc : s.readReg64 .x3 ≠ 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outside : ∀ (i : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) :
    ∃ out, runWords blockIterationCode s = some out ∧ OuterFrame s out ∧
      out.pc = s.pc ∧ out.readReg64 .x2 = s.readReg64 .x2 + 64#64 ∧
      out.readReg64 .x3 = s.readReg64 .x3 - 1#64 ∧
      savedHash out = SHS.SHA256.compress (savedHash s) (sourceBlock s) ∧
      BlockReady out ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) := by
  obtain ⟨gated, hg, postGate⟩ := exists_of_map_some _ _ _ (block_gate s hc)
  simp only [blockControlView, Prod.mk.injEq] at postGate
  obtain ⟨gs, gn, gp, g0, g1, g2, g3, g4, g5, g6⟩ := postGate
  have gf : CoreFrame s gated := ⟨controlStable_of_stable gs, gn, g0, g1, g2, g3, g4, g6⟩
  have reads (i : Fin 16) : gated.mem.canRead (gated.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [gf.mem, g2]; exact hr i
  have sep (i : Fin 16) (b : Fin 4) :
      288 ≤ (gated.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - gated.sp).toNat := by
    rw [g2, gf.sp]; exact outside i b
  obtain ⟨hashed, hh, hf, hp, _, hash, readyHash, frame, readable⟩ :=
    block_preserves_ready gated (ready.of_core gf) g5 reads sep
  obtain ⟨out, ha, postAdvance⟩ := exists_of_map_some _ _ _ (block_advance hashed)
  simp only [blockControlView, Prod.mk.injEq] at postAdvance
  obtain ⟨ast, an, ap, a0, a1, a2, a3, a4, _, a6⟩ := postAdvance
  have amem := congrArg Arm64.State.mem ast
  change out.mem = hashed.mem at amem
  have asp := congrArg Arm64.State.sp ast
  change out.sp = hashed.sp at asp
  have astable := congrArg nonMemory ast
  have af : OuterFrame hashed out :=
    ⟨by simpa only [nonMemory_stable] using astable, an, a0, a1, a4, a6⟩
  have tail := runWords_append_success hh ha
  have whole := runWords_append_success hg tail
  refine ⟨out, whole, (gf.outer.trans hf.outer).trans af, ?_, ?_, ?_, ?_,
    readyHash.of_stable ast a0, ?_, ?_⟩
  · rw [ap, hp, gp]
    simp only [BitVec.add_assoc]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    calc
      s.pc + (8#64 + (320#64 + -328#64)) = s.pc + 0#64 :=
        congrArg (s.pc + ·) (by decide +kernel)
      _ = s.pc := BitVec.add_zero _
  · rw [a2, hf.x2, g2]
  · rw [a3, hf.2.2.2.2.2.1, g3]
  · change wordVector 8 out.mem (out.sp + 256#64) = _
    rw [amem, asp]
    change savedHash hashed = _
    rw [hash]
    simp only [savedHash, sourceBlock, gf.mem, gf.sp, g2]
  · intro p h
    rw [amem]
    exact (frame p (by rw [gf.sp]; exact h)).trans (congrArg (fun m : Arm64.Memory => m.cells p) gf.mem)
  · intro a n read
    rw [amem]
    exact readable a n (by rw [gf.mem]; exact read)

def memoryBlock (m : Arm64.Memory) (base : BitVec 64) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun i => reverseWord (m.read32 (base + BitVec.ofNat 64 (4 * i.val)))

theorem outer_loop_prefix (s : Arm64.State) (ready : BlockReady s)
    (n : Nat) (bound : n < 2 ^ 64) (hc : s.readReg64 .x3 = BitVec.ofNat 64 n)
    (hr : ∀ (i : Fin n) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin n) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (k : Nat) (hk : k ≤ n) :
    ∃ out, runCycles blockIterationCode k s = some out ∧ OuterFrame s out ∧
      out.pc = s.pc ∧ out.readReg64 .x2 = s.readReg64 .x2 + BitVec.ofNat 64 (64 * k) ∧
      out.readReg64 .x3 = BitVec.ofNat 64 (n - k) ∧
      savedHash out = Fin.foldl k
        (fun H (i : Fin k) => SHS.SHA256.compress H
          (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)))) (savedHash s) ∧
      BlockReady out ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a count, s.mem.canRead a count = true → out.mem.canRead a count = true) := by
  let P (i : Nat) (mid : Arm64.State) : Prop :=
    OuterFrame s mid ∧ mid.pc = s.pc ∧
    mid.readReg64 .x2 = s.readReg64 .x2 + BitVec.ofNat 64 (64 * i) ∧
    mid.readReg64 .x3 = BitVec.ofNat 64 (n - i) ∧
    savedHash mid = Fin.foldl i
      (fun H (j : Fin i) => SHS.SHA256.compress H
        (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * j.val)))) (savedHash s) ∧
    BlockReady mid ∧
    (∀ p, 288 ≤ (p - s.sp).toNat → mid.mem.cells p = s.mem.cells p) ∧
    (∀ a count, s.mem.canRead a count = true → mid.mem.canRead a count = true)
  have h0 : P 0 s := ⟨OuterFrame.refl s, rfl, by simp, by simpa using hc,
    (Fin.foldl_zero _ _).symm, ready, by intro p hp; rfl, by intro a count read; exact read⟩
  have hs (i : Nat) (hi : i < k) (mid : Arm64.State) (hp : P i mid) :
      ∃ out, runWords blockIterationCode mid = some out ∧ P (i + 1) out := by
    obtain ⟨ff, pc, ptr, count, hash, readyMid, frame, readable⟩ := hp
    have hin : i < n := by omega
    let t : Fin n := ⟨i, hin⟩
    have positive : mid.readReg64 .x3 ≠ 0#64 := by
      intro hz
      have hn := congrArg BitVec.toNat (count.symm.trans hz)
      have subBound : n - i < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt subBound] at hn
      omega
    have reads (j : Fin 16) : mid.mem.canRead
        (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val)) 4 = true := by
      rw [ptr]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using readable _ _ (hr t j)
    have outside (j : Fin 16) (b : Fin 4) :
        288 ≤ (mid.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val) + BitVec.ofNat 64 b.val - mid.sp).toNat := by
      rw [ptr, ff.sp]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using sep t j b
    have source : sourceBlock mid = memoryBlock s.mem
        (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i)) := by
      apply Vector.ext
      intro j hj
      simp only [sourceBlock, memoryBlock, Vector.getElem_ofFn, ptr]
      apply congrArg reverseWord
      apply read32_of_cells
      intro b
      apply frame
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using sep t ⟨j, hj⟩ b
    obtain ⟨out, he, oframe, op, o2, o3, oh, readyOut, outsideOut, readableOut⟩ :=
      block_iteration mid readyMid positive reads outside
    refine ⟨out, he, ff.trans oframe, op.trans pc, ?_, ?_, ?_, readyOut, ?_, ?_⟩
    · rw [o2, ptr]
      simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [o3, count]
      have arithmetic : n - i = (n - (i + 1)) + 1 := by omega
      rw [arithmetic, BitVec.ofNat_add, BitVec.add_sub_cancel]
    · rw [oh, hash, source]
      exact (Fin.foldl_succ_last
        (fun H (j : Fin (i + 1)) => SHS.SHA256.compress H
          (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * j.val))))
        (savedHash s)).symm
    · intro p hp
      exact (outsideOut p (by rw [ff.sp]; exact hp)).trans (frame p hp)
    · intro a count read
      exact readableOut a count (readable a count read)
  exact iterateStep_invariant (runWords blockIterationCode) P k s h0 hs

end Crypto.ARM64.Imported
