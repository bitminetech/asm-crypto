import Proofs.X86_64.BlockCycle

namespace Crypto.X86_64
open X86

def wordsFrom (m : Mem) (ptr : Val) : Vector Word 16 := Vector.ofFn fun i =>
  let a := ptr + BitVec.ofNat 64 (4*i.val)
  m.read a ++ m.read (a+1) ++ m.read (a+2) ++ m.read (a+3)

def foldBlocks (m : Mem) (ptr : Val) (n : Nat) (h : Vector Word 8) : Vector Word 8 :=
  match n with
  | 0 => h
  | k+1 => foldBlocks m (ptr+64) k (Crypto.Reference.WordModel.compress h (wordsFrom m ptr))

def outsideCycle (sp p : Val) : Prop :=
  288 ≤ (p-sp).toNat ∧ 8 ≤ (p-(sp+424)).toNat

private def byteAt (ptr : Val) (t : Nat) (i : Fin 16) (b : Fin 4) :=
  ptr + BitVec.ofNat 64 (64*t) + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 b.val

private theorem byteAt_succ (ptr : Val) (t : Nat) (i : Fin 16) (b : Fin 4) :
    byteAt (ptr+64) t i b = byteAt ptr (t+1) i b := by
  simp [byteAt, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
  rw [← BitVec.add_assoc, BitVec.add_comm (64#64), BitVec.add_assoc]

private structure PhaseInputs (s : Cpu) (m : Mem) (n : Nat) : Prop where
  bytes : ∀ t, t < n → ∀ (i : Fin 16) (b : Fin 4),
    let p := byteAt (s.regs.get .rbp) t i b
    outsideCycle (s.regs.get .rsp) p ∧ s.mem.read p = m.read p

private theorem head_input (s : Cpu) (m : Mem) (n : Nat) (input : PhaseInputs s m (n+1)) :
    sourceBlock s = wordsFrom m (s.regs.get .rbp) := by
  apply Vector.ext
  intro i hi
  let ix : Fin 16 := ⟨i,hi⟩
  let a := s.regs.get .rbp + BitVec.ofNat 64 (4*i)
  have eq (b : Fin 4) : s.mem.read (a + BitVec.ofNat 64 b.val) = m.read (a + BitVec.ofNat 64 b.val) := by
    simpa [byteAt, ix, a] using (input.bytes 0 (by omega) ix b).2
  simp only [sourceBlock, sourceWord, wordsFrom, Vector.getElem_ofFn]
  exact congrArg₂ BitVec.append (congrArg₂ BitVec.append
    (congrArg₂ BitVec.append (by simpa using eq 0) (eq 1)) (eq 2)) (eq 3)

private theorem tail_input (base : Val) (s out : Cpu) (m : Mem) (n : Nat)
    (input : PhaseInputs s m (n+1)) (post : CycleResult base s out) : PhaseInputs out m n := by
  constructor
  intro t ht i b
  dsimp only
  rw [post.rbp, byteAt_succ, post.rsp]
  obtain ⟨apart, initial⟩ := input.bytes (t+1) (by omega) i b
  exact ⟨apart, (post.frame _ apart.1 apart.2).trans initial⟩

def phaseEvents (base sp k : Val) : Nat → Val → List Event
  | 0, _ => blockGuardEvents base sp
  | n+1, ptr => cycleEvents base sp ptr k ++ phaseEvents base sp k n (ptr+64)

structure PhaseResult (base : Val) (s out : Cpu) (m : Mem) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x2d3
  stack : out.regs.get .rsp = s.regs.get .rsp
  constants : out.regs.get .rdi = s.regs.get .rdi
  pointer : out.regs.get .rbp = s.regs.get .rbp + BitVec.ofNat 64 (64*n)
  count : blocksLeft out = 0
  frame : ∀ p, outsideCycle (s.regs.get .rsp) p → out.mem.read p = s.mem.read p
  hash : hashWords (project out) = foldBlocks m (s.regs.get .rbp) n (hashWords (project s))
  observations : ObservedExecution base s (phaseEvents base (s.regs.get .rsp) (s.regs.get .rdi)
    n (s.regs.get .rbp)) out

attribute [local irreducible] steps hashWords image Crypto.Reference.WordModel.compress

private theorem phase_loop (base : Val) (sites : CycleSites base) (m : Mem) (n : Nat) (s : Cpu)
    (live : s.ms = none) (pc : s.rip = base+0x15c) (loaded : ImageLoaded base s.mem)
    (k : s.regs.get .rdi = base+0x390) (count : blocksLeft s = BitVec.ofNat 64 n)
    (bound : n < 2^64) (input : PhaseInputs s m n)
    (sep : ∀ j, j < image.size → 432 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base (3975*n+2) s = some out ∧ PhaseResult base s out m n := by
  induction n generalizing s with
  | zero =>
    obtain ⟨out, run, ok, mem, regs, rip⟩ := blocks_test base s live loaded pc sites.guardTarget
    have empty : blocksLeft s = 0 := count
    refine ⟨out, run, ⟨ok, by simpa [empty] using rip, by rw [regs], by rw [regs],
      by simp [regs], by simpa only [blocksLeft, regs, mem] using empty, ?_, ?_,
      steps_observe_fragment run pc (by decide +kernel)⟩⟩
    · exact fun p _ => congrArg (fun v : Mem => v.read p) mem
    · simp only [hashWords, project, regs, mem, foldBlocks]
  | succ n ih =>
    have positive : blocksLeft s ≠ 0 := by
      intro z
      have h := congrArg BitVec.toNat (count.symm.trans z)
      change (n+1) % (2^64) = 0 at h
      rw [Nat.mod_eq_of_lt bound] at h
      omega
    obtain ⟨mid, one, post⟩ := block_cycle base s live pc loaded k positive sites sep
      (fun i b => by simpa [byteAt] using Nat.le_trans (by decide : 256 ≤ 288) (input.bytes 0 (by omega) i b).1.1)
    have code : ImageLoaded base mid.mem := fun j hj =>
      (post.frame _ (Nat.le_trans (by decide : 288 ≤ 432) (sep j hj))
        (Crypto.ARM64.Imported.region_store_delta _ _ 424 432 8 (by decide) (sep j hj))).trans (loaded j hj)
    have dec : blocksLeft mid = BitVec.ofNat 64 n := by
      rw [post.count, count, BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    obtain ⟨out, tail, done⟩ := ih mid post.live post.pc code (post.rdi.trans k) dec (by omega)
      (tail_input base s mid m n input post) (by simpa only [post.rsp] using sep)
    have rest := done.observations
    rw [post.rsp,post.rdi,post.rbp] at rest
    refine ⟨out, by simpa only [show 3975*(n+1)+2 = 3975+(3975*n+2) by omega] using steps_append one tail,
      ⟨done.live, done.pc, done.stack.trans post.rsp, done.constants.trans post.rdi, ?_, done.count, ?_, ?_, post.observations.append rest⟩⟩
    · rw [done.pointer, post.rbp, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
      rw [BitVec.add_comm (64 : Val)]; rfl
    · intro p hp
      exact (done.frame _ (by simpa only [post.rsp] using hp)).trans (post.frame p hp.1 hp.2)
    · rw [done.hash, post.rbp, post.hash, head_input s m n input, foldBlocks]

/-- Execute a phase against a snapshot of the source bytes. Only source bytes
of the requested blocks have to agree with that snapshot. -/
theorem phase_snapshot (base : Val) (sites : CycleSites base) (s : Cpu) (m : Mem) (n : Nat)
    (live : s.ms = none) (pc : s.rip = base+0x15c) (loaded : ImageLoaded base s.mem)
    (k : s.regs.get .rdi = base+0x390) (count : (blocksLeft s).toNat = n)
    (sep : ∀ j, j < image.size → 432 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (src : ∀ t, t < n → ∀ (i : Fin 16) (b : Fin 4),
      let a := s.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val
      outsideCycle (s.regs.get .rsp) a ∧ s.mem.read a = m.read a) :
    ∃ out, steps base (3975*n+2) s = some out ∧ PhaseResult base s out m n :=
  phase_loop base sites m n s live pc loaded k (by rw [← count]; simp)
    (by rw [← count]; exact (blocksLeft s).isLt) ⟨src⟩ sep

/-- A complete message or padding phase. Each block is read from the original
memory in order. The last two instructions detect the exhausted block count. -/
theorem phase_loaded (base : Val) (sites : CycleSites base) (s : Cpu) (n : Nat)
    (live : s.ms = none) (pc : s.rip = base+0x15c) (loaded : ImageLoaded base s.mem)
    (k : s.regs.get .rdi = base+0x390) (count : (blocksLeft s).toNat = n)
    (sep : ∀ j, j < image.size → 432 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (src : ∀ t, t < n → ∀ (i : Fin 16) (b : Fin 4), outsideCycle (s.regs.get .rsp)
      (s.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val)) :
    ∃ out, steps base (3975*n+2) s = some out ∧ PhaseResult base s out s.mem n :=
  phase_snapshot base sites s s.mem n live pc loaded k count sep (fun t ht i b => ⟨src t ht i b,rfl⟩)

end Crypto.X86_64
