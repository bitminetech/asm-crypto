import Proofs.X86_64.Fragments
import Proofs.X86_64.CompressionTrace

namespace Crypto.X86_64
open X86 Crypto.Reference.WordModel

private theorem latchBytes :
    decodeAt image 0x279 = some incIndex ∧
    decodeAt image 0x27c = some (cmpLimit 64) ∧
    decodeAt image 0x280 = some (branchBelow (-126)) := by decide +kernel

/-- Work done by the first n FIPS rounds on one block. -/
def roundFold (W : Vector Word 64) (H : Vector Word 8) (n : Nat) :=
  Fin.foldl n (fun work i => specRoundStep W i.val work) H

structure RoundState (base : Val) (s out : Cpu) (W : Vector Word 64) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = if n < 64 then base + 0x204 else base + 0x282
  index : out.regs.get .rbx = BitVec.ofNat 64 n
  mem : out.mem = s.mem
  constants : out.regs.get .rdi = s.regs.get .rdi
  stack : out.regs.get .rsp = s.regs.get .rsp
  blockPtr : out.regs.get .rbp = s.regs.get .rbp
  hash : working (project out) = roundFold W (working (project s)) n
  observations : ObservedExecution base s (WordLoop.round.prefix base (s.regs.get .rsp)
    (s.regs.get .rbp) (s.regs.get .rdi) n) out

private theorem working_after_index (out body : Cpu) (v : Val)
    (regs : out.regs = body.regs.set .rbx v) :
    working (project out) = working (project body) := by
  simp (config := { decide := true }) [working, project, DataState.word, regs, Regs.get_set_ne]

private theorem roundFold_succ (W : Vector Word 64) (H : Vector Word 8) (n : Nat) :
    roundFold W H (n+1) = specRoundStep W n (roundFold W H n) := by
  unfold roundFold
  rw [Fin.foldl_succ_last]
  rfl

attribute [local irreducible] steps X86.run specRoundStep working roundFold wordsAt

set_option maxRecDepth 800 in
theorem round_prefix (base : Val) (s : Cpu) (W : Vector Word 64)
    (live : s.ms = none) (pc : s.rip = base + 0x204) (index : s.regs.get .rbx = 0)
    (loaded : ImageLoaded base s.mem) (target : canonical (base + 0x204) = true)
    (constants : ∀ i : Fin 64, wordsAt s .rdi i.val = Crypto.Reference.WordModel.K[i.val]!)
    (schedule : ∀ i : Fin 64, wordsAt s .rsp i.val = W[i.val]!) (n : Nat) (bound : n ≤ 64) :
    ∃ out, steps base (n * 43) s = some out ∧ RoundState base s out W n := by
  induction n with
  | zero => exact ⟨s, by simp [steps], ⟨live, pc, index, rfl, rfl, rfl, rfl, by simp [roundFold], .nil _⟩⟩
  | succ n ih =>
    have small : n < 64 := by omega
    obtain ⟨mid, reached, state⟩ := ih (by omega)
    have start : mid.rip = base + 0x204 := by simpa [small] using state.pc
    have kv := constants ⟨n,small⟩
    have wv := schedule ⟨n,small⟩
    obtain ⟨body, runBody, bodyLive, bodyPC, mem, idx, rdi, rsp, rbp, work⟩ :=
      round_loaded base mid state.live (state.mem ▸ loaded) start n state.index W
        (by simpa only [wordsAt, state.mem, state.constants] using kv)
        (by simpa only [wordsAt, state.mem, state.stack] using wv)
    have code : ImageLoaded base body.mem := (mem.trans state.mem) ▸ loaded
    have back : body.rip + 9 + (-126) = base + 0x204 := by
      rw [bodyPC]; simp [BitVec.add_assoc]
    obtain ⟨out, latched, regs, sameMem, ok, endPC⟩ := count_exit base body 0x279 64 (-126)
      bodyLive code bodyPC (by decide) latchBytes.1 latchBytes.2.1 latchBytes.2.2
      (by rw [back]; exact target)
    have next : body.regs.get .rbx + 1 = BitVec.ofNat 64 (n+1) := by
      rw [idx, state.index, BitVec.ofNat_add]; rfl
    have natBound : n+1 < 2^64 := by omega
    have observed := WordLoop.round.observed_iteration state.live bodyLive start bodyPC state.index runBody latched
    rw [state.stack, state.blockPtr, state.constants] at observed
    refine ⟨out, ?_, ⟨ok, ?_, ?_, sameMem.trans (mem.trans state.mem), ?_, ?_, ?_, ?_,
      state.observations.append (by simpa only [WordLoop.initialIndex, Nat.zero_add] using observed)⟩⟩
    · rw [Nat.succ_mul]
      exact steps_append reached (steps_append runBody latched)
    · rw [next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt natBound, back, bodyPC] at endPC
      simpa only [BitVec.add_assoc] using endPC
    · rw [regs, Regs.get_set_same, next]
    · rw [regs, Regs.get_set_ne _ _ _ _ (by decide), rdi, state.constants]
    · rw [regs, Regs.get_set_ne _ _ _ _ (by decide), rsp, state.stack]
    · rw [regs, Regs.get_set_ne _ _ _ _ (by decide), rbp, state.blockPtr]
    · exact (working_after_index out body _ regs).trans (work.trans
        ((congrArg (specRoundStep W n) state.hash).trans (roundFold_succ W _ n).symm))

/-- Starting at the first compression round, all 64 iterations fetch and
execute 2,752 x86 instructions and leave the eight FIPS working words in
r8d–r15d at the feed-forward entry. -/
theorem rounds_loaded (base : Val) (s : Cpu) (W : Vector Word 64)
    (live : s.ms = none) (pc : s.rip = base + 0x204) (index : s.regs.get .rbx = 0)
    (loaded : ImageLoaded base s.mem) (target : canonical (base + 0x204) = true)
    (constants : ∀ i : Fin 64, wordsAt s .rdi i.val = Crypto.Reference.WordModel.K[i.val]!)
    (schedule : ∀ i : Fin 64, wordsAt s .rsp i.val = W[i.val]!) :
    ∃ out, steps base 2752 s = some out ∧ RoundState base s out W 64 :=
  round_prefix base s W live pc index loaded target constants schedule 64 (by decide)

end Crypto.X86_64
