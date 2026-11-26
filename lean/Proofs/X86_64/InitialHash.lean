import Proofs.X86_64.PhaseSwitch
import Proofs.X86_64.Tables
import Proofs.X86_64.HashLoad
import Proofs.X86_64.FrameTrace
import Proofs.ARM64.ImportedHashInitWords

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (wordVector)

private def ivStart : FrameCode := [(.relative .rax 0x376,7)]
private def ivPC (n : Nat) := if n = 0 then 0x11a else 0x119+12*n
def ivPair (i : Fin 4) : FrameCode :=
  [(.load .rcx .rax (BitVec.ofNat 64 (8*i.val)), if i.val = 0 then 3 else 4),
    (.store (256+8*i.val) .rcx,8)]
private def ivEnd : FrameCode := [(.relative .rdi 0x240,7),(.constant 432 0,12)]

private theorem iv_decode : decodeSeq 0x113 ivStart.length = some (moveInstructions ivStart) ∧
    (∀ i : Fin 4, decodeSeq (ivPC i.val) (ivPair i).length = some (moveInstructions (ivPair i)) ∧
      ivPC i.val + (if i.val = 0 then 3 else 4) + 8 = ivPC (i.val+1)) ∧
    decodeSeq 0x149 ivEnd.length = some (moveInstructions ivEnd) := by decide +kernel

private def copyIV (m : Mem) (sp pool : Val) : Nat → Mem
  | 0 => m
  | n+1 => (copyIV m sp pool n).writeSize .q (sp+BitVec.ofNat 64 (256+8*n))
      (m.readSize .q (pool+BitVec.ofNat 64 (8*n)))

private theorem copied_iv_words (m : Mem) (sp pool : Val) :
    wordVector 8 (byteView (copyIV m sp pool 4)) (sp+256) = wordVector 8 (byteView m) pool := by
  let snapshot : Arm64.State := {mem := byteView m, sp := sp, pc := pool - 732}
  have equal := Crypto.ARM64.Imported.initialHashMemory_words snapshot
  simpa [snapshot, Crypto.ARM64.Imported.initialHashMemory, List.range_succ, copyIV,
    byteView_write64, byteView_read64, BitVec.sub_eq_add_neg, BitVec.add_assoc] using equal

private theorem pair_wf (i : Fin 4) : ∀ p ∈ ivPair i, p.1.wellPlaced 288 := by
  intro p h
  simp only [ivPair, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h <;> subst p
  · change GPR.rcx ≠ .rsp
    decide
  · change 256+8*i.val+8 ≤ 288
    have := i.isLt
    omega

def ivPairEvents (base sp : Val) (i : Fin 4) : List Event :=
  let regs := (Regs.set {} .rsp sp).set .rax (base+0x490)
  moveEvents (ivPair i) {rip := base+BitVec.ofNat 64 (ivPC i.val), regs := regs}

def ivPrefixEvents (base sp : Val) : Nat → List Event
  | 0 => frameFragment base sp 0x113 1
  | n+1 => ivPrefixEvents base sp n ++
      if h : n < 4 then ivPairEvents base sp ⟨n,h⟩ else []

private structure IVPrefix (base : Val) (s out : Cpu) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base+BitVec.ofNat 64 (ivPC n)
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rbp = s.regs.get .rbp
  pool : out.regs.get .rax = base+0x490
  mem : out.mem = copyIV s.mem (s.regs.get .rsp) (base+0x490) n
  frame : ∀ p, 288 ≤ (p-s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p
  observations : ObservedExecution base s (ivPrefixEvents base (s.regs.get .rsp) n) out

private theorem iv_prefix (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x113)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 288 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (n : Nat) (bound : n ≤ 4) :
    ∃ out, steps base (1+2*n) s = some out ∧ IVPrefix base s out n := by
  induction n with
  | zero =>
    have run := moves_loaded base ivStart 0x113 288 s live pc loaded sep
      (by intro p hp; simp [ivStart] at hp; subst p; decide) iv_decode.1
    have observe := steps_observe_fragment (count := 1) run pc (by decide +kernel)
    refine ⟨_, run, ⟨?_,?_,?_,?_,?_,?_,?_,observe⟩⟩ <;>
      simp [moveRun, ivStart, FrameMove.eval, pc, live, ivPC, copyIV, Regs.get_set_ne, BitVec.add_assoc]
  | succ n ih =>
    let i : Fin 4 := ⟨n,by omega⟩
    obtain ⟨mid, run, prev⟩ := ih (by omega)
    obtain ⟨decode, next⟩ := iv_decode.2.1 i
    have code : ImageLoaded base mid.mem := fun j hj => (prev.frame _ (sep j hj)).trans (loaded j hj)
    have pair := moves_loaded base (ivPair i) (ivPC i.val) 288 mid prev.live prev.pc code
      (by simpa only [prev.stack] using sep) (pair_wf i) decode
    have val : mid.mem.readSize .q ((base+0x490)+BitVec.ofNat 64 (8*n)) =
        s.mem.readSize .q ((base+0x490)+BitVec.ofNat 64 (8*n)) := by
      apply Mem.readN_congr _ _ _ 8
      intro b hb
      apply prev.frame
      have size : image.size = 1200 := by decide +kernel
      have fact := sep (0x490+8*n+b) (by rw [size]; omega)
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using fact
    let out := moveRun (ivPair i) mid
    have mem : out.mem = mid.mem.writeSize .q (s.regs.get .rsp+BitVec.ofNat 64 (256+8*n))
        (s.mem.readSize .q ((base+0x490)+BitVec.ofNat 64 (8*n))) := by
      simp [out, moveRun, ivPair, FrameMove.eval, prev.stack, prev.pool, Regs.get_set_ne, i]
      exact congrArg (mid.mem.writeSize .q _) val
    have oneTrace := moves_observed (ivPair i) prev.live pair prev.pc decode (by
      simp [ivPair,moveInstructions,linear,FrameMove.op])
    have eq : moveEvents (ivPair i) mid = ivPairEvents base (s.regs.get .rsp) i := by
      simp [ivPairEvents,ivPair, moveEvents,FrameMove.eval,prev.stack,prev.pc,prev.pool,Regs.get_set_ne,i]
    rw [eq] at oneTrace
    have trace := prev.observations.append oneTrace
    refine ⟨out, by simpa only [show 1+2*(n+1) = (1+2*n)+2 by omega] using steps_append run pair,
      ⟨?_,?_,?_,?_,?_,?_,?_, by simpa only [ivPrefixEvents,dif_pos (show n < 4 by omega)] using trace⟩⟩
    · exact prev.live
    · rw [← next]
      simp [out, moveRun, ivPair, FrameMove.eval, prev.pc, BitVec.ofNat_add, BitVec.add_assoc, i]
    · simpa [out, moveRun, ivPair, FrameMove.eval, Regs.get_set_ne] using prev.stack
    · simpa [out, moveRun, ivPair, FrameMove.eval, Regs.get_set_ne] using prev.ptr
    · simpa [out, moveRun, ivPair, FrameMove.eval, Regs.get_set_ne] using prev.pool
    · rw [mem, prev.mem, copyIV]
    · intro p hp
      rw [mem, counter_frame _ _ _ _ (Crypto.ARM64.Imported.region_store_delta _ _ (256+8*n) 288 8 (by omega) hp)]
      exact prev.frame _ hp

private theorem iv_loaded_words (base : Val) (m : Mem) (loaded : ImageLoaded base m) :
    wordVector 8 (byteView m) (base+0x490) = SHS.SHA256.H0_256 := by
  apply Vector.ext
  intro j hj
  have size : image.size = 1200 := by decide +kernel
  have read := loaded_word base m loaded (0x490+4*j) (by rw [size]; omega)
  have word := congrArg (fun v : Vector Word 8 => v[j]) image_constants.2
  simp only [wordVector, Vector.getElem_ofFn]
  simp only [Vector.getElem_ofFn] at word
  rw [← byteView_read32]
  apply Eq.trans _ word
  simpa [BitVec.ofNat_add, BitVec.add_assoc] using read

def initialHashEvents (base sp : Val) : List Event :=
  ivPrefixEvents base sp 4 ++ frameFragment base sp 0x149 2

structure InitialHashState (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x15c
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rbp = s.regs.get .rbp
  constants : out.regs.get .rdi = base+0x390
  phase : phase out = 0
  hash : hashWords (project out) = SHS.SHA256.H0_256
  frame : ∀ p, 288 ≤ (p-s.regs.get .rsp).toNat → 8 ≤ (p-(s.regs.get .rsp+432)).toNat →
    out.mem.read p = s.mem.read p
  observations : ObservedExecution base s (initialHashEvents base (s.regs.get .rsp)) out

theorem initial_hash_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x113)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 440 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base 11 s = some out ∧ InitialHashState base s out := by
  obtain ⟨mid, copied, post⟩ := iv_prefix base s live pc loaded
    (fun j hj => Nat.le_trans (by decide : 288 ≤ 440) (sep j hj)) 4 (by decide)
  have code : ImageLoaded base mid.mem := fun j hj =>
    (post.frame _ (Nat.le_trans (by decide : 288 ≤ 440) (sep j hj))).trans (loaded j hj)
  have run := moves_loaded base ivEnd 0x149 440 mid post.live post.pc code (by simpa only [post.stack] using sep)
    (by intro p h; simp only [ivEnd,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h|h <;> subst p <;> decide)
    iv_decode.2.2
  let out := moveRun ivEnd mid
  have mem : out.mem = mid.mem.writeSize .q (s.regs.get .rsp+432) 0 := by
    simp [out, moveRun, ivEnd, FrameMove.eval, Regs.get_set_ne, post.stack]
  have sp : out.regs.get .rsp = s.regs.get .rsp := by simpa [out, moveRun, ivEnd, FrameMove.eval, Regs.get_set_ne] using post.stack
  have pool := (copied_iv_words s.mem (s.regs.get .rsp) (base+0x490)).trans (iv_loaded_words base _ loaded)
  have last := steps_observe_fragment run post.pc (by decide +kernel)
  rw [post.stack] at last
  have observing : ObservedExecution base s (initialHashEvents base (s.regs.get .rsp)) out :=
    post.observations.append last
  refine ⟨out, steps_append copied run, ⟨by simpa [out, moveRun, ivEnd, FrameMove.eval] using post.live, ?_, sp, ?_, ?_, ?_, ?_, ?_, observing⟩⟩
  · simp [out, moveRun, ivEnd, FrameMove.eval, post.pc, ivPC, BitVec.add_assoc]
  · simpa [out, moveRun, ivEnd, FrameMove.eval, Regs.get_set_ne] using post.ptr
  · simp [out, moveRun, ivEnd, FrameMove.eval, post.pc, ivPC, BitVec.add_assoc]
  · rw [phase, sp, mem, read64_write64]
  · apply Eq.trans _ pool
    apply Vector.ext
    intro j hj
    simp only [hashWords, project, wordVector, Vector.getElem_ofFn, sp, mem, ← post.mem, ← byteView_read32]
    apply congrArg (BitVec.setWidth 32)
    apply Mem.readN_congr _ _ _ 4
    intro b hb
    apply counter_frame
    rw [BitVec.add_assoc, BitVec.add_assoc, stack_delta]
    have small : ∀ (j : Fin 8) (b : Fin 4),
        8 ≤ (256+(BitVec.ofNat 64 (4*j.val)+BitVec.ofNat 64 b.val)-432).toNat := by decide +kernel
    exact small ⟨j,hj⟩ ⟨b,hb⟩
  · intro p hf hs
    rw [mem, counter_frame _ _ _ _ hs, post.frame _ hf]

end Crypto.X86_64
