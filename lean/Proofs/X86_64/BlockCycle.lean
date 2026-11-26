import Proofs.X86_64.Block
import Proofs.X86_64.OuterControl

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (wordVector)

private def resetIndex : Instr := ⟨(WordInst.rr .xor .rbx .rbx).op,2⟩
private theorem reset_bytes : decodeAt image 0x16b = some resetIndex := by decide +kernel

private theorem reset_step (s : Cpu) (live : s.ms = none) :
    let out := X86.step resetIndex s
    out.ms = none ∧ out.rip = s.rip+2 ∧ out.mem = s.mem ∧ out.regs = s.regs.set .rbx 0 := by
  obtain ⟨proj, hl, rip⟩ := word_step (.rr .xor .rbx .rbx) s 2 live
  refine ⟨hl,rip,congrArg DataState.mem proj,?_⟩
  simpa [WordInst.eval, WordOp.apply, DataState.put, project, DataState.word, resetIndex] using congrArg DataState.regs proj

private theorem hash_after_counter (s : Cpu) (v : Val) :
    wordVector 8 (byteView (s.mem.writeSize .q (s.regs.get .rsp+424) v)) (s.regs.get .rsp+256) =
      hashWords (project s) := by
  apply Vector.ext
  intro j hj
  simp only [hashWords, project, wordVector, Vector.getElem_ofFn, ← byteView_read32]
  apply congrArg (BitVec.setWidth 32)
  apply Mem.readN_congr _ _ _ 4
  intro b hb
  apply counter_frame
  let off := 256 + 4*j + b
  have addr : s.regs.get .rsp+256+BitVec.ofNat 64 (4*j)+BitVec.ofNat 64 b =
      s.regs.get .rsp + BitVec.ofNat 64 off := by simp [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [addr, ← BitVec.sub_sub, Crypto.ARM64.Imported.address_delta]
  have low : off < 288 := by dsimp [off]; omega
  have dist : ∀ a : Fin 288, 8 ≤ ((BitVec.ofNat 64 a.val) - 424).toNat := by decide +kernel
  exact dist ⟨off,low⟩

structure CycleSites (base : Val) : Prop where
  guardTarget : canonical (base+0x2d3) = true
  inputTarget : canonical (base+0x16d) = true
  scheduleTarget : canonical (base+0x17f) = true
  roundTarget : canonical (base+0x204) = true
  repeatTarget : canonical (base+0x15c) = true

def blockGuardEvents (base sp : Val) := frameFragment base sp 0x15c 2

def cycleEvents (base sp ptr k : Val) : List Event :=
  blockGuardEvents base sp ++ frameFragment base sp 0x16b 1 ++
    blockEvents base sp ptr k ++ frameFragment base sp 0x2c2 3

structure CycleResult (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x15c
  rsp : out.regs.get .rsp = s.regs.get .rsp
  rdi : out.regs.get .rdi = s.regs.get .rdi
  rbp : out.regs.get .rbp = s.regs.get .rbp + 64
  count : blocksLeft out = blocksLeft s - 1
  frame : ∀ p, 288 ≤ (p-s.regs.get .rsp).toNat → 8 ≤ (p-(s.regs.get .rsp+424)).toNat →
    out.mem.read p = s.mem.read p
  hash : hashWords (project out) = Crypto.Reference.WordModel.compress (hashWords (project s)) (sourceBlock s)
  observations : ObservedExecution base s (cycleEvents base (s.regs.get .rsp)
    (s.regs.get .rbp) (s.regs.get .rdi)) out

attribute [local irreducible] steps hashWords Crypto.Reference.WordModel.compress image X86.step

theorem block_cycle (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x15c)
    (loaded : ImageLoaded base s.mem) (k : s.regs.get .rdi = base+0x390) (positive : blocksLeft s ≠ 0)
    (sites : CycleSites base)
    (sep : ∀ j, j < image.size → 432 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (src : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.regs.get .rbp+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val-s.regs.get .rsp).toNat) :
    ∃ out, steps base 3975 s = some out ∧ CycleResult base s out := by
  obtain ⟨checked, guardRun, gl, gm, gr, gp⟩ := blocks_test base s live loaded pc sites.guardTarget
  rw [if_neg positive] at gp
  let ready := X86.step resetIndex checked
  have reset := one_at base checked 0x16b _ gl (gm ▸ loaded) gp reset_bytes (by decide) (by decide)
  obtain ⟨rl, rp, rm, rr⟩ := reset_step checked gl
  change ready.regs = _ at rr
  change ready.mem = _ at rm
  have rsp : ready.regs.get .rsp = s.regs.get .rsp := by simp [rr, gr, Regs.get_set_ne]
  have rbp : ready.regs.get .rbp = s.regs.get .rbp := by simp [rr, gr, Regs.get_set_ne]
  have rdi : ready.regs.get .rdi = s.regs.get .rdi := by simp [rr, gr, Regs.get_set_ne]
  have m := rm.trans gm
  obtain ⟨mixed, run, post⟩ := block_loaded base ready rl (by simpa [gp, BitVec.add_assoc] using rp)
    (by simp [rr]) (m ▸ loaded) (rdi.trans k)
    (fun j hj => by rw [rsp]; exact Nat.le_trans (by decide : 288 ≤ 432) (sep j hj))
    (by simpa only [rbp, rsp] using src) sites.inputTarget sites.scheduleTarget sites.roundTarget
  have sp := post.stack.trans rsp
  have frame (p : Val) (hp : 288 ≤ (p-s.regs.get .rsp).toNat) : mixed.mem.read p = s.mem.read p :=
    (post.frame _ (by rw [rsp]; exact hp)).trans (congrArg (fun mem : Mem => mem.read p) m)
  have imageM : ImageLoaded base mixed.mem :=
    fun j hj => (frame _ (Nat.le_trans (by decide : 288 ≤ 432) (sep j hj))).trans (loaded j hj)
  obtain ⟨out, advance, ok, back, regs, mem⟩ := advance_loaded base mixed post.live imageM post.pc sites.repeatTarget
    (fun j hj => by rw [sp]; exact Crypto.ARM64.Imported.region_store_delta _ _ 424 432 8 (by decide) (sep j hj))
  have spOut : out.regs.get .rsp = mixed.regs.get .rsp := by simp [regs, Regs.get_set_ne]
  have count : blocksLeft mixed = blocksLeft s := by
    unfold blocksLeft
    rw [sp]
    apply Mem.readN_congr _ _ _ 8
    intro b hb
    apply frame
    change 288 ≤ ((s.regs.get .rsp + 424#64 + BitVec.ofNat 64 b) - s.regs.get .rsp).toNat
    rw [BitVec.add_assoc, ← BitVec.ofNat_add (n := 64) 424 b, Crypto.ARM64.Imported.address_delta,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have H : hashWords (project ready) = hashWords (project s) := by simp only [hashWords, project, m, rsp]
  have B : sourceBlock ready = sourceBlock s := by simp only [sourceBlock, sourceWord, rbp, m]
  have guardTrace : ObservedExecution base s (blockGuardEvents base (s.regs.get .rsp)) checked :=
    steps_observe_fragment guardRun pc (by decide +kernel)
  have resetTrace := steps_observe_fragment reset gp (by decide +kernel)
  have blockTrace := post.observations
  have advanceTrace := steps_observe_fragment advance post.pc (by decide +kernel)
  have guardSp : checked.regs.get .rsp = s.regs.get .rsp := by rw [gr]
  rw [guardSp] at resetTrace
  rw [rsp,rbp,rdi] at blockTrace
  rw [sp] at advanceTrace
  have observed : ObservedExecution base s (cycleEvents base (s.regs.get .rsp)
      (s.regs.get .rbp) (s.regs.get .rdi)) out :=
    by simpa only [cycleEvents, List.append_assoc] using guardTrace.append (resetTrace.append (blockTrace.append advanceTrace))
  refine ⟨out, steps_append guardRun (steps_append reset (steps_append run advance)), ⟨ok, back,
    spOut.trans sp, by simp [regs, Regs.get_set_ne, post.constants, rdi],
    by simp [regs, post.blockPtr, rbp], ?_, ?_, ?_, observed⟩⟩
  · rw [blocksLeft, spOut, mem, read64_write64, count]
  · intro p a b
    rw [mem, counter_frame _ _ _ _ (by simpa only [sp] using b), frame _ a]
  · have preserve : hashWords (project out) = hashWords (project mixed) := by
      unfold hashWords
      simp only [project]
      rw [mem, spOut]
      simpa only [hashWords, project] using hash_after_counter mixed (blocksLeft mixed - 1)
    exact preserve.trans (post.hash.trans (by rw [H,B]))

end Crypto.X86_64
