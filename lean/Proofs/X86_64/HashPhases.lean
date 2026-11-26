import Proofs.X86_64.BlockPhase
import Proofs.X86_64.PhaseSwitch

namespace Crypto.X86_64
open X86

def outsidePhases (sp p : Val) := 288 ≤ (p-sp).toNat ∧ 16 ≤ (p-(sp+424)).toNat

private theorem apart_cycle {sp p : Val} (h : outsidePhases sp p) : outsideCycle sp p :=
  ⟨h.1,Nat.le_trans (by decide) h.2⟩

private theorem outside_image (p sp : Val) (h : 440 ≤ (p-sp).toNat) : outsidePhases sp p :=
  ⟨Nat.le_trans (by decide) h,Crypto.ARM64.Imported.region_store_delta _ _ 424 440 16 (by decide) h⟩

private theorem phase_slot (sp : Val) (d : Nat) (b : Fin 8)
    (h : ∀ j : Fin 8, 288 ≤ (BitVec.ofNat 64 d+BitVec.ofNat 64 j.val).toNat ∧
      8 ≤ ((BitVec.ofNat 64 d+BitVec.ofNat 64 j.val)-424).toNat) :
    outsideCycle sp (sp+BitVec.ofNat 64 d+BitVec.ofNat 64 b.val) := by
  unfold outsideCycle
  rw [BitVec.add_assoc, BitVec.add_comm sp, BitVec.add_sub_cancel, BitVec.add_comm _ sp, stack_delta]
  exact h b

private theorem read_phase_slot (s out : Cpu) (base : Val) (m : Mem) (n d : Nat)
    (post : PhaseResult base s out m n)
    (h : ∀ b : Fin 8, 288 ≤ (BitVec.ofNat 64 d+BitVec.ofNat 64 b.val).toNat ∧
      8 ≤ ((BitVec.ofNat 64 d+BitVec.ofNat 64 b.val)-424).toNat) :
    out.mem.readSize .q (out.regs.get .rsp+BitVec.ofNat 64 d) =
    s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) := by
  rw [post.stack]
  exact Mem.readN_congr _ _ _ 8 (fun b hb => post.frame _ (phase_slot _ d ⟨b,hb⟩ h))

private theorem pad_apart (sp : Val) (t : Fin 2) (i : Fin 16) (b : Fin 4) : outsidePhases sp
    (sp+288+BitVec.ofNat 64 (64*t.val)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val) := by
  let o := 288+64*t.val+4*i.val+b.val
  have addr : sp+288+BitVec.ofNat 64 (64*t.val)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val =
      sp+BitVec.ofNat 64 o := by simp [o, BitVec.ofNat_add, BitVec.add_assoc]
  unfold outsidePhases
  rw [addr, stack_delta, Crypto.ARM64.Imported.address_delta]
  have bound : 288 ≤ o ∧ o < 416 := by
    dsimp [o]
    have := t.isLt
    have := i.isLt
    have := b.isLt
    omega
  have finite : ∀ j : Fin 416, 16 ≤ ((BitVec.ofNat 64 j.val)-424).toNat := by decide +kernel
  exact ⟨by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2^64)] using bound.1,finite ⟨o,bound.2⟩⟩

private theorem switch_hash (base : Val) (s out : Cpu) (post : SwitchResult base s out) :
    hashWords (project out) = hashWords (project s) := by
  apply Vector.ext
  intro j hj
  simp only [hashWords, project, Crypto.ARM64.Imported.wordVector, Vector.getElem_ofFn, post.stack, ← byteView_read32]
  apply congrArg (BitVec.setWidth 32)
  apply Mem.readN_congr _ _ _ 4
  intro b hb
  apply post.frame
  rw [BitVec.add_assoc, BitVec.add_assoc, stack_delta]
  have finite : ∀ (j : Fin 8) (b : Fin 4), 16 ≤
      (256+(BitVec.ofNat 64 (4*j.val)+BitVec.ofNat 64 b.val)-424).toNat := by decide +kernel
  exact finite ⟨j,hj⟩ ⟨b,hb⟩

def phaseTestEvents (base sp : Val) := frameFragment base sp 0x2d3 2

def hashPhasesEvents (base sp ptr : Val) (n k : Nat) : List Event :=
  phaseEvents base sp (base+0x390) n ptr ++ phaseTestEvents base sp ++
    frameFragment base sp 0x2de 5 ++ phaseEvents base sp (base+0x390) k (sp+288) ++ phaseTestEvents base sp

structure HashPhasesResult (base : Val) (s out : Cpu) (n k : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x307
  stack : out.regs.get .rsp = s.regs.get .rsp
  frame : ∀ p, outsidePhases (s.regs.get .rsp) p → out.mem.read p = s.mem.read p
  hash : hashWords (project out) = foldBlocks s.mem (s.regs.get .rsp+288) k
    (foldBlocks s.mem (s.regs.get .rbp) n (hashWords (project s)))
  observations : ObservedExecution base s (hashPhasesEvents base (s.regs.get .rsp) (s.regs.get .rbp) n k) out

attribute [local irreducible] steps image hashWords Crypto.Reference.WordModel.compress foldBlocks

/-- The message loop, phase switch and padding loop reach serialization with
the two compression folds of the input snapshot. -/
theorem hash_phases_loaded (base : Val) (s : Cpu) (n k : Nat) (live : s.ms = none) (pc : s.rip = base+0x15c)
    (loaded : ImageLoaded base s.mem) (sites : CycleSites base) (exitPC : canonical (base+0x307) = true)
    (constants : s.regs.get .rdi = base+0x390) (phase0 : phase s = 0)
    (counts : (blocksLeft s).toNat = n) (pad : (paddingCount s).toNat = k) (padBound : k ≤ 2)
    (sep : ∀ j, j < image.size → 440 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (src : ∀ t, t < n → ∀ (i : Fin 16) (b : Fin 4), outsideCycle (s.regs.get .rsp)
      (s.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val)) :
    ∃ out, steps base (3975*(n+k)+13) s = some out ∧ HashPhasesResult base s out n k := by
  have short j (h : j < image.size) := Nat.le_trans (by decide : 432 ≤ 440) (sep j h)
  have away j (h : j < image.size) := outside_image _ _ (sep j h)
  obtain ⟨m, msgRun, msg⟩ := phase_loaded base sites s n live pc loaded constants counts short src
  have codeM : ImageLoaded base m.mem := fun j hj => (msg.frame _ (apart_cycle (away j hj))).trans (loaded j hj)
  have phaseM : phase m = 0 := (read_phase_slot _ _ _ _ _ 432 msg (by decide +kernel)).trans phase0
  obtain ⟨a, testA, al, am, ar, ap⟩ := phase_test base m msg.live codeM msg.pc exitPC
  rw [if_pos phaseM] at ap
  have stackA : a.regs.get .rsp = s.regs.get .rsp := (congrArg (fun r : Regs => r.get .rsp) ar).trans msg.stack
  obtain ⟨b, switch, sw⟩ := switch_loaded base a al ap (am ▸ codeM) sites.repeatTarget
    (by simpa only [stackA] using sep)
  have stackB := sw.stack.trans stackA
  have frame (p : Val) (hp : outsidePhases (s.regs.get .rsp) p) : b.mem.read p = s.mem.read p :=
    (sw.frame p (by rw [stackA]; exact hp.2)).trans
      ((congrArg (fun m : Mem => m.read p) am).trans (msg.frame p (apart_cycle hp)))
  have codeB : ImageLoaded base b.mem := fun j hj => (frame _ (away j hj)).trans (loaded j hj)
  have countA : paddingCount a = paddingCount s := by
    unfold paddingCount
    rw [ar, am]
    exact read_phase_slot _ _ _ _ _ 440 msg (by decide +kernel)
  have kB : b.regs.get .rdi = base+0x390 :=
    sw.constants.trans ((congrArg (fun r : Regs => r.get .rdi) ar).trans (msg.constants.trans constants))
  obtain ⟨q, padRun, padding⟩ := phase_snapshot base sites b s.mem k sw.live sw.pc codeB kB
    (by rw [sw.count, countA, pad]) (by simpa only [stackB] using short)
    (fun t ht i byte => by
      dsimp only
      rw [sw.ptr, stackA, stackB]
      have apart := pad_apart (s.regs.get .rsp) ⟨t,by omega⟩ i byte
      exact ⟨apart_cycle apart,frame _ apart⟩)
  have qFrame (p : Val) (hp : outsidePhases (s.regs.get .rsp) p) : q.mem.read p = s.mem.read p :=
    (padding.frame _ (by rw [stackB]; exact apart_cycle hp)).trans (frame _ hp)
  have codeQ : ImageLoaded base q.mem := fun j hj => (qFrame _ (away j hj)).trans (loaded j hj)
  have marker := (read_phase_slot _ _ _ _ _ 432 padding (by decide +kernel)).trans sw.phase
  have phaseQ : phase q ≠ 0 := by change phase q = 1 at marker; rw [marker]; decide
  obtain ⟨out, testB, ok, mem, regs, rip⟩ := phase_test base q padding.live codeQ padding.pc exitPC
  rw [if_neg phaseQ] at rip
  have hashA : hashWords (project a) = hashWords (project m) := by simp only [hashWords, project, ar, am]
  have hashQ : hashWords (project out) = hashWords (project q) := by simp only [hashWords, project, mem, regs]
  have hashB := (switch_hash _ _ _ sw).trans (hashA.trans msg.hash)
  have msgTrace := msg.observations
  have testATrace := steps_observe_fragment testA msg.pc (by decide +kernel)
  have switchTrace := steps_observe_fragment switch ap (by decide +kernel)
  have padTrace := padding.observations
  have testBTrace := steps_observe_fragment testB padding.pc (by decide +kernel)
  rw [constants] at msgTrace
  rw [msg.stack] at testATrace
  rw [stackA] at switchTrace
  rw [stackB,kB,sw.ptr,stackA] at padTrace
  rw [padding.stack,stackB] at testBTrace
  have observations : ObservedExecution base s
      (hashPhasesEvents base (s.regs.get .rsp) (s.regs.get .rbp) n k) out :=
    by simpa only [hashPhasesEvents, List.append_assoc] using msgTrace.append (testATrace.append (switchTrace.append (padTrace.append testBTrace)))
  refine ⟨out, ?_, ⟨ok, rip, (congrArg (fun r : Regs => r.get .rsp) regs).trans (padding.stack.trans stackB),
    fun p hp => (congrArg (fun m : Mem => m.read p) mem).trans (qFrame _ hp), ?_, observations⟩⟩
  · rw [show 3975*(n+k)+13 = (3975*n+2)+(2+(5+((3975*k+2)+2))) by omega]
    exact steps_append msgRun (steps_append testA (steps_append switch (steps_append padRun testB)))
  · rw [hashQ, padding.hash, sw.ptr, stackA, hashB]

end Crypto.X86_64
