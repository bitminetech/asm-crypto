import Proofs.X86_64.InputWords
import Proofs.X86_64.Schedule
import Proofs.X86_64.Tables
import Proofs.X86_64.FeedForward
import Proofs.X86_64.FrameTrace
import Proofs.ARM64.ImportedCellFrame
import Proofs.ARM64.ImportedHashInitFrame

namespace Crypto.X86_64
open X86

private theorem hash_frame (s out : Cpu) (rsp : out.regs.get .rsp = s.regs.get .rsp)
    (frame : ∀ p, 256 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p) :
    hashWords (project out) = hashWords (project s) := by
  unfold hashWords project
  simp only [rsp]
  apply Crypto.ARM64.Imported.hash_snapshot_of_frame
  intro p hp
  simp only [byteView, Arm64.Memory.ofFn, frame p hp]

/-- One compression block's public observations in execution order. -/
def blockEvents (base sp ptr k : Val) : List Event :=
  WordLoop.input.prefix base sp ptr k 16 ++
  WordLoop.expansion.prefix base sp ptr k 48 ++
  frameFragment base sp 0x1c2 9 ++
  WordLoop.round.prefix base sp ptr k 64 ++
  frameFragment base sp 0x282 8

structure BlockResult (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base + 0x2c2
  stack : out.regs.get .rsp = s.regs.get .rsp
  constants : out.regs.get .rdi = s.regs.get .rdi
  blockPtr : out.regs.get .rbp = s.regs.get .rbp
  index : out.regs.get .rbx = 64
  frame : ∀ p, 288 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p
  hash : hashWords (project out) = Crypto.Reference.WordModel.compress (hashWords (project s)) (sourceBlock s)
  observations : ObservedExecution base s (blockEvents base (s.regs.get .rsp)
    (s.regs.get .rbp) (s.regs.get .rdi)) out

attribute [local irreducible] WordLoop.prefix frameFragment steps working hashWords Crypto.Reference.WordModel.compress Crypto.Reference.WordModel.schedule

set_option maxHeartbeats 1500000 in
/-- A block from memory, in big-endian byte order, is compressed into the
saved hash in the stack frame. The complete path includes input loads,
schedule generation, working-register initialization, rounds and feed-forward. -/
theorem block_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x16d)
    (idx : s.regs.get .rbx = 0) (loaded : ImageLoaded base s.mem)
    (constants : s.regs.get .rdi = base + 0x390)
    (sep : ∀ j, j < image.size → 288 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (src : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.regs.get .rbp + BitVec.ofNat 64 (4*i.val) + BitVec.ofNat 64 b.val - s.regs.get .rsp).toNat)
    (inputPC : canonical (base + 0x16d) = true) (expansionPC : canonical (base + 0x17f) = true)
    (roundPC : canonical (base + 0x204) = true) :
    ∃ out, steps base 3969 s = some out ∧ BlockResult base s out := by
  have apart j (hj : j < image.size) : 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat :=
    Nat.le_trans (by decide : 256 ≤ 288) (sep j hj)
  obtain ⟨copied, copy, cp⟩ := input_prefix base s live pc idx loaded apart src inputPC 16 (by decide)
  have codeC : ImageLoaded base copied.mem := fun j hj => (cp.frame _ (apart j hj)).trans (loaded j hj)
  let M := sourceBlock s
  have first (j : Nat) (hj : j < 16) : (stackWords copied)[j]! = M[j]! := by
    rw [cp.words _ hj]
    simp [M, sourceBlock, hj]
  obtain ⟨expanded, expand, ex, expansionTrace⟩ := schedule_loaded base copied M cp.live cp.pc cp.index codeC
    (by simpa only [cp.stack] using apart) expansionPC first
  have stackE := ex.stack.trans cp.stack
  have frame (p : Val) (hp : 256 ≤ (p-s.regs.get .rsp).toNat) : expanded.mem.read p = s.mem.read p :=
    (ex.frame _ (by rw [cp.stack]; exact hp)).trans (cp.frame _ hp)
  have codeE : ImageLoaded base expanded.mem := fun j hj => (frame _ (apart j hj)).trans (loaded j hj)
  obtain ⟨ready, init, liveR, pcR, hw, memR, idxR, spR, kR, bpR⟩ :=
    hash_loaded base expanded ex.live codeE ex.pc
  have codeR : ImageLoaded base ready.mem := memR ▸ codeE
  obtain ⟨mixed, rounds, mr, math⟩ := rounds_compress base ready M liveR pcR idxR codeR roundPC
    (kR.trans (ex.constants.trans (cp.constants.trans constants)))
    (by rw [memR, spR]; exact ex.words)
  have stackM := mr.stack.trans (spR.trans stackE)
  have memM := mr.mem.trans memR
  have baseM : hashBase mixed = s.regs.get .rsp + 256 := by rw [hashBase, stackM]
  have distance (p : Val) (hp : 288 ≤ (p-s.regs.get .rsp).toNat) : 32 ≤ (p-hashBase mixed).toNat := by
    rw [baseM]
    exact Crypto.ARM64.Imported.region_store_delta _ _ 256 288 32 (by decide) hp
  obtain ⟨out, feed, ff, result⟩ := feed_forward_loaded base mixed mr.live mr.pc
    (memM ▸ codeE) (fun j hj => distance _ (sep j hj))
  have H := hash_frame s expanded stackE frame
  have hashM : hashWords (project mixed) = hashWords (project s) := hash_frame _ _ stackM
    (fun p hp => (congrArg (fun m : Mem => m.read p) memM).trans (frame _ hp))
  have initial := hw.trans H
  rw [initial] at math
  rw [hashM] at result
  have pcInit : expanded.rip = base+0x1c2 := ex.pc
  have initTrace := steps_observe_fragment init pcInit (by decide +kernel)
  have feedTrace := steps_observe_fragment feed mr.pc (by decide +kernel)
  have roundTrace := mr.observations
  have indexSp := spR.trans stackE
  have indexP := bpR.trans (ex.blockPtr.trans cp.blockPtr)
  have indexK := kR.trans (ex.constants.trans cp.constants)
  rw [cp.stack, cp.blockPtr, cp.constants] at expansionTrace
  rw [stackE] at initTrace
  rw [indexSp,indexP,indexK] at roundTrace
  rw [stackM] at feedTrace
  have observed : ObservedExecution base s (blockEvents base (s.regs.get .rsp)
      (s.regs.get .rbp) (s.regs.get .rdi)) out := by
    unfold blockEvents
    simpa only [List.append_assoc] using cp.observations.append (expansionTrace.append (initTrace.append (roundTrace.append feedTrace)))
  exact ⟨out, steps_append copy (steps_append expand (steps_append init (steps_append rounds feed))),
    ⟨ff.live, ff.pc, (congrArg (fun r : Regs => r.get .rsp) ff.regs).trans stackM,
      (congrArg (fun r : Regs => r.get .rdi) ff.regs).trans
        (mr.constants.trans (kR.trans (ex.constants.trans cp.constants))),
      (congrArg (fun r : Regs => r.get .rbp) ff.regs).trans
        (mr.blockPtr.trans (bpR.trans (ex.blockPtr.trans cp.blockPtr))),
      (congrArg (fun r : Regs => r.get .rbx) ff.regs).trans mr.index,
      fun p hp => (ff.frame _ (distance p hp)).trans
        ((congrArg (fun m : Mem => m.read p) memM).trans (frame p (by omega))),
      result.trans math, observed⟩⟩

end Crypto.X86_64
