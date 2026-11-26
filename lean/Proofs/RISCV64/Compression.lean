import Proofs.RISCV64.RoundLoop
import Proofs.RISCV64.FeedForward
import Proofs.RISCV64.LoadedExecution

namespace Crypto.RISCV64

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

open Crypto.ARM64.Imported (wordVector)
open SHS.Equiv.VecBridge (getElem_bang_eq_getElem)
open SHS.Equiv.SHA256.Foldl.Sequential (addH)

private theorem loadHash_frame (s : CPU) :
    let out := run loadHashBody s
    out.mem = s.mem ∧ out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧
      out.reg 15 = 0 ∧ out.pc = s.pc + 0x22 := by
  simp (config := { decide := true }) [run, loadHashBody, Instruction.step, BitVec.add_assoc]

private theorem constants_read (base : Addr) (s : CPU) (loaded : ImageLoaded base s.mem)
    (address : s.reg 10 = base + BitVec.ofNat 64 constantsOffset) (i : Fin 64) :
    s.mem.read32 (s.reg 10 + BitVec.ofNat 64 (4*i.val)) = SHS.SHA256.K[i.val]! := by
  rw [address, BitVec.add_assoc, ← BitVec.ofNat_add, loaded_word _ _ loaded]
  · have table := congrArg (fun v : Vector Word 64 => v[i.val]) image_constants.1
    rw [getElem_bang_eq_getElem _ _ i.isLt]
    simpa only [Vector.getElem_ofFn] using table
  · have size : image.size = 0x540 := by decide +kernel
    rw [size]
    change 0x420 + 4 * i.val + 4 ≤ 0x540
    have := i.isLt
    omega

private theorem feed_end (s : CPU) : (run feedForward s).pc = s.pc + 0x60 := by
  exact linear_end_pc feedForward s (by decide)

attribute [local irreducible] run roundCode storedHash SHS.SHA256.compress SHS.SHA256.schedule

/-- FIPS compression from the fetched hash load, 64 rounds and feed-forward.
At this cutpoint the schedule is in the stack workspace. The bytes of K
come from the linked image identified by a0. -/
theorem compression_loaded (base : Addr) (s : CPU) (M : Vector Word 16)
    (pc : s.pc = base + 0x1ae) (loaded : ImageLoaded base s.mem)
    (address : s.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (schedule : wordVector 64 s.mem (s.reg 2) = SHS.SHA256.schedule M) :
    ∃ startRounds endRounds out,
      ImageExecution base s loadHashBody startRounds ∧
      ImageExecution base startRounds (roundCode 64) endRounds ∧
      ImageExecution base endRounds feedForward out ∧ out.pc = base + 0x2ee ∧
      storedHash out = SHS.SHA256.compress (storedHash s) M ∧ out.reg 2 = s.reg 2 ∧
      (∀ p, 288 ≤ (p - s.reg 2).toNat → out.mem.cells p = s.mem.cells p) := by
  let pre := run loadHashBody s
  obtain ⟨ram, sp, k, zero, pos⟩ := loadHash_frame s
  have prePC : pre.pc = base + 0x1d0 := by
    change (run loadHashBody s).pc = _
    rw [pos, pc, BitVec.add_assoc]; rfl
  have kh (i : Fin 64) :
      pre.mem.read32 (pre.reg 10 + BitVec.ofNat 64 (4*i.val)) = SHS.SHA256.K[i.val]! :=
    constants_read base pre (by change ImageLoaded base (run loadHashBody s).mem; rwa [ram])
      (k.trans address) i
  have wh (i : Fin 64) :
      pre.mem.read32 (pre.reg 2 + BitVec.ofNat 64 (4*i.val)) = (SHS.SHA256.schedule M)[i.val]! := by
    change (run loadHashBody s).mem.read32 ((run loadHashBody s).reg 2 + _) = _
    rw [ram, sp, getElem_bang_eq_getElem _ _ i.isLt, ← schedule]
    simp only [wordVector, Vector.getElem_ofFn]
  obtain ⟨post, rounds, atFeed, stack, _, same, compressed⟩ :=
    rounds_compress base pre M prePC zero kh wh
  have prePath := ImageExecution.linear_run base s loadHashBody 0x1ae pc
    (by decide) loadHashBody_decoded (by decide)
  have postPath := ImageExecution.linear_run base post feedForward 0x28e atFeed
    (by decide) feedForward_decoded (by decide)
  have hash : storedHash post = storedHash s := by
    unfold storedHash
    exact congrArg₂ (fun m sp => wordVector 8 m (sp + 256)) (same.trans ram) (stack.trans sp)
  have work : working pre = storedHash s := load_hash_value s
  have spFinal : post.reg 2 = s.reg 2 := stack.trans sp
  have memFinal : post.mem = s.mem := same.trans ram
  refine ⟨pre, post, run feedForward post, prePath, rounds, postPath, ?_, ?_, ?_, ?_⟩
  · rw [feed_end, atFeed, BitVec.add_assoc]; rfl
  · calc
      storedHash (run feedForward post) = addH (storedHash post) (working post) :=
        feed_forward_value post
      _ = addH (working pre) (working post) :=
        congrArg (fun iv => addH iv (working post)) (hash.trans work.symm)
      _ = SHS.SHA256.compress (working pre) M := compressed
      _ = SHS.SHA256.compress (storedHash s) M := congrArg (SHS.SHA256.compress · M) work
  · have outside : 288 ≤ ((post.reg 2 + 288) - post.reg 2).toNat := by
      rw [BitVec.add_comm _ (288 : Addr), BitVec.add_sub_cancel]
      decide
    exact (feed_forward_frame post _ outside).1.trans spFinal
  · intro p outside
    exact (feed_forward_frame post p (by rw [spFinal]; exact outside)).2.trans
      (congrArg (fun m : Memory => m.cells p) memFinal)

end Crypto.RISCV64
