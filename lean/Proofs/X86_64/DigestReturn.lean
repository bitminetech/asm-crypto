import Proofs.X86_64.Digest
import Proofs.X86_64.Entry
import Proofs.X86_64.Return

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (memoryBytes32 digestBytes)

private theorem read_saved (s out : Cpu) (r : ReturnState s out) (i : Fin 6) :
    out.regs.get (savedReg i) = s.mem.readSize .q
      (s.regs.get .rsp + BitVec.ofNat 64 (496-8*i.val)) := by
  obtain ⟨i,hi⟩ := i
  interval_cases i <;> first | exact r.rbx | exact r.rbp | exact r.r12 | exact r.r13 | exact r.r14 | exact r.r15

def digestReturnEvents (base sp dst : Val) :=
  digestEvents base sp dst ++ returnEvents base sp

structure DigestReturnState (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp+504)
  stack : out.regs.get .rsp = s.regs.get .rsp+512
  status : out.regs.get .rax = 0
  calleeSaved : ∀ i : Fin 6, out.regs.get (savedReg i) =
    s.mem.readSize .q (s.regs.get .rsp + BitVec.ofNat 64 (496-8*i.val))
  bytes : memoryBytes32 (byteView out.mem) (digestPtr s) = digestBytes (hashWords (project s))
  frame : ∀ p, 32 ≤ (p-digestPtr s).toNat → out.mem.read p = s.mem.read p

/-- Serialize and return in 34 fetched instructions. The separation premises
cover the image and the hash, saved-register and return-address reads. -/
theorem digest_return_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x307)
    (loaded : ImageLoaded base s.mem) (target : canonical (s.mem.readSize .q (s.regs.get .rsp+504)) = true)
    (imageSep : ∀ j, j < image.size → 32 ≤ (base+BitVec.ofNat 64 j-digestPtr s).toNat)
    (stackSep : ∀ j, j < 512 → 32 ≤ (s.regs.get .rsp+BitVec.ofNat 64 j-digestPtr s).toNat) :
    ∃ out, returnAt base 34 s = some out ∧ DigestReturnState s out ∧
      ObservedExecution base s (digestReturnEvents base (s.regs.get .rsp) (digestPtr s)) out := by
  obtain ⟨mid, write, ok, next, rsp, frame, bytes, observedWrite⟩ := digest_loaded base s live pc loaded imageSep
    (fun i b => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      apply stackSep
      have := i.isLt
      have := b.isLt
      omega)
  have read (j : Nat) (bound : j+8 ≤ 512) :
      mid.mem.readSize .q (mid.regs.get .rsp+BitVec.ofNat 64 j) =
      s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 j) := by
    rw [rsp]
    apply Mem.readN_congr _ _ _ 8
    intro b hb
    apply frame
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stackSep (j+b) (by omega)
  have ret := read 504 (by decide)
  obtain ⟨out, pop, post, observedPop⟩ := return_loaded base mid ok
    (fun j hj => (frame _ (imageSep j hj)).trans (loaded j hj)) next ((congrArg canonical ret).trans target)
  rw [rsp] at observedPop
  exact ⟨out, return_append write pop, ⟨post.live, post.pc.trans ret,
    post.stack.trans (by rw [rsp]), post.status, fun i => (read_saved mid out post i).trans
      (read _ (by have := i.isLt; omega)), by rw [post.mem]; exact bytes,
    fun p hp => (congrArg (fun m : Mem => m.read p) post.mem).trans (frame p hp)⟩, observedWrite.append observedPop⟩

end Crypto.X86_64
