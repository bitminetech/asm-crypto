import Proofs.X86_64.Preparation
import Proofs.X86_64.PreparedCall

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (paddingBlockCount)

structure CallSites (base : Val) : Prop where
  loops : CycleSites base
  copy : CopySites base
  padding : canonical (base+0xf8) = true
  digest : canonical (base+0x307) = true

def bodySteps (size : Nat) := 95+6*(size%64)+optionalMove (size%64)+3975*(size/64+(if size%64 < 56 then 1 else 2))

private abbrev keptOffset (x : Val) := 288 ≤ x.toNat ∧ 128 ≤ (x-288).toNat ∧
    8 ≤ (x-424).toNat ∧ 8 ≤ (x-432).toNat ∧ 8 ≤ (x-440).toNat

private theorem fixed_read (base : Val) (s out : Cpu) (data : ByteArray) (post : PreparedState base s out data)
    (d : Nat) (h : ∀ i : Fin 8, keptOffset (BitVec.ofNat 64 d+BitVec.ofNat 64 i.val)) :
    out.mem.readSize .q (out.regs.get .rsp+BitVec.ofNat 64 d) =
      s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) := by
  rw [post.stack]
  apply Mem.readN_congr _ _ _ 8
  intro i hi
  apply post.frame
  unfold prepKept
  rw [BitVec.add_assoc,BitVec.add_comm (s.regs.get .rsp),BitVec.add_sub_cancel,
    BitVec.add_comm _ (s.regs.get .rsp)]
  simpa only [stack_delta] using h ⟨i,hi⟩

def bodyEvents (base sp src dst : Val) (data : ByteArray) : List Event :=
  prepareEvents base sp src data.size ++ preparedCallEvents base sp src dst data

structure BodyResult (s out : Cpu) (message : Crypto.Reference.ByteList) : Prop where
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp+504)
  stack : out.regs.get .rsp = s.regs.get .rsp+512
  status : out.regs.get .rax = BitVec.ofNat 64 (Crypto.Reference.sha256 message).1
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) =
    s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 (496-8*i.val))
  bytes : Crypto.ARM64.Imported.memoryBytes32 (byteView out.mem) (digestPtr s) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  frame : ∀ p, 512 ≤ (p-s.regs.get .rsp).toNat → 32 ≤ (p-digestPtr s).toNat → out.mem.read p = s.mem.read p

attribute [local irreducible] steps image

theorem body_return (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (live : s.ms = none)
    (pc : s.rip = base+0x25) (loaded : ImageLoaded base s.mem) (sites : CallSites base)
    (target : canonical (s.mem.readSize .q (s.regs.get .rsp+504)) = true)
    (size : (s.regs.get .rcx).toNat = message.bytes.size) (bound : message.bytes.size < 2^61)
    (codeSep : ∀ j, j < image.size → 512 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (inputSep : ∀ i : Fin message.bytes.size, 512 ≤ (s.regs.get .rbp+BitVec.ofNat 64 i.val-s.regs.get .rsp).toNat)
    (input : ∀ i : Fin message.bytes.size, s.mem.read (s.regs.get .rbp+BitVec.ofNat 64 i.val) = (message.bytes.get! i.val).toBitVec)
    (imageDst : ∀ j, j < image.size → 32 ≤ (base+BitVec.ofNat 64 j-digestPtr s).toNat)
    (stackDst : ∀ j, j < 512 → 32 ≤ (s.regs.get .rsp+BitVec.ofNat 64 j-digestPtr s).toNat) :
    ∃ out, returnAt base (bodySteps message.bytes.size) s = some out ∧ BodyResult s out message ∧
      ObservedExecution base s (bodyEvents base (s.regs.get .rsp) (s.regs.get .rbp) (digestPtr s) message.bytes) out := by
  obtain ⟨a,prep,ready⟩ := preparation_loaded base s message.bytes live pc loaded sites.copy sites.padding size codeSep inputSep input
  have far (p : Val) (h : 512 ≤ (p-s.regs.get .rsp).toNat) := prepKept_of_outside _ _ h
  have code : ImageLoaded base a.mem := fun j hj => (ready.frame _ (far _ (codeSep j hj))).trans (loaded j hj)
  have ret := fixed_read base s a _ ready 504 (by decide +kernel)
  have dst : digestPtr a = digestPtr s := fixed_read base s a _ ready 416 (by decide +kernel)
  have padBound := (Crypto.ARM64.Imported.paddingBlockCount_bounds message.bytes).2
  have msgCount : (blocksLeft a).toNat = message.bytes.size/64 := by
    rw [ready.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have pads : (paddingCount a).toNat = paddingBlockCount message.bytes := by
    rw [ready.pads,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have src t (ht : t < message.bytes.size/64) (i : Fin 16) (b : Fin 4) :
      outsideCycle (a.regs.get .rsp) (a.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val) := by
    let j := 64*t+4*i.val+b.val
    have hj : j < message.bytes.size := by dsimp [j]; have := i.isLt; have := b.isLt; omega
    have eq : a.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val =
      s.regs.get .rbp+BitVec.ofNat 64 j := by simp [j,ready.ptr,BitVec.ofNat_add,BitVec.add_assoc]
    rw [eq,ready.stack]
    exact ⟨Nat.le_trans (by decide : 288 ≤ 512) (inputSep ⟨j,hj⟩),
      Crypto.ARM64.Imported.region_store_delta _ _ 424 512 8 (by decide) (inputSep ⟨j,hj⟩)⟩
  obtain ⟨out,run,post,observed⟩ := prepared_return base a message ready.live ready.pc code sites.loops sites.digest
    ((congrArg canonical ret).trans target) ready.constants ready.phase msgCount pads ready.hash bound
    (fun j hj => by rw [ready.stack]; exact Nat.le_trans (by decide : 440 ≤ 512) (codeSep j hj)) src
    (by simpa only [dst] using imageDst) (by simpa only [ready.stack,dst] using stackDst)
    (fun i => by rw [ready.ptr]; exact (ready.frame _ (far _ (inputSep i))).trans (input i))
    (by simpa only [ready.stack,padBase] using ready.padding)
  have cells : ∀ (i : Fin 6) (b : Fin 8), keptOffset (BitVec.ofNat 64 (496-8*i.val)+BitVec.ofNat 64 b.val) := by decide +kernel
  rw [ready.stack,ready.ptr,dst] at observed
  have observedBody := ready.observations.append observed
  refine ⟨out, ?_, ⟨post.live,post.pc.trans ret,post.stack.trans (by rw [ready.stack]),post.status,
    fun i => (post.saved i).trans (fixed_read _ _ _ _ ready _ (cells i)),by simpa only [dst] using post.bytes,?_⟩,observedBody⟩
  · have eq : bodySteps message.bytes.size = (48+6*(message.bytes.size%64)+optionalMove (message.bytes.size%64))+
        (3975*(message.bytes.size/64+paddingBlockCount message.bytes)+47) := by
      unfold bodySteps paddingBlockCount
      omega
    rw [eq]
    exact return_append prep run
  · intro p outside outDst
    have keep := far p outside
    exact (post.frame p (by rw [ready.stack]; exact ⟨keep.1,Crypto.ARM64.Imported.region_store_delta _ _ 424 512 16 (by decide) outside⟩)
      (by rw [dst]; exact outDst)).trans (ready.frame _ keep)

end Crypto.X86_64
