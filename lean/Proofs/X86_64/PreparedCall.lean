import Proofs.X86_64.DigestReturn
import Proofs.X86_64.HashPhases
import Proofs.X86_64.PhaseReference
import Reference.SHA256

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (paddingBlockCount digestBytes memoryBytes32)
open Crypto.Reference.ByteLayout

private theorem read_fixed_slot (base : Val) (s out : Cpu) (n k d : Nat) (post : HashPhasesResult base s out n k)
    (outside : ∀ b : Fin 8, 288 ≤ (BitVec.ofNat 64 d+BitVec.ofNat 64 b.val).toNat ∧
      16 ≤ ((BitVec.ofNat 64 d+BitVec.ofNat 64 b.val)-424).toNat) :
    out.mem.readSize .q (out.regs.get .rsp+BitVec.ofNat 64 d) =
      s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) := by
  rw [post.stack]
  apply Mem.readN_congr _ _ _ 8
  intro b hb
  apply post.frame
  unfold outsidePhases
  rw [BitVec.add_assoc, BitVec.add_comm (s.regs.get .rsp), BitVec.add_sub_cancel,
    BitVec.add_comm _ (s.regs.get .rsp), stack_delta]
  exact outside ⟨b,hb⟩

def preparedCallEvents (base sp src dst : Val) (data : ByteArray) : List Event :=
  hashPhasesEvents base sp src (data.size/64) (paddingBlockCount data) ++ digestReturnEvents base sp dst

structure DigestResult (s out : Cpu) (message : Crypto.Reference.ByteList) : Prop where
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp+504)
  stack : out.regs.get .rsp = s.regs.get .rsp+512
  status : out.regs.get .rax = BitVec.ofNat 64 (Crypto.Reference.sha256 message).1
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) =
    s.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 (496-8*i.val))
  bytes : memoryBytes32 (byteView out.mem) (digestPtr s) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  frame : ∀ p, outsidePhases (s.regs.get .rsp) p → 32 ≤ (p-digestPtr s).toNat → out.mem.read p = s.mem.read p

attribute [local irreducible] steps hashWords foldBlocks Crypto.Reference.digest

/-- Both block phases through the first RET. The premises identify the IV,
the two public counts, the original payload and the prepared padding bytes. -/
theorem prepared_return (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList)
    (live : s.ms = none) (pc : s.rip = base+0x15c) (loaded : ImageLoaded base s.mem)
    (sites : CycleSites base) (exitPC : canonical (base+0x307) = true)
    (target : canonical (s.mem.readSize .q (s.regs.get .rsp+504)) = true)
    (constants : s.regs.get .rdi = base+0x390) (phase0 : phase s = 0)
    (count : (blocksLeft s).toNat = message.bytes.size/64)
    (pads : (paddingCount s).toNat = paddingBlockCount message.bytes)
    (initial : hashWords (project s) = Crypto.Reference.WordModel.H0_256) (bound : message.bytes.size < 2^61)
    (imageStack : ∀ j, j < image.size → 440 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (src : ∀ t, t < message.bytes.size/64 → ∀ (i : Fin 16) (b : Fin 4), outsideCycle (s.regs.get .rsp)
      (s.regs.get .rbp+BitVec.ofNat 64 (64*t)+BitVec.ofNat 64 (4*i.val)+BitVec.ofNat 64 b.val))
    (imageDst : ∀ j, j < image.size → 32 ≤ (base+BitVec.ofNat 64 j-digestPtr s).toNat)
    (stackDst : ∀ j, j < 512 → 32 ≤ (s.regs.get .rsp+BitVec.ofNat 64 j-digestPtr s).toNat)
    (source : ∀ i : Fin message.bytes.size, s.mem.read (s.regs.get .rbp+BitVec.ofNat 64 i.val) = (message.bytes.get! i.val).toBitVec)
    (padding : ∀ i : Fin (64*paddingBlockCount message.bytes), s.mem.read (s.regs.get .rsp+288+BitVec.ofNat 64 i.val) =
      ((implPaddedBytes message.bytes).get! (message.bytes.size/64*64+i.val)).toBitVec) :
    ∃ out, returnAt base (3975*(message.bytes.size/64+paddingBlockCount message.bytes)+47) s = some out ∧
      DigestResult s out message ∧
      ObservedExecution base s (preparedCallEvents base (s.regs.get .rsp) (s.regs.get .rbp) (digestPtr s) message.bytes) out := by
  obtain ⟨hashed, run, post⟩ := hash_phases_loaded base s _ _ live pc loaded sites exitPC constants phase0
    count pads (Crypto.ARM64.Imported.paddingBlockCount_bounds _).2 imageStack src
  have dst : digestPtr hashed = digestPtr s := read_fixed_slot _ _ _ _ _ 416 post (by decide +kernel)
  have ret := read_fixed_slot _ _ _ _ _ 504 post (by decide +kernel)
  have code : ImageLoaded base hashed.mem := fun j hj =>
    (post.frame _ ⟨Nat.le_trans (by decide : 288 ≤ 440) (imageStack j hj),
      Crypto.ARM64.Imported.region_store_delta _ _ 424 440 16 (by decide) (imageStack j hj)⟩).trans (loaded j hj)
  obtain ⟨out, finish, result, observeFinish⟩ := digest_return_loaded base hashed post.live post.pc code
    ((congrArg canonical ret).trans target) (by simpa only [dst] using imageDst)
    (by simpa only [post.stack,dst] using stackDst)
  have cells : ∀ (i : Fin 6) (b : Fin 8),
      288 ≤ (BitVec.ofNat 64 (496-8*i.val)+BitVec.ofNat 64 b.val).toNat ∧
      16 ≤ ((BitVec.ofNat 64 (496-8*i.val)+BitVec.ofNat 64 b.val)-424).toNat := by decide +kernel
  rw [post.stack,dst] at observeFinish
  have observe := post.observations.append observeFinish
  refine ⟨out, by simpa only [Nat.add_assoc] using return_append run finish, ⟨result.live, result.pc.trans ret, result.stack.trans (by rw [post.stack]),
    result.status, fun i => (result.calleeSaved i).trans (read_fixed_slot _ _ _ _ _ _ post (cells i)), ?_, ?_⟩, observe⟩
  · rw [← dst,result.bytes,post.hash,initial]
    exact folds_reference message.bytes bound s.mem s.mem _ _ source padding
  · intro p hp hd
    exact (result.frame p (by simpa only [dst] using hd)).trans (post.frame p hp)

end Crypto.X86_64
