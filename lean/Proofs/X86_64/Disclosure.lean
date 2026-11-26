import Proofs.X86_64.Caller
import Proofs.ARM64.ImportedDisclosure

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (disclosure_region_offset disclosure_memoryBytes32_point)

/-- Only the used payload and the call's private stack may retain secret bytes.
Caller-clobbered registers are private and the digest is the permitted release. -/
def publicByte (s : Cpu) (msg : Crypto.Reference.ByteList) (p : Val) : Prop :=
  ¬(Region.mk (s.regs.get .rdi + BitVec.ofNat 64 msg.offset) msg.bytes.size).Contains p ∧
    ¬(stackRegion s).Contains p

structure SameContext (left right : Cpu) (l r : Crypto.Reference.ByteList) : Prop where
  input : left.regs.get .rdi = right.regs.get .rdi
  output : left.regs.get .rsi = right.regs.get .rsi
  stack : left.regs.get .rsp = right.regs.get .rsp
  link : left.mem.readSize .q (left.regs.get .rsp) = right.mem.readSize .q (right.regs.get .rsp)
  offset : l.offset = r.offset
  count : l.bytes.size = r.bytes.size

structure ReturnedAgreement (left right a b : Cpu) (l r : Crypto.Reference.ByteList) : Prop where
  domain : ∀ p, publicByte left l p ↔ publicByte right r p
  pc : a.rip = b.rip
  stack : a.regs.get .rsp = b.regs.get .rsp
  status : a.regs.get .rax = b.regs.get .rax
  live : a.ms = b.ms
  bytes : ∀ p, publicByte left l p → a.mem.read p = b.mem.read p

/-- Vary the entire private input, the initial output and all stack locals.
With equal permitted digests, the returned byte observation agrees. -/
theorem sha256_disclosures {base left right l r le re}
    (leftEntry : CallerEntry base left l le) (rightEntry : CallerEntry base right r re)
    (ctx : SameContext left right l r)
    (publicMem : ∀ p, publicByte left l p → ¬(outputRegion left).Contains p →
      left.mem.read p = right.mem.read p)
    (release : (Crypto.Reference.sha256 l).2 = (Crypto.Reference.sha256 r).2) :
    ∃ a b, returnAt base (callSteps l.bytes.size) left = some a ∧
      returnAt base (callSteps r.bytes.size) right = some b ∧ ReturnedAgreement left right a b l r := by
  obtain ⟨a,la,ha⟩ := sha256_serial _ _ _ _ leftEntry
  obtain ⟨b,rb,hb⟩ := sha256_serial _ _ _ _ rightEntry
  have sp : stackRegion left = stackRegion right := by simp only [stackRegion, frameBase, ctx.stack]
  have dst : outputRegion left = outputRegion right := by simp only [outputRegion, ctx.output]
  refine ⟨a,b,la,rb,⟨fun p => ?_,ha.pc.trans (ctx.link.trans hb.pc.symm),?_,
    ha.status.trans hb.status.symm,ha.live.trans hb.live.symm,?_⟩⟩
  · simp only [publicByte, ctx.input, ctx.offset, ctx.count, sp]
  · rw [ha.stack, hb.stack, ctx.stack]
  · intro p observable
    by_cases inside : (outputRegion left).Contains p
    · obtain ⟨i,address⟩ := disclosure_region_offset _ _ inside
      have same := ha.digest.trans ((congrArg (Vector.map UInt8.toBitVec) release).trans hb.digest.symm)
      have point := disclosure_memoryBytes32_point _ _ _ _ same i
      rw [← ctx.output] at point
      rw [address]
      exact point
    · exact (ha.frame p inside observable.2).trans ((publicMem p observable inside).trans
        (hb.frame p (dst ▸ inside) (sp ▸ observable.2)).symm)

end Crypto.X86_64
