import Proofs.X86_64.Body
import Proofs.ARM64.ImportedCallerEntry

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (caller_region_contains_offset caller_outside_delta)

def frameBase (s : Cpu) := s.regs.get .rsp-504
def inputRegion (s : Cpu) (extent : Nat) : Region := ⟨s.regs.get .rdi,extent⟩
def outputRegion (s : Cpu) : Region := ⟨s.regs.get .rsi,32⟩
def stackRegion (s : Cpu) : Region := ⟨frameBase s,512⟩
def imageRegion (base : Val) : Region := ⟨base,image.size⟩

/-- Serial callable entry for the baseline System V register convention.
The extent is independent of the ByteList's three header words. -/
structure CallerEntry (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (extent : Nat) : Prop where
  live : s.ms = none
  pc : s.rip = base
  loaded : ImageLoaded base s.mem
  layout : message.WellFormed
  size64 : message.size < 2^64
  accessible : message.size ≤ extent
  bound : message.bytes.size < 2^61
  stackAligned : (s.regs.get .rsp).toNat % 16 = 8
  inputAligned : (s.regs.get .rdi).toNat % 8 = 0
  inputValid : (inputRegion s extent).Valid
  outputValid : (outputRegion s).Valid
  stackValid : (stackRegion s).Valid
  imageValid : (imageRegion base).Valid
  inputStack : (inputRegion s extent).Disjoint (stackRegion s)
  imageStack : (imageRegion base).Disjoint (stackRegion s)
  stackOutput : (stackRegion s).Disjoint (outputRegion s)
  imageOutput : (imageRegion base).Disjoint (outputRegion s)
  inputOutput : (inputRegion s extent).Disjoint (outputRegion s)
  imageCanonical : ∀ p, (imageRegion base).Contains p → canonical p = true
  returnCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true
  sizeWord : s.mem.readSize .q (s.regs.get .rdi) = BitVec.ofNat 64 message.size
  offsetWord : headerOffset s = BitVec.ofNat 64 message.offset
  countWord : (headerLength s).toNat = message.bytes.size
  bytes : ∀ i : Fin message.bytes.size, s.mem.read (s.regs.get .rdi+BitVec.ofNat 64 (message.offset+i.val)) =
    (message.bytes.get! i.val).toBitVec

structure CallResult (s out : Cpu) (message : Crypto.Reference.ByteList) : Prop where
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  stack : out.regs.get .rsp = s.regs.get .rsp+8
  status : out.regs.get .rax = BitVec.ofNat 64 (Crypto.Reference.sha256 message).1
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  digest : Crypto.ARM64.Imported.memoryBytes32 (byteView out.mem) (s.regs.get .rsi) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  frame : PreservedOutside s.mem.read out.mem.read (outputRegion s) (stackRegion s)

def callSteps (size : Nat) := 11+bodySteps size

attribute [local irreducible] steps image

def callEvents (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) : List Event :=
  entryEvents base (s.regs.get .rsp) ++ headerEvents base (frameBase s) (s.regs.get .rdi) ++
    bodyEvents base (frameBase s) (s.regs.get .rdi+BitVec.ofNat 64 message.offset)
      (s.regs.get .rsi) message.bytes

/-- Starting at the symbol with the caller's actual registers and memory,
the loaded image returns the reference digest and status in an exact number
of instructions. The frame accounts for both the digest and private stack. -/
theorem sha256_observed (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out, returnAt base (callSteps message.bytes.size) s = some out ∧ CallResult s out message ∧
      ObservedExecution base s (callEvents base s message) out := by
  have codeSep j (hj : j < image.size) : 512 ≤ (base+BitVec.ofNat 64 j-frameBase s).toNat := by
    apply caller_outside_delta (stackRegion s) entry.stackValid
    intro h
    exact entry.imageStack _ ⟨caller_region_contains_offset _ entry.imageValid j hj,h⟩
  have inputSep j (hj : j < extent) : 512 ≤ (s.regs.get .rdi+BitVec.ofNat 64 j-frameBase s).toNat := by
    apply caller_outside_delta (stackRegion s) entry.stackValid
    intro h
    exact entry.inputStack _ ⟨caller_region_contains_offset _ entry.inputValid j hj,h⟩
  have stackDst j (hj : j < 512) : 32 ≤ (frameBase s+BitVec.ofNat 64 j-s.regs.get .rsi).toNat := by
    apply caller_outside_delta (outputRegion s) entry.outputValid
    intro h
    exact entry.stackOutput _ ⟨caller_region_contains_offset _ entry.stackValid j hj,h⟩
  have imageDst j (hj : j < image.size) : 32 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsi).toNat := by
    apply caller_outside_delta (outputRegion s) entry.outputValid
    intro h
    exact entry.imageOutput _ ⟨caller_region_contains_offset _ entry.imageValid j hj,h⟩
  have imageSize : image.size = 1200 := by decide +kernel
  have canonicalAt (j : Nat) (hj : j < 1200) : canonical (base+BitVec.ofNat 64 j) = true :=
    entry.imageCanonical _ (caller_region_contains_offset _ entry.imageValid j (by change j < image.size; omega))
  have sites : CallSites base := ⟨⟨canonicalAt _ (by decide),canonicalAt _ (by decide),canonicalAt _ (by decide),
      canonicalAt _ (by decide),canonicalAt _ (by decide)⟩,⟨canonicalAt _ (by decide),canonicalAt _ (by decide)⟩,
      canonicalAt _ (by decide),canonicalAt _ (by decide)⟩
  have entrySP : frameBase s+504 = s.regs.get .rsp := BitVec.sub_add_cancel _ _
  have saves : s.regs.get .rsp-48 = frameBase s+456 := by simp [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have far (p : Val) (h : 512 ≤ (p-frameBase s).toNat) : 48 ≤ (p-(s.regs.get .rsp-48)).toNat := by
    rw [saves]; exact Crypto.ARM64.Imported.region_store_delta _ _ 456 512 48 (by decide) h
  obtain ⟨a,pushes,pro⟩ := entry_loaded base s entry.live entry.pc entry.loaded (fun j hj => far _ (codeSep j hj))
  have spA : a.regs.get .rsp = frameBase s := pro.stack
  have rdi := pro.regs .rdi (by decide)
  have rsi := pro.regs .rsi (by decide)
  have aFrame (p : Val) (h : 512 ≤ (p-frameBase s).toNat) := pro.frame p (far p h)
  have codeA : ImageLoaded base a.mem := fun j hj => (aFrame _ (codeSep j hj)).trans (entry.loaded j hj)
  obtain ⟨lo,_,off,bytesFit⟩ := entry.layout
  have headerFit : 24 ≤ extent := Nat.le_trans lo (Nat.le_trans off entry.accessible)
  have field (d : Nat) (fits : d+8 ≤ extent) : a.mem.readSize .q (a.regs.get .rdi+BitVec.ofNat 64 d) =
      s.mem.readSize .q (s.regs.get .rdi+BitVec.ofNat 64 d) := by
    rw [rdi]
    apply Mem.readN_congr _ _ _ 8
    intro k hk
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact aFrame _ (inputSep _ (by omega))
  have hdr := header_loaded base a pro.live pro.pc codeA
    (fun j hj => by rw [spA]; exact Nat.le_trans (by decide : 424 ≤ 512) (codeSep j hj))
    (fun j => by rw [rdi,spA]; exact Crypto.ARM64.Imported.region_store_delta _ _ 416 512 8 (by decide) (inputSep _ (by have := j.isLt; omega)))
  obtain ⟨b,header,head⟩ := hdr
  have spB := head.stack.trans spA
  have hdrOffset : headerOffset a = BitVec.ofNat 64 message.offset :=
    (field 8 (by omega)).trans entry.offsetWord
  have addr : b.regs.get .rbp = s.regs.get .rdi+BitVec.ofNat 64 message.offset := head.payload.trans (by rw [rdi,hdrOffset])
  have len : (b.regs.get .rcx).toNat = message.bytes.size :=
    (congrArg BitVec.toNat (head.count.trans (field 16 (by omega)))).trans entry.countWord
  have bMem : b.mem = a.mem.writeSize .q (frameBase s+416) (s.regs.get .rsi) := by simpa only [spA,rsi] using head.mem
  have dst : digestPtr b = s.regs.get .rsi := by rw [digestPtr,spB,bMem,read64_write64]
  have before (p : Val) (h : 512 ≤ (p-frameBase s).toNat) : b.mem.read p = s.mem.read p :=
    (congrArg (fun m : Mem => m.read p) bMem).trans
      ((counter_frame _ _ _ _ (Crypto.ARM64.Imported.region_store_delta _ _ 416 512 8 (by decide) h)).trans (aFrame _ h))
  have reads (d : Nat) (hd : ∀ k : Fin 8, 8 ≤ (BitVec.ofNat 64 d+BitVec.ofNat 64 k.val-416).toNat) :
      b.mem.readSize .q (b.regs.get .rsp+BitVec.ofNat 64 d) = a.mem.readSize .q (frameBase s+BitVec.ofNat 64 d) := by
    rw [bMem,spB]; exact stack_read_other _ _ _ _ _ hd
  have ret : b.mem.readSize .q (b.regs.get .rsp+504) = s.mem.readSize .q (s.regs.get .rsp) := by
    apply Eq.trans (reads 504 (by decide +kernel))
    rw [← entrySP]
    apply Mem.readN_congr _ _ _ 8
    intro k hk
    apply pro.frame
    rw [saves,BitVec.add_assoc,stack_delta]
    exact (by decide +kernel : ∀ k : Fin 8, 48 ≤ (504+BitVec.ofNat 64 k.val-456).toNat) ⟨k,hk⟩
  have source (i : Fin message.bytes.size) : 512 ≤ (b.regs.get .rbp+BitVec.ofNat 64 i.val-frameBase s).toNat := by
    rw [addr,BitVec.add_assoc,← BitVec.ofNat_add]
    apply inputSep
    have := i.isLt
    have := entry.accessible
    omega
  obtain ⟨out,body,done,observed⟩ := body_return base b message head.live head.pc (fun j hj => (before _ (codeSep j hj)).trans (entry.loaded j hj)) sites
    ((congrArg canonical ret).trans entry.returnCanonical) len entry.bound
    (by simpa only [spB] using codeSep) (by simpa only [spB] using source)
    (fun i => (before _ (source i)).trans (by rw [addr,BitVec.add_assoc,← BitVec.ofNat_add]; exact entry.bytes i))
    (by simpa only [dst] using imageDst) (by simpa only [spB,dst] using stackDst)
  have slots : ∀ (i : Fin 6) (b : Fin 8), 8 ≤
    (BitVec.ofNat 64 (496-8*i.val)+BitVec.ofNat 64 b.val-416).toNat := by decide +kernel
  have observeHeader := head.observations
  rw [spA,rdi] at observeHeader
  rw [addr,spB,dst] at observed
  have observeCall := pro.observations.append (observeHeader.append observed)
  refine ⟨out, ?_, ⟨done.live,done.pc.trans ret,done.stack.trans ?_,done.status,?_,by simpa only [dst] using done.bytes,?_⟩, by simpa only [callEvents,List.append_assoc] using observeCall⟩
  · exact return_append (steps_append pushes header) body
  · rw [spB,← entrySP,BitVec.add_assoc]; rfl
  · intro i
    apply Eq.trans (done.saved i)
    apply Eq.trans (reads _ (slots i))
    have index : 496-8*i.val = 456+(40-8*i.val) := by have := i.isLt; omega
    simpa only [saves,index,BitVec.ofNat_add,BitVec.add_assoc] using pro.saved i
  · intro p hd hs
    have outside := caller_outside_delta _ entry.stackValid p hs
    exact (done.frame p (by rw [spB]; exact outside) (by rw [dst]; exact caller_outside_delta _ entry.outputValid _ hd)).trans
      (before p outside)

/-- Functional and ABI consequences of the exact fetched serial execution. -/
theorem sha256_serial (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out, returnAt base (callSteps message.bytes.size) s = some out ∧ CallResult s out message := by
  obtain ⟨out, steps, result, _⟩ := sha256_observed base s message extent entry
  exact ⟨out,steps,result⟩

end Crypto.X86_64
