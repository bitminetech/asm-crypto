import Proofs.X86_64.FrameTrace
import Proofs.X86_64.InputWords
import Proofs.X86_64.FeedForward
import Proofs.ARM64.ImportedExit

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (wordVector reverseWord memoryBytes32 digestBytes)

def digestPC (n : Nat) := if n = 0 then 0x30f else 0x30e + 12*n
private def hashSlot (i : Fin 8) := BitVec.ofNat 64 (256 + 4*i.val)
private def readSwap (i : Fin 8) : WordBlock := [(.loadStack .rax (hashSlot i),7),(.bswap .rax,2)]
private def storeDigest (i : Fin 8) : Instr :=
  ⟨.mov .d (.mem {base := some .rsi, disp := BitVec.ofNat 64 (4*i.val)}) (.reg .rax),
    if i.val = 0 then 2 else 3⟩
private def getPtr : Instr := ⟨.mov .q (.reg .rsi) (.mem {base := some .rsp, disp := 416}),8⟩

private theorem ptr_decode : decodeAt image 0x307 = some getPtr := by decide +kernel
private theorem digest_table : ∀ i : Fin 8,
    decodeSeq (digestPC i.val) 2 = some (instructions (readSwap i)) ∧
    decodeAt image (digestPC i.val + 9) = some (storeDigest i) ∧
    digestPC i.val + 9 < codeEnd ∧ digestPC i.val + 9 + (storeDigest i).len ≤ codeEnd ∧
    digestPC i.val + 9 + (storeDigest i).len = digestPC (i.val+1) := by decide +kernel

private theorem ptr_step (s : Cpu) (live : s.ms = none) :
    X86.step getPtr s = {s with
      regs := s.regs.set .rsi (s.mem.readSize .q (s.regs.get .rsp+416)),
      rip := s.rip + 8} := by
  simp [getPtr, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.readMem, Cpu.setReg, Cpu.setRip, Value.writeView, Ea.addr, Ea.offset]

private theorem store_step (i : Fin 8) (s : Cpu) (live : s.ms = none) :
    X86.step (storeDigest i) s = {s with
      mem := s.mem.writeSize .d (s.regs.get .rsi + BitVec.ofNat 64 (4*i.val))
        (((s.regs.get .rax).setWidth 32).setWidth 64), rip := s.rip + BitVec.ofNat 64 (storeDigest i).len} := by
  simp [storeDigest, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.writeOperand, Cpu.writeMem, Cpu.getReg, Cpu.setRip, trunc32, Ea.addr, Ea.offset]

private theorem read_swap (s : DataState) (i : Fin 8) :
    let out := evalBlock (readSwap i) s
    out.word .rax = reverseWord ((hashWords s)[i.val]) ∧ out.mem = s.mem ∧
      out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rsi = s.regs.get .rsi := by
  simp (config := { decide := true }) [readSwap, evalBlock, WordInst.eval, DataState.put, DataState.word,
    Regs.get_set_ne, hashWords, wordVector, hashSlot, BitVec.ofNat_add, BitVec.add_assoc, byteView_read32,
    Arm64.Memory.read32, bswap_bytes, Crypto.ARM64.Imported.reverseWord_bytes]

def digestWordEvents (base sp dst : Val) (i : Fin 8) : List Event :=
  frameFragment base sp (digestPC i.val) 2 ++
    [(base+BitVec.ofNat 64 (digestPC i.val+9),storeDigest i,
      [⟨true,dst+BitVec.ofNat 64 (4*i.val),4⟩])]

def digestPrefixEvents (base sp dst : Val) : Nat → List Event
  | 0 => []
  | n+1 => digestPrefixEvents base sp dst n ++ if h : n < 8 then digestWordEvents base sp dst ⟨n,h⟩ else []

def digestEvents (base sp dst : Val) :=
  frameFragment base sp 0x307 1 ++ digestPrefixEvents base sp dst 8

attribute [local irreducible] steps image

private theorem digest_word (base : Val) (s : Cpu) (i : Fin 8) (live : s.ms = none)
    (pc : s.rip = base + BitVec.ofNat 64 (digestPC i.val)) (loaded : ImageLoaded base s.mem) :
    ∃ out, steps base 3 s = some out ∧ out.ms = none ∧ out.rip = base + BitVec.ofNat 64 (digestPC (i.val+1)) ∧
      out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rsi = s.regs.get .rsi ∧
      out.mem = s.mem.writeSize .d (s.regs.get .rsi + BitVec.ofNat 64 (4*i.val))
        ((reverseWord ((hashWords (project s))[i.val])).setWidth 64) ∧
      ObservedExecution base s (digestWordEvents base (s.regs.get .rsp) (s.regs.get .rsi) i) out := by
  obtain ⟨pair, store, start, stop, finish⟩ := digest_table i
  let mid := X86.run (instructions (readSwap i)) s
  have run : steps base 2 s = some mid := fetch_word_block (readSwap i) _ _ _ live loaded pc (by rfl) pair
  obtain ⟨proj, ok, rip⟩ := word_block (readSwap i) s live
  have facts := read_swap (project s) i
  rw [← proj] at facts
  obtain ⟨val, mem, sp, dst⟩ := facts
  change mid.mem = s.mem at mem
  change mid.rip = s.rip + 9 at rip
  have midPC : mid.rip = base + BitVec.ofNat 64 (digestPC i.val+9) := by rw [rip, pc, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have fetch := fetch_at _ mid _ _ (mem ▸ loaded) midPC store start stop
  have one : steps base 1 mid = some (X86.step (storeDigest i) mid) := by
    simp [steps, stepInside, guard, Cpu.stopped, show mid.ms = none from ok, fetch, show isReturn (storeDigest i) = false from rfl]
  have decoded : ∀ index : Fin 8, frameFragmentValid (digestPC index.val) 2 = true := by decide +kernel
  have readTrace := steps_observe_fragment run pc (decoded i)
  have writeTrace := steps_observe_single one midPC store start stop
    (show dataAccesses (storeDigest i) mid = some [⟨true,s.regs.get .rsi+BitVec.ofNat 64 (4*i.val),4⟩] from by
      simp [storeDigest, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes, show mid.regs.get .rsi = s.regs.get .rsi from dst])
  refine ⟨_, steps_append run one, ?_, ?_, ?_, ?_, ?_, readTrace.append writeTrace⟩
  · rw [store_step i mid ok]; exact ok
  · rw [store_step i mid ok]
    change mid.rip + _ = _
    rw [← finish, midPC]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  · rw [store_step i mid ok]; exact sp
  · rw [store_step i mid ok]; exact dst
  · rw [store_step i mid ok]
    change mid.mem.writeSize _ _ _ = _
    rw [mem, show mid.regs.get .rsi = _ from dst, show (mid.regs.get .rax).setWidth 32 = _ from val]
    rfl

private structure DigestPrefix (base dst : Val) (s out : Cpu) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base + BitVec.ofNat 64 (digestPC n)
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rsi = dst
  frame : ∀ p, 32 ≤ (p-dst).toNat → out.mem.read p = s.mem.read p
  written : ∀ i : Fin 8, i.val < n → (wordVector 8 (byteView out.mem) dst)[i.val] =
    reverseWord ((hashWords (project s))[i.val])
  observations : ObservedExecution base s (digestPrefixEvents base (s.regs.get .rsp) dst n) out

private theorem digest_prefix (base dst : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x30f)
    (ptr : s.regs.get .rsi = dst) (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 32 ≤ (base + BitVec.ofNat 64 j - dst).toNat)
    (src : ∀ (i : Fin 8) (b : Fin 4),
      32 ≤ (s.regs.get .rsp + hashSlot i + BitVec.ofNat 64 b.val - dst).toNat)
    (n : Nat) (bound : n ≤ 8) : ∃ out, steps base (3*n) s = some out ∧ DigestPrefix base dst s out n := by
  induction n with
  | zero => exact ⟨s, by simp [steps], ⟨live, pc, rfl, ptr, fun _ _ => rfl, fun _ h => by omega, .nil _⟩⟩
  | succ n ih =>
    let i : Fin 8 := ⟨n,by omega⟩
    obtain ⟨mid, before, prev⟩ := ih (by omega)
    have code : ImageLoaded base mid.mem := fun j hj => (prev.frame _ (sep j hj)).trans (loaded j hj)
    obtain ⟨out, run, ok, rip, stack, dest, store, observed⟩ := digest_word base mid i prev.live prev.pc code
    have read : mid.mem.readSize .d (s.regs.get .rsp + hashSlot i) = s.mem.readSize .d (s.regs.get .rsp + hashSlot i) :=
      Mem.readN_congr _ _ _ 4 (fun k hk => prev.frame _ (src i ⟨k,hk⟩))
    have old : (hashWords (project mid))[i.val] = (hashWords (project s))[i.val] := by
      simpa only [hashWords, wordVector, project, Vector.getElem_ofFn, prev.stack, ← byteView_read32,
        hashSlot, BitVec.ofNat_add, BitVec.add_assoc] using congrArg (BitVec.setWidth 32) read
    rw [prev.ptr] at store
    rw [prev.stack,prev.ptr] at observed
    have fullObservation := prev.observations.append observed
    refine ⟨out, by simpa only [Nat.mul_succ] using steps_append before run,
      ⟨ok, rip, stack.trans prev.stack, dest.trans prev.ptr, ?_, ?_,
        by simpa [digestPrefixEvents,i,show n < 8 by omega] using fullObservation⟩⟩
    · intro p hp
      apply Eq.trans _ (prev.frame _ hp)
      rw [← byteView_read, store, byteView_write32, Crypto.ARM64.Imported.read8_write32_outside]
      · rfl
      · exact Crypto.ARM64.Imported.region_word_store_delta _ _ _ 32 (by change 4*n+4 ≤ 32; omega) hp
    · intro j hj
      simp only [wordVector, Vector.getElem_ofFn, store, byteView_write32]
      by_cases eq : i = j
      · subst j; rw [Crypto.ARM64.Imported.read32_write32]; exact congrArg reverseWord old
      · apply Eq.trans _ (prev.written j (by have : n ≠ j.val := fun h => eq (Fin.ext h); omega))
        simp only [wordVector, Vector.getElem_ofFn]
        exact Crypto.ARM64.Imported.read_word_store_other (byteView mid.mem) dst (i.castLE (by decide : 8 ≤ 64))
          (j.castLE (by decide : 8 ≤ 64)) (reverseWord ((hashWords (project mid))[i.val])) (fun e => eq (Fin.ext (congrArg (fun v : Fin 64 => v.val) e)))

def digestPtr (s : Cpu) := s.mem.readSize .q (s.regs.get .rsp+416)

/-- The final 25 load/swap/store instructions serialize the eight hash words
to exactly the 32 big-endian bytes of the digest. -/
theorem digest_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x307)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 32 ≤ (base + BitVec.ofNat 64 j - digestPtr s).toNat)
    (src : ∀ (i : Fin 8) (b : Fin 4), 32 ≤
      (s.regs.get .rsp + BitVec.ofNat 64 (256+4*i.val) + BitVec.ofNat 64 b.val - digestPtr s).toNat) :
    ∃ out, steps base 25 s = some out ∧ out.ms = none ∧ out.rip = base + 0x36e ∧
      out.regs.get .rsp = s.regs.get .rsp ∧
      (∀ p, 32 ≤ (p-digestPtr s).toNat → out.mem.read p = s.mem.read p) ∧
      memoryBytes32 (byteView out.mem) (digestPtr s) = digestBytes (hashWords (project s)) ∧
      ObservedExecution base s (digestEvents base (s.regs.get .rsp) (digestPtr s)) out := by
  let mid := X86.step getPtr s
  have f := fetch_at base s 0x307 getPtr loaded pc ptr_decode (by decide) (by decide)
  have one : steps base 1 s = some mid := by simp [steps, stepInside, guard, Cpu.stopped, live, f, mid, show isReturn getPtr = false from rfl]
  have stack : mid.regs.get .rsp = s.regs.get .rsp := by simp [mid, ptr_step _ live, Regs.get_set_ne]
  have mem : mid.mem = s.mem := by simp [mid, ptr_step _ live]
  obtain ⟨out, run, post⟩ := digest_prefix base (digestPtr s) mid
    (by simp [mid, ptr_step _ live, live]) (by simp [mid, ptr_step _ live, pc, BitVec.add_assoc])
    (by simp [mid, ptr_step _ live, digestPtr]) (mem ▸ loaded) sep (by simpa only [stack] using src) 8 (by decide)
  have hash : hashWords (project mid) = hashWords (project s) := by simp only [hashWords, project, mem, stack]
  have getObservation := steps_observe_fragment one pc (by decide +kernel)
  have rest := post.observations
  rw [stack] at rest
  have observe : ObservedExecution base s (digestEvents base (s.regs.get .rsp) (digestPtr s)) out :=
    getObservation.append rest
  refine ⟨out, steps_append one run, post.live, post.pc, post.stack.trans stack,
    fun p hp => (post.frame _ hp).trans (congrArg (fun m : Mem => m.read p) mem), ?_,observe⟩
  apply Crypto.ARM64.Imported.bytes_of_reversed_words
  apply Vector.ext
  intro j hj
  simpa only [hash, Vector.getElem_map] using post.written ⟨j,hj⟩ hj

end Crypto.X86_64
