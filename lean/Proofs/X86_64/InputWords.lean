import Proofs.X86_64.Memory
import Proofs.X86_64.Fragments
import Proofs.X86_64.CompressionTrace
import Proofs.ARM64.ImportedMemoryRange

namespace Crypto.X86_64
open X86

private theorem input_decoded : decodeSeq 0x16d inputBody.length = some (instructions inputBody) := by
  decide +kernel

def sourceWord (s : Cpu) (t : Nat) : Word :=
  let a := s.regs.get .rbp + BitVec.ofNat 64 (4*t)
  s.mem.read a ++ s.mem.read (a+1) ++ s.mem.read (a+2) ++ s.mem.read (a+3)

def sourceBlock (s : Cpu) : Vector Word 16 := Vector.ofFn (fun i => sourceWord s i.val)

theorem bswap_bytes (a b c d : BitVec 8) :
    (Value.bswap .d ((d ++ c ++ b ++ a).setWidth 64)).setWidth 32 = a ++ b ++ c ++ d := by
  simp only [Value.bswap, Value.byteRev, Size.bytes, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil, trunc32, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  have bits (w x y z : BitVec 8) (i : Nat) :
      ((w ++ x ++ y ++ z) : BitVec 32).getLsbD i =
        if i < 8 then z.getLsbD i else if i-8 < 8 then y.getLsbD (i-8)
        else if i-8-8 < 8 then x.getLsbD (i-8-8) else w.getLsbD (i-8-8-8) := by
    rw [BitVec.getLsbD_append (x := w ++ x ++ y) (y := z),
      BitVec.getLsbD_append (x := w ++ x) (y := y), BitVec.getLsbD_append (x := w) (y := x)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp (config := { decide := true }) <;>
    simp only [← BitVec.getLsbD_eq_getElem, bits] <;> simp (config := { decide := true })

private theorem input_value (s : Cpu) (t : Nat) (idx : s.regs.get .rbx = BitVec.ofNat 64 t) :
    let out := evalBlock inputBody (project s)
    out.mem = s.mem.writeSize .d (s.regs.get .rsp + BitVec.ofNat 64 (4*t)) ((sourceWord s t).setWidth 64) ∧
    out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rdi = s.regs.get .rdi ∧
    out.regs.get .rbp = s.regs.get .rbp ∧ out.regs.get .rbx = s.regs.get .rbx := by
  have scale : s.regs.get .rbx * 4#64 = BitVec.ofNat 64 (4*t) := by
    rw [idx, BitVec.ofNat_mul, BitVec.mul_comm]
  simp (config := { decide := true }) [inputBody, evalBlock, WordInst.eval, WordOp.apply, project,
    DataState.word, DataState.put, Regs.get_set_ne, Indexed.read, Indexed.addr,
    byteView_read32, Arm64.Memory.read32, sourceWord, bswap_bytes]
  rw [scale]

private theorem input_loaded (base : Val) (s : Cpu) (t : Nat) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x16d)
    (index : s.regs.get .rbx = BitVec.ofNat 64 t) :
    ∃ out, steps base 3 s = some out ∧ out.ms = none ∧ out.rip = base + 0x176 ∧
      out.mem = s.mem.writeSize .d (s.regs.get .rsp + BitVec.ofNat 64 (4*t)) ((sourceWord s t).setWidth 64) ∧
      out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rdi = s.regs.get .rdi ∧
      out.regs.get .rbp = s.regs.get .rbp ∧ out.regs.get .rbx = s.regs.get .rbx := by
  obtain ⟨proj, ok, rip⟩ := word_block inputBody s live
  have value := input_value s t index
  rw [← proj] at value
  exact ⟨_, fetch_word_block _ _ _ _ live loaded pc (by decide) input_decoded, ok,
    rip.trans (by rw [pc, BitVec.add_assoc]; rfl), value⟩

private theorem inputLatch :
    decodeAt image 0x176 = some incIndex ∧
    decodeAt image 0x179 = some (cmpLimit 16) ∧
    decodeAt image 0x17d = some (branchBelow (-18)) := by decide +kernel

attribute [local irreducible] steps X86.run stackWords

private theorem input_cycle (base : Val) (s : Cpu) (t : Fin 16) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x16d)
    (index : s.regs.get .rbx = BitVec.ofNat 64 t.val)
    (sep : ∀ j, j < image.size → 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (target : canonical (base + 0x16d) = true) :
    ∃ out, steps base 6 s = some out ∧ out.ms = none ∧
      out.rip = (if t.val+1 < 16 then base + 0x16d else base + 0x17f) ∧
      out.regs.get .rbx = BitVec.ofNat 64 (t.val+1) ∧
      out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rbp = s.regs.get .rbp ∧
      (∀ p, 256 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p) ∧
      stackWords out = (stackWords s).set! t.val (sourceWord s t.val) ∧
      ObservedExecution base s (WordLoop.input.iteration base (s.regs.get .rsp) (s.regs.get .rbp) (s.regs.get .rdi) t.val) out := by
  obtain ⟨body, runBody, ok, bodyPC, mem', rsp, rdi, rbp, idx⟩ :=
    input_loaded base s t.val live loaded pc index
  have outside (p : Val) (h : 256 ≤ (p - s.regs.get .rsp).toNat) : body.mem.read p = s.mem.read p := by
    rw [← byteView_read, mem', byteView_write32, Crypto.ARM64.Imported.read8_write32_outside]
    · rfl
    · exact Crypto.ARM64.Imported.workspace_store_delta _ _ (t.castLE (by decide : 16 ≤ 64)) h
  have code : ImageLoaded base body.mem := fun j hj => (outside _ (sep j hj)).trans (loaded j hj)
  have back : body.rip + 9 + (-18) = base + 0x16d := by rw [bodyPC]; simp [BitVec.add_assoc]
  obtain ⟨out, latched, regs, sameMem, live', pc'⟩ := count_exit base body 0x176 16 (-18) ok
    code bodyPC (by decide) inputLatch.1 inputLatch.2.1 inputLatch.2.2 (by rw [back]; exact target)
  have next : body.regs.get .rbx + 1 = BitVec.ofNat 64 (t.val+1) := by
    rw [BitVec.ofNat_add, show body.regs.get .rbx = BitVec.ofNat 64 t.val from idx.trans index]; rfl
  have stack : out.regs.get .rsp = s.regs.get .rsp := by
    rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rsp
  refine ⟨out, steps_append runBody latched, live', ?_, ?_, stack, ?_, ?_, ?_, ?_,
    WordLoop.input.observed_iteration live ok pc bodyPC index runBody latched⟩
  · rw [next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := t.isLt; omega), back, bodyPC] at pc'
    simpa only [BitVec.add_assoc] using pc'
  · rw [regs, Regs.get_set_same, next]
  · rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rdi
  · rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rbp
  · intro p hp; rw [sameMem]; exact outside _ hp
  · unfold stackWords
    rw [stack, sameMem, mem', byteView_write32]
    exact Crypto.ARM64.Imported.wordVector_store64 _ _ (t.castLE (by decide : 16 ≤ 64)) _

structure InputState (s out : Cpu) (base : Val) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = if n < 16 then base + 0x16d else base + 0x17f
  index : out.regs.get .rbx = BitVec.ofNat 64 n
  stack : out.regs.get .rsp = s.regs.get .rsp
  constants : out.regs.get .rdi = s.regs.get .rdi
  blockPtr : out.regs.get .rbp = s.regs.get .rbp
  frame : ∀ p, 256 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p
  words : ∀ j : Nat, j < n → (stackWords out)[j]! = sourceWord s j
  observations : ObservedExecution base s (WordLoop.input.prefix base (s.regs.get .rsp)
    (s.regs.get .rbp) (s.regs.get .rdi) n) out

theorem input_prefix (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x16d)
    (idx : s.regs.get .rbx = 0) (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (src : ∀ (t : Fin 16) (b : Fin 4),
      256 ≤ (s.regs.get .rbp + BitVec.ofNat 64 (4*t.val) + BitVec.ofNat 64 b.val - s.regs.get .rsp).toNat)
    (target : canonical (base + 0x16d) = true) (n : Nat) (bound : n ≤ 16) :
    ∃ out, steps base (n*6) s = some out ∧ InputState s out base n := by
  induction n with
  | zero => exact ⟨s, by simp [steps], ⟨live, pc, idx, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => by omega, .nil _⟩⟩
  | succ n ih =>
    have small : n < 16 := by omega
    let t : Fin 16 := ⟨n,small⟩
    obtain ⟨mid, before, state⟩ := ih (by omega)
    have code : ImageLoaded base mid.mem := fun j hj => (state.frame _ (sep j hj)).trans (loaded j hj)
    obtain ⟨out, one, ok, rip, idx', rsp, rdi, rbp, frame, words, observations⟩ :=
      input_cycle base mid t state.live code (by simpa [small] using state.pc) state.index
        (by simpa only [state.stack] using sep) target
    have word : sourceWord mid n = sourceWord s n := by
      have h (b : Fin 4) := state.frame _ (src t b)
      simp only [sourceWord, state.blockPtr]
      simp only [show t.val = n from rfl] at h
      exact congrArg₂ BitVec.append (congrArg₂ BitVec.append
        (congrArg₂ BitVec.append (by simpa using h 0) (h 1)) (h 2)) (h 3)
    rw [state.stack, state.blockPtr, state.constants] at observations
    refine ⟨out, ?_, ⟨ok, rip, idx', rsp.trans state.stack, rdi.trans state.constants,
      rbp.trans state.blockPtr, ?_, ?_, state.observations.append (by simpa only [WordLoop.initialIndex, Nat.zero_add, t] using observations)⟩⟩
    · rw [Nat.succ_mul]; exact steps_append before one
    · intro p hp
      exact (frame _ (by rw [state.stack]; exact hp)).trans (state.frame _ hp)
    · intro j hj
      have hj' : j < 64 := by omega
      rw [words, SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ hj',
        Crypto.ARM64.Imported.vector_setBang_eq_setIfInBounds, Vector.getElem_setIfInBounds]
      by_cases eq : n = j
      · subst j; simpa [t] using word
      · have earlier := state.words j (by omega)
        simpa [t, eq, hj'] using earlier

end Crypto.X86_64
