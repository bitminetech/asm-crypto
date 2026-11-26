import Proofs.X86_64.Memory
import Proofs.X86_64.Fragments
import Proofs.X86_64.CompressionTrace
import Proofs.ARM64.ImportedScheduleSpec
import Proofs.ARM64.ImportedMemoryRange

namespace Crypto.X86_64
open X86 Crypto.Reference.WordModel
open Crypto.ARM64.Imported (wordVector expandedWords)

private theorem slot (s : Cpu) (t : Fin 64) (index : s.regs.get .rbx = BitVec.ofNat 64 t.val) :
    Indexed.addr ⟨.rsp, 0⟩ (project s) = s.regs.get .rsp + BitVec.ofNat 64 (4*t.val) := by
  simp [Indexed.addr, project, index, BitVec.ofNat_mul, BitVec.mul_comm]

private theorem previousWord (s : Cpu) (t : Fin 64) (k : Nat) (hk : k ≤ t.val)
    (index : s.regs.get .rbx = BitVec.ofNat 64 t.val) :
    tableWord (project s) .rsp (-BitVec.ofNat 64 (4*k)) = (stackWords s)[t.val-k]! := by
  have hb : t.val-k < 64 := by have := t.isLt; omega
  unfold tableWord Indexed.read Indexed.addr project
  simp only [index, byteView_read32]
  rw [show BitVec.ofNat 64 t.val * 4 = BitVec.ofNat 64 (4*t.val) by
    rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl]
  rw [← BitVec.sub_eq_add_neg, Crypto.ARM64.Imported.slot_address_back _ _ _ hk]
  simp [stackWords, wordVector, hb]

private theorem expansionLatch :
    decodeAt image 0x1b9 = some incIndex ∧
    decodeAt image 0x1bc = some (cmpLimit 64) ∧
    decodeAt image 0x1c0 = some (branchBelow (-67)) := by decide +kernel

structure ScheduleState (s out : Cpu) (base : Val) (W : Vector Word 64) (t : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = if t < 64 then base + 0x17f else base + 0x1c2
  index : out.regs.get .rbx = BitVec.ofNat 64 t
  stack : out.regs.get .rsp = s.regs.get .rsp
  constants : out.regs.get .rdi = s.regs.get .rdi
  blockPtr : out.regs.get .rbp = s.regs.get .rbp
  frame : ∀ p, 256 ≤ (p - s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p
  words : stackWords out = W

attribute [local irreducible] steps X86.run specScheduleStep expandedWords

private theorem schedule_step (base : Val) (s : Cpu) (M : Vector Word 16) (t : Fin 64)
    (ge : 16 ≤ t.val) (live : s.ms = none) (pc : s.rip = base + 0x17f)
    (index : s.regs.get .rbx = BitVec.ofNat 64 t.val) (loaded : ImageLoaded base s.mem)
    (separate : ∀ j, j < image.size → 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (canonicalBase : canonical (base + 0x17f) = true) :
    ∃ out, steps base 23 s = some out ∧ ScheduleState s out base
      (specScheduleStep M t.val (stackWords s)) (t.val + 1) ∧
      ObservedExecution base s (WordLoop.expansion.iteration base (s.regs.get .rsp)
        (s.regs.get .rbp) (s.regs.get .rdi) t.val) out := by
  obtain ⟨body, runBody, ok, bodyPC, mem, idx, rsp, rdi, rbp⟩ :=
    expansion_loaded base s live loaded pc
  rw [slot s t index] at mem
  have outside (p : Val) (h : 256 ≤ (p - s.regs.get .rsp).toNat) :
      body.mem.read p = s.mem.read p := by
    rw [← byteView_read, mem, byteView_write32, Crypto.ARM64.Imported.read8_write32_outside]
    · rfl
    · exact Crypto.ARM64.Imported.workspace_store_delta _ _ t h
  have code : ImageLoaded base body.mem := fun j hj => (outside _ (separate j hj)).trans (loaded j hj)
  have back : body.rip + 9 + (-67) = base + 0x17f := by rw [bodyPC]; simp [BitVec.add_assoc]
  obtain ⟨out, latched, regs, sameMem, live', pc'⟩ := count_exit base body 0x1b9 64 (-67)
    ok code bodyPC (by decide) expansionLatch.1 expansionLatch.2.1 expansionLatch.2.2
    (by rw [back]; exact canonicalBase)
  have next : body.regs.get .rbx + 1 = BitVec.ofNat 64 (t.val+1) := by
    rw [BitVec.ofNat_add, show body.regs.get .rbx = BitVec.ofNat 64 t.val from idx.trans index]; rfl
  have stack : out.regs.get .rsp = s.regs.get .rsp := by
    rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rsp
  refine ⟨out, ?_, ⟨live', ?_, ?_, stack, ?_, ?_, ?_, ?_⟩,
    WordLoop.expansion.observed_iteration live ok pc bodyPC index runBody latched⟩
  · exact steps_append runBody latched
  · rw [next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := t.isLt; omega), back, bodyPC] at pc'
    simpa only [BitVec.add_assoc] using pc'
  · rw [regs, Regs.get_set_same, next]
  · rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rdi
  · rw [regs, Regs.get_set_ne _ _ _ _ (by decide)]; exact rbp
  · intro p hp
    rw [sameMem]; exact outside _ hp
  · conv_lhs => unfold stackWords
    rw [stack, show out.mem = _ from sameMem, mem, byteView_write32, Crypto.ARM64.Imported.wordVector_store64]
    change (stackWords s).set! t.val (expandedWord (project s)) = specScheduleStep M t.val (stackWords s)
    have prev (k : Nat) (h : k ≤ t.val) := previousWord s t k h index
    simp only [expandedWord, specScheduleStep, if_neg (by omega : ¬t.val < 16)]
    rw [← prev 2 (by omega), ← prev 7 (by omega), ← prev 15 (by omega), ← prev 16 ge]
    rfl

theorem schedule_prefix (base : Val) (s : Cpu) (M : Vector Word 16)
    (live : s.ms = none) (pc : s.rip = base + 0x17f) (index : s.regs.get .rbx = 16)
    (loaded : ImageLoaded base s.mem)
    (separate : ∀ j, j < image.size → 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (target : canonical (base + 0x17f) = true) (n : Nat) (bound : n ≤ 48) :
    ∃ out, steps base (n*23) s = some out ∧
      ScheduleState s out base (expandedWords M (stackWords s) n) (16+n) ∧
      ObservedExecution base s (WordLoop.expansion.prefix base (s.regs.get .rsp)
        (s.regs.get .rbp) (s.regs.get .rdi) n) out := by
  induction n with
  | zero =>
    exact ⟨s, by simp [steps], ⟨live, pc, index, rfl, rfl, rfl, fun _ _ => rfl, by simp [expandedWords]⟩, .nil _⟩
  | succ n ih =>
    have small : 16+n < 64 := by omega
    obtain ⟨mid, before, state, prior⟩ := ih (by omega)
    have code : ImageLoaded base mid.mem := fun j hj => (state.frame _ (separate j hj)).trans (loaded j hj)
    have apart j (hj : j < image.size) :
        256 ≤ (base + BitVec.ofNat 64 j - mid.regs.get .rsp).toNat := by
      rw [state.stack]; exact separate j hj
    obtain ⟨out, one, post, observed⟩ := schedule_step base mid M ⟨16+n,small⟩ (by change 16 ≤ 16+n; omega)
      state.live (by simpa [small] using state.pc) state.index code apart target
    rw [state.stack, state.constants, state.blockPtr] at observed
    refine ⟨out, ?_, ⟨post.live, post.pc, post.index, post.stack.trans state.stack,
      post.constants.trans state.constants, post.blockPtr.trans state.blockPtr, ?_, ?_⟩, prior.append observed⟩
    · rw [Nat.succ_mul]; exact steps_append before one
    · intro p h
      exact (post.frame p (by rw [state.stack]; exact h)).trans (state.frame p h)
    · rw [post.words, state.words]
      simp [expandedWords, Fin.foldl_succ_last]

/-- All 48 new words are derived from the initial 16. Arbitrary old bytes in
slots 16–63 are allowed. The fetched loop writes only to its 256-byte table. -/
theorem schedule_loaded (base : Val) (s : Cpu) (M : Vector Word 16)
    (live : s.ms = none) (pc : s.rip = base + 0x17f) (index : s.regs.get .rbx = 16)
    (loaded : ImageLoaded base s.mem)
    (separate : ∀ j, j < image.size → 256 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rsp).toNat)
    (target : canonical (base + 0x17f) = true)
    (initial : ∀ j, j < 16 → (stackWords s)[j]! = M[j]!) :
    ∃ out, steps base 1104 s = some out ∧ ScheduleState s out base (Crypto.Reference.WordModel.schedule M) 64 ∧
      ObservedExecution base s (WordLoop.expansion.prefix base (s.regs.get .rsp)
        (s.regs.get .rbp) (s.regs.get .rdi) 48) out := by
  obtain ⟨out, run, post, observed⟩ := schedule_prefix base s M live pc index loaded separate target 48 (by decide)
  rw [Crypto.ARM64.Imported.expanded_eq_schedule _ _ initial] at post
  exact ⟨out, run, post, observed⟩

end Crypto.X86_64
