import Proofs.X86_64.HashLoad
import Proofs.ARM64.ImportedHashFrame

namespace Crypto.X86_64
open X86 Crypto.Reference.WordModel
open Crypto.ARM64.Imported (wordVector)

def workReg (i : Fin 8) : GPR := (#v[.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] : Vector GPR 8)[i.val]

private theorem workReg_word (s : DataState) (i : Fin 8) :
    s.word (workReg i) = (working s)[i.val] := by
  obtain ⟨i, hi⟩ := i
  interval_cases i <;> rfl

private theorem addH_word (h w : Vector Word 8) (i : Fin 8) :
    (addH h w)[i.val] = w[i.val] + h[i.val] := by
  obtain ⟨i, hi⟩ := i
  interval_cases i <;> simp [addH]

def feedInst (i : Fin 8) : Instr :=
  ⟨.bin .add .d (.mem {base := some .rsp, disp := BitVec.ofNat 64 (256+4*i.val)}) (.reg (workReg i)), 8⟩

private theorem feed_decode : ∀ i : Fin 8,
    decodeAt image (0x282 + 8*i.val) = some (feedInst i) := by decide +kernel

def hashBase (s : Cpu) := s.regs.get .rsp + 256

private theorem feed_step (s : Cpu) (i : Fin 8) (live : s.ms = none) :
    let addr := hashBase s + BitVec.ofNat 64 (4*i.val)
    let val := (working (project s))[i.val] + (hashWords (project s))[i.val]
    let out := X86.step (feedInst i) s
    out.regs = s.regs ∧ out.ms = none ∧ out.rip = s.rip + 8 ∧
      out.mem = s.mem.writeSize .d addr (val.setWidth 64) := by
  rw [← workReg_word]
  simp [feedInst, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.setFlags,
    Cpu.readOperand, Cpu.writeOperand, Cpu.writeMem, Cpu.readMem, Cpu.getReg, Cpu.setRip,
    Ea.addr, Ea.offset, Flags.addResult, trunc32, BitVec.setWidth_add _ _ (by decide : 32 ≤ 64),
    DataState.word, project, hashWords, hashBase, wordVector, ← byteView_read32,
    BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm]

structure FeedState (base : Val) (s out : Cpu) (n : Nat) : Prop where
  regs : out.regs = s.regs
  live : out.ms = none
  pc : out.rip = base + BitVec.ofNat 64 (0x282 + 8*n)
  frame : ∀ p, 32 ≤ (p - hashBase s).toNat → out.mem.read p = s.mem.read p
  words : ∀ j : Fin 8, (hashWords (project out))[j.val] =
    if j.val < n then (working (project s))[j.val] + (hashWords (project s))[j.val]
    else (hashWords (project s))[j.val]

private theorem feed_cell (s out : Cpu) (i j : Fin 8) (v : Word)
    (regs : out.regs = s.regs)
    (mem : out.mem = s.mem.writeSize .d (hashBase s + BitVec.ofNat 64 (4*i.val)) (v.setWidth 64)) :
    (hashWords (project out))[j.val] = if i = j then v else (hashWords (project s))[j.val] := by
  simp only [hashWords, project, wordVector, Vector.getElem_ofFn, regs, mem, byteView_write32]
  by_cases h : i = j
  · subst j; simp [hashBase, Crypto.ARM64.Imported.read32_write32]
  · rw [if_neg h]
    apply Crypto.ARM64.Imported.read_word_store_other _ (hashBase s)
      (i.castLE (by decide : 8 ≤ 64)) (j.castLE (by decide : 8 ≤ 64)) v
    intro eq
    exact h (Fin.ext (congrArg (fun n : Fin 64 => n.val) eq))

attribute [local irreducible] steps working hashWords image

theorem feed_prefix (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x282)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 32 ≤ (base + BitVec.ofNat 64 j - hashBase s).toNat)
    (n : Nat) (bound : n ≤ 8) :
    ∃ out, steps base n s = some out ∧ FeedState base s out n := by
  induction n with
  | zero => exact ⟨s, by simp [steps], ⟨rfl, live, pc, fun _ _ => rfl, fun _ => by simp⟩⟩
  | succ n ih =>
    have small : n < 8 := by omega
    let i : Fin 8 := ⟨n,small⟩
    obtain ⟨mid, run, prev⟩ := ih (by omega)
    have code : ImageLoaded base mid.mem := fun j hj => (prev.frame _ (sep j hj)).trans (loaded j hj)
    have fetched := fetch_at base mid (0x282+8*n) (feedInst i) code prev.pc (feed_decode i)
      (by unfold codeEnd; omega) (by change 0x282+8*n+8 ≤ 0x385; omega)
    let out := X86.step (feedInst i) mid
    have one : steps base 1 mid = some out := by
      simp [steps, stepInside, guard, Cpu.stopped, prev.live, fetched, out, show isReturn (feedInst i) = false from rfl]
    obtain ⟨regs, ok, rip, mem⟩ := feed_step mid i prev.live
    have addr : hashBase mid = hashBase s := by simp only [hashBase, prev.regs]
    have work : working (project mid) = working (project s) := by
      simp only [working, DataState.word, project, prev.regs]
    have old := prev.words i
    simp only [i, Nat.lt_irrefl, if_false] at old
    refine ⟨out, steps_append run one, ⟨regs.trans prev.regs, ok, ?_, ?_, ?_⟩⟩
    · rw [rip, prev.pc, BitVec.add_assoc, show 0x282+8*(n+1) = (0x282+8*n)+8 by omega, BitVec.ofNat_add (n := 64) (0x282+8*n) 8]
      rfl
    · intro p hp
      change out.mem.read p = _
      have eq : out.mem.read p = mid.mem.read p := by
        rw [← byteView_read, show out.mem = _ from mem, byteView_write32, Crypto.ARM64.Imported.read8_write32_outside]
        · rfl
        · rw [addr]
          exact Crypto.ARM64.Imported.region_word_store_delta _ _ _ 32 (by change 4*n+4 ≤ 32; omega) hp
      exact eq.trans (prev.frame _ hp)
    · intro j
      rw [feed_cell mid out i j _ regs mem, work]
      by_cases same : i = j
      · subst j; simp [old, i]
      · rw [if_neg same, prev.words]
        have ne : j.val ≠ n := fun eq => same (Fin.ext eq.symm)
        rw [if_congr (by omega : j.val < n ↔ j.val < n+1) rfl rfl]

theorem feed_forward_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base + 0x282)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 32 ≤ (base + BitVec.ofNat 64 j - hashBase s).toNat) :
    ∃ out, steps base 8 s = some out ∧ FeedState base s out 8 ∧
      hashWords (project out) = addH (hashWords (project s)) (working (project s)) := by
  obtain ⟨out, run, post⟩ := feed_prefix base s live pc loaded sep 8 (by decide)
  refine ⟨out, run, post, ?_⟩
  apply Vector.ext
  intro j hj
  exact (by simpa only [hj, if_true, addH_word _ _ ⟨j,hj⟩] using post.words ⟨j,hj⟩)

end Crypto.X86_64
