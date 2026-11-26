import Proofs.X86_64.Compression
import Proofs.X86_64.Counter

namespace Crypto.X86_64
open X86 Crypto.Reference.WordModel

theorem steps_add (base : Val) (n m : Nat) (s : Cpu) :
    steps base (n + m) s = (steps base n s).bind (steps base m) := by
  induction n generalizing s with
  | zero => simp [steps]
  | succ n ih =>
    simp only [Nat.succ_add, steps, ← Option.bind_assoc, ih]

theorem steps_append {base : Val} {a b c : Cpu} {n m : Nat}
    (first : steps base n a = some b) (second : steps base m b = some c) :
    steps base (n+m) a = some c := by
  rw [steps_add, first]
  exact second

theorem return_append {base : Val} {a b c : Cpu} {n m : Nat}
    (first : steps base n a = some b) (last : returnAt base m b = some c) :
    returnAt base (n+m) a = some c := by
  induction n generalizing a with
  | zero =>
    have eq : a = b := by simpa [steps] using first
    simpa only [Nat.zero_add,eq] using last
  | succ n ih =>
    cases stopped : a.stopped <;> cases f : fetch base a with
    | none => simp [steps, stepInside, stopped, f, guard] at first
    | some i =>
      cases ret : isReturn i <;> simp [steps, stepInside, stopped, f, ret, guard] at first <;>
        simpa [Nat.succ_add,returnAt,stopped,f,ret,guard] using ih first

private theorem expansion_frame (s : DataState) :
    let out := evalBlock expansionBody s
    out.regs.get .rbx = s.regs.get .rbx ∧ out.regs.get .rsp = s.regs.get .rsp ∧
    out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rbp = s.regs.get .rbp := by
  simp (config := { decide := true }) [evalBlock, expansionBody, WordInst.eval,
    DataState.put, Regs.get_set_ne]

theorem expansion_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x17f) :
    ∃ out, steps base expansionBody.length s = some out ∧ out.ms = none ∧
      out.rip = base + 0x1b9 ∧ out.mem =
        s.mem.writeSize .d (Indexed.addr ⟨.rsp, 0⟩ (project s))
          ((expandedWord (project s)).setWidth 64) ∧
      out.regs.get .rbx = s.regs.get .rbx ∧ out.regs.get .rsp = s.regs.get .rsp ∧
      out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rbp = s.regs.get .rbp := by
  obtain ⟨proj, ok, rip⟩ := word_block expansionBody s live
  have frame := expansion_frame (project s)
  rw [← proj] at frame
  exact ⟨_, fetch_word_block _ _ _ _ live loaded pc (by decide) expansion_decoded, ok,
    rip.trans (by rw [pc, BitVec.add_assoc]; rfl),
    (congrArg DataState.mem proj).trans (expansion_memory _), frame⟩

/-- The round body preserves the bases and index of its two input tables. -/
private theorem round_frame (s : DataState) :
    let out := evalBlock roundBody s
    out.mem = s.mem ∧ out.regs.get .rbx = s.regs.get .rbx ∧
    out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rsp = s.regs.get .rsp ∧
    out.regs.get .rbp = s.regs.get .rbp := by
  simp (config := { decide := true }) [evalBlock, roundBody, WordInst.eval, DataState.put,
    Regs.get_set_ne]

def wordsAt (s : Cpu) (r : GPR) (i : Nat) : Word :=
  (s.mem.readSize .d (s.regs.get r + BitVec.ofNat 64 i * 4)).setWidth 32

set_option maxRecDepth 8000 in
theorem round_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x204) (t : Nat)
    (index : s.regs.get .rbx = BitVec.ofNat 64 t) (W : Vector Word 64)
    (k : wordsAt s .rdi t = Crypto.Reference.WordModel.K[t]!) (w : wordsAt s .rsp t = W[t]!) :
    ∃ out, steps base roundBody.length s = some out ∧ out.ms = none ∧
      out.rip = base + 0x279 ∧ out.mem = s.mem ∧ out.regs.get .rbx = s.regs.get .rbx ∧
      out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rbp = s.regs.get .rbp ∧
      working (project out) = specRoundStep W t (working (project s)) := by
  obtain ⟨proj, ok, rip⟩ := word_block roundBody s live
  have frame := round_frame (project s)
  rw [← proj] at frame
  obtain ⟨mem, idx, rdi, rsp, rbp⟩ := frame
  refine ⟨_, fetch_word_block _ _ _ _ live loaded pc (by decide) round_decoded, ok,
    rip.trans (by rw [pc, BitVec.add_assoc]; rfl), mem, idx, rdi, rsp, rbp, ?_⟩
  rw [proj, round_value]
  have load (r : GPR) : tableWord (project s) r = wordsAt s r t := by
    simp [tableWord, wordsAt, Indexed.read, Indexed.addr, project, index]
  rw [load, load, k, w]
  rfl

end Crypto.X86_64
