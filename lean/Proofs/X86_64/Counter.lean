import Proofs.X86_64.Fetch

namespace Crypto.X86_64
open X86

def incIndex : Instr := ⟨.un .inc .q (.reg .rbx), 3⟩
def cmpLimit (limit : Val) : Instr := ⟨.bin .cmp .q (.reg .rbx) (.imm limit), 4⟩
def branchBelow (disp : Val) : Instr := ⟨.jcc .b disp, 2⟩

theorem inc_step (s : Cpu) (live : s.ms = none) :
    X86.step incIndex s = { s with
      regs := s.regs.set .rbx (s.regs.get .rbx + 1),
      flags := Flags.inc .q (s.regs.get .rbx) s.flags, rip := s.rip + 3 } := by
  simp [incIndex, X86.step, Cpu.stopped, live, Cpu.readOperand, Cpu.writeOperand,
    Cpu.getReg, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Flags.addResult, Value.writeView]

theorem index_cmp_step (s : Cpu) (limit : Val) (live : s.ms = none) :
    X86.step (cmpLimit limit) s = { s with
      flags := Flags.sub .q (s.regs.get .rbx) limit s.flags, rip := s.rip + 4 } := by
  simp [cmpLimit, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem,
    Cpu.readOperand, Cpu.getReg, Cpu.setRip, Cpu.setFlags]

private theorem branch_step (s : Cpu) (disp : Val) (live : s.ms = none)
    (valid : canonical (s.rip + 2 + disp) = true) :
    X86.step (branchBelow disp) s = { s with
      rip := if s.flags.cf then s.rip + 2 + disp else s.rip + 2 } := by
  cases cf : s.flags.cf <;>
    simp [branchBelow, X86.step, Cpu.stopped, live, Cc.eval, cf, Cpu.setRipChecked, Cpu.setRip]
  simp_all

def countCode (limit disp : Val) := [incIndex, cmpLimit limit, branchBelow disp]

/-- INC/CMP/JB updates the public index and selects the back edge from the
unsigned result of CMP, independently of the incoming flags. -/
theorem count_run (s : Cpu) (limit disp : Val) (live : s.ms = none)
    (target : canonical (s.rip + 9 + disp) = true) :
    let n := s.regs.get .rbx + 1
    let out := X86.run (countCode limit disp) s
    out.regs = s.regs.set .rbx n ∧ out.mem = s.mem ∧ out.ms = none ∧
      out.rip = if n.toNat < limit.toNat then s.rip + 9 + disp else s.rip + 9 := by
  let s1 := X86.step incIndex s
  let s2 := X86.step (cmpLimit limit) s1
  have h1 : s1.ms = none := by simpa [s1, inc_step _ live] using live
  have h2 : s2.ms = none := by simpa [s2, index_cmp_step _ _ h1] using h1
  have pc : s2.rip + 2 = s.rip + 9 := by
    simp [s2, index_cmp_step _ _ h1, s1, inc_step _ live, BitVec.add_assoc]
  change (X86.step (branchBelow disp) s2).regs = _ ∧
    (X86.step (branchBelow disp) s2).mem = _ ∧ (X86.step (branchBelow disp) s2).ms = _ ∧
    (X86.step (branchBelow disp) s2).rip = _
  rw [branch_step _ _ h2 (by rw [pc]; exact target)]
  simp [s2, index_cmp_step _ _ h1, s1, inc_step _ live, Flags.sub, Flags.subCF, Value.uval, live,
    BitVec.add_assoc]

theorem count_fetched (base : Val) (s : Cpu) (off : Nat) (limit disp : Val)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + BitVec.ofNat 64 off) (bound : off + 9 ≤ codeEnd)
    (inc : decodeAt image off = some incIndex)
    (cmp : decodeAt image (off + 3) = some (cmpLimit limit))
    (jb : decodeAt image (off + 7) = some (branchBelow disp)) :
    steps base 3 s = some (X86.run (countCode limit disp) s) := by
  let s1 := X86.step incIndex s
  let s2 := X86.step (cmpLimit limit) s1
  have h1 : s1.ms = none := by simpa [s1, inc_step _ live] using live
  have h2 : s2.ms = none := by simpa [s2, index_cmp_step _ _ h1] using h1
  have first := fetch_at base s off incIndex loaded pc inc (by omega) (by change off + 3 ≤ codeEnd; omega)
  have m1 : s1.mem = s.mem := by simp [s1, inc_step _ live]
  have p1 : s1.rip = base + BitVec.ofNat 64 (off+3) := by
    simp [s1, inc_step _ live, pc, BitVec.ofNat_add, BitVec.add_assoc]
  have second := fetch_at base s1 (off+3) (cmpLimit limit) (m1 ▸ loaded) p1 cmp
    (by omega) (by change off+3+4 ≤ codeEnd; omega)
  have m2 : s2.mem = s.mem := by simp [s2, index_cmp_step _ _ h1, m1]
  have p2 : s2.rip = base + BitVec.ofNat 64 (off+7) := by
    simp [s2, index_cmp_step _ _ h1, p1, BitVec.ofNat_add, BitVec.add_assoc]
  have third := fetch_at base s2 (off+7) (branchBelow disp) (m2 ▸ loaded) p2 jb
    (by omega) (by change off+7+2 ≤ codeEnd; omega)
  have one : stepInside base s = some s1 := by simp [stepInside, guard, Cpu.stopped, live, first, s1, show isReturn incIndex = false from rfl]
  have two : stepInside base s1 = some s2 := by simp [stepInside, guard, Cpu.stopped, h1, second, s2, show isReturn (cmpLimit limit) = false from rfl]
  have three : stepInside base s2 = some (X86.step (branchBelow disp) s2) := by
    simp [stepInside, guard, Cpu.stopped, h2, third, show isReturn (branchBelow disp) = false from rfl]
  simp only [steps, one, Option.bind_some, two, three]
  rfl

theorem count_exit (base : Val) (s : Cpu) (off : Nat) (limit disp : Val)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + BitVec.ofNat 64 off) (bound : off + 9 ≤ codeEnd)
    (inc : decodeAt image off = some incIndex)
    (cmp : decodeAt image (off + 3) = some (cmpLimit limit))
    (jb : decodeAt image (off + 7) = some (branchBelow disp))
    (target : canonical (s.rip + 9 + disp) = true) :
    ∃ out, steps base 3 s = some out ∧ out.regs = s.regs.set .rbx (s.regs.get .rbx + 1) ∧
      out.mem = s.mem ∧ out.ms = none ∧
      out.rip = if (s.regs.get .rbx + 1).toNat < limit.toNat then s.rip + 9 + disp else s.rip + 9 :=
  ⟨_, count_fetched base s off limit disp live loaded pc bound inc cmp jb, count_run s limit disp live target⟩

end Crypto.X86_64
