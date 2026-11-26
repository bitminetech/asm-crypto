import Proofs.X86_64.Fetch

namespace Crypto.X86_64
open X86

/-- Successors of a scalar instruction before RET, as image-relative addresses.
A conditional branch admits both outcomes. -/
def nextAddresses (pc : Val) (i : Instr) : List Val :=
  let next := pc + BitVec.ofNat 64 i.len
  match i.op with
  | .ret => []
  | .jmp (.rel d) => [next+d]
  | .jcc _ d => [next+d, next]
  | _ => [next]

def successors (off : Nat) := nextAddresses (BitVec.ofNat 64 off)

theorem fetch_decodes {base s i} (h : fetch base s = some i) :
    decodeAt image (s.rip-base).toNat = some i := by
  unfold fetch at h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,d,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  exact Option.some.inj h ▸ d

def Reaches (pcs : List Val) (s : Cpu) : Prop := s.ms = none → s.rip ∈ pcs

@[local simp] private theorem reaches_set (s : Cpu) (p : Val) (pcs : List Val) (h : p ∈ pcs) :
    Reaches pcs (s.setRip p) := fun _ => h

@[local simp] private theorem reaches_halt (s : Cpu) (e : MsErr) (pcs : List Val) :
    Reaches pcs (s.halt e) := by cases h : s.ms <;> simp [Reaches,Cpu.halt,h]

@[local simp] private theorem reaches_checked (s : Cpu) (p : Val) (pcs : List Val) (h : p ∈ pcs) :
    Reaches pcs (s.setRipChecked p) := by
  unfold Cpu.setRipChecked; split
  · exact fun _ => h
  · apply reaches_halt

/-- Only a control transfer can change RIP away from the next instruction.
Faulted states have no continuing edge. -/
theorem step_edges (form : ScalarForm) (len : Nat) (s : Cpu) (live : s.ms = none)
    (regular : isReturn ⟨form.op,len⟩ = false) :
    Reaches (nextAddresses s.rip ⟨form.op,len⟩) (X86.step ⟨form.op,len⟩ s) := by
  cases form
  all_goals try cases ‹BinKind›
  all_goals try cases ‹Bool›
  all_goals simp [ScalarForm.op, isReturn] at regular
  all_goals simp [ScalarForm.op, nextAddresses, X86.step, Cpu.stopped, live] <;>
    repeat (split <;> try simp)

theorem fetched_scalar {base : Val} {s : Cpu} {i : Instr} (h : fetch base s = some i) : ScalarLeaf i := by
  unfold fetch at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨op, decoded, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Option.some.inj h ▸ decodeAt_scalar decoded

private def otherReg (r : GPR) := decide (r ≠ .rsp)
private def otherDst : Operand → Bool
  | .reg r _ => otherReg r
  | _ => true

def keepsStack (i : Instr) := match i.op with
  | .mov _ d _ | .bin _ _ d _ | .rot _ _ d _ | .shift _ _ d _ | .un _ _ d => otherDst d
  | .movx _ _ _ r _ | .lea _ r _ | .bswap _ r => otherReg r
  | .jmp (.rel _) | .jcc .. => true
  | _ => false

private def sp (s : Cpu) := s.regs.get .rsp
@[local simp] private theorem halt_sp (s : Cpu) (e : MsErr) : sp (s.halt e) = sp s := by
  cases h : s.ms <;> simp [Cpu.halt,h,sp]
@[local simp] private theorem rip_sp (s : Cpu) (v : Val) : sp (s.setRip v) = sp s := rfl
@[local simp] private theorem checked_sp (s : Cpu) (v : Val) : sp (s.setRipChecked v) = sp s := by
  unfold Cpu.setRipChecked; split <;> first | rfl | apply halt_sp
@[local simp] private theorem flags_sp (s : Cpu) (f : Flags) : sp (s.setFlags f) = sp s := rfl
@[local simp] private theorem undef_sp (s : Cpu) : sp s.undefBit.2 = sp s := rfl
@[local simp] private theorem mem_sp (s : Cpu) (sz : Size) (a v : Val) : sp (s.writeMem sz a v) = sp s := rfl
@[local simp] private theorem reg_sp (s : Cpu) (sz : Size) (r : GPR) (v : Val) (high : Bool)
    (h : r ≠ .rsp) : sp (s.setReg sz r v high) = sp s := by simp [sp,Cpu.setReg,h]
@[local simp] private theorem operand_sp (s : Cpu) (sz : Size) (nr : Val) (d : Operand) (v : Val)
    (h : otherDst d = true) : sp (s.writeOperand sz nr d v) = sp s := by
  cases d <;> simp_all [Cpu.writeOperand, otherDst, otherReg]

theorem keep_stack (form : ScalarForm) (len : Nat) (s : Cpu) (live : s.ms = none)
    (kept : keepsStack ⟨form.op,len⟩ = true) : sp (X86.step ⟨form.op,len⟩ s) = sp s := by
  cases form
  all_goals try cases ‹BinKind›
  all_goals try cases ‹Bool›
  all_goals simp only [ScalarForm.op,keepsStack,otherReg,decide_eq_true_eq,Bool.false_eq_true] at kept
  all_goals try contradiction
  all_goals simp [ScalarForm.op,X86.step,Cpu.stopped,live,kept] <;> repeat (split <;> try simp [kept])

end Crypto.X86_64
