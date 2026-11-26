import Proofs.X86_64.Fragments
import Proofs.X86_64.Observations

namespace Crypto.X86_64
open X86

private def statusInst : Instr := ⟨.mov .d (.reg .rax) (.imm 0), 5⟩
private def freeInst : Instr := ⟨.bin .add .q (.reg .rsp) (.imm 456), 7⟩
private def popInst (r : GPR) (len : Nat) : Instr := ⟨.pop .q (.reg r), len⟩
private def retInst : Instr := ⟨.ret, 1⟩

private def exitCode := [statusInst, freeInst, popInst .r15 2, popInst .r14 2,
  popInst .r13 2, popInst .r12 2, popInst .rbp 1, popInst .rbx 1, retInst]

private theorem exit_decode : decodeSeq 0x36e 9 = some exitCode := by decide +kernel

private theorem status_step (s : Cpu) (live : s.ms = none) :
    X86.step statusInst s = {s with regs := s.regs.set .rax 0, rip := s.rip + 5} := by
  simp [statusInst, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem,
    Cpu.readOperand, Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Value.writeView, trunc32]

private theorem free_step (s : Cpu) (live : s.ms = none) :
    X86.step freeInst s = {s with
      regs := s.regs.set .rsp (s.regs.get .rsp + 456),
      flags := Flags.add .q (s.regs.get .rsp) 456 s.flags, rip := s.rip + 7} := by
  simp [freeInst, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.getReg, Cpu.writeOperand, Cpu.setFlags, Cpu.setReg, Cpu.setRip, Value.writeView, Flags.addResult]

private theorem pop_step (s : Cpu) (r : GPR) (len : Nat) (live : s.ms = none) :
    X86.step (popInst r len) s = {s with
      regs := (s.regs.set .rsp (s.regs.get .rsp + 8)).set r (s.mem.readSize .q (s.regs.get .rsp)),
      rip := s.rip + BitVec.ofNat 64 len} := by
  simp [popInst, X86.step, Cpu.stopped, live, Cpu.popValue, Cpu.writeOperand, Cpu.setReg,
    Cpu.readMem, Cpu.setRip, Size.bytes, Value.writeView]

private theorem ret_step (s : Cpu) (live : s.ms = none) :
    X86.step retInst s =
      if canonical (s.mem.readSize .q (s.regs.get .rsp)) then
        {s with regs := s.regs.set .rsp (s.regs.get .rsp + 8), rip := s.mem.readSize .q (s.regs.get .rsp)}
      else s.halt (.unimplemented "non-canonical return address (#GP(0) in hardware)") := by
  simp [retInst, X86.step, Cpu.stopped, live, Cpu.readMem, Cpu.setReg, Value.writeView]

private theorem fetch_return (base : Val) (ops : List Instr) (off : Nat) (s : Cpu)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem) (pc : s.rip = base + BitVec.ofNat 64 off)
    (decode : decodeSeq off ops.length = some ops)
    (ends : ops.getLast?.map isReturn = some true)
    (linear : ∀ ins ∈ ops.dropLast, ∀ st : Cpu, st.ms = none → ImageLoaded base st.mem →
      let out := X86.step ins st
      isReturn ins = false ∧ out.ms = none ∧ ImageLoaded base out.mem ∧ out.rip = st.rip + BitVec.ofNat 64 ins.len) :
    returnAt base ops.length s = some (X86.run ops s) ∧
      ObservedExecution base s (observeCode ops s) (X86.run ops s) := by
  induction ops generalizing off s with
  | nil => simp at ends
  | cons i rest ih =>
    simp only [List.length_cons, decodeSeq] at decode
    cases hi : decodeAt image off with
    | none => simp [hi] at decode
    | some x =>
      by_cases bound : off < codeEnd ∧ off + x.len ≤ codeEnd
      · cases tail : decodeSeq (off+x.len) rest.length with
        | none => simp [hi, guard, bound, tail] at decode
        | some ys =>
          simp [hi, guard, bound, tail] at decode
          obtain ⟨same, restEq⟩ := decode
          subst x ys
          have fetched := fetch_at _ _ _ _ loaded pc hi bound.1 bound.2
          obtain ⟨accesses,seen⟩ := scalar_accesses_defined i s (decodeAt_scalar hi)
          have stepOne : stepLoaded base s = some (X86.step i s) :=
            by simp [stepLoaded, guard, Cpu.stopped, live, fetched]
          cases rest with
          | nil =>
            have ret : isReturn i = true := by simpa using ends
            exact ⟨by simp [returnAt, guard, Cpu.stopped, live, fetched, ret, X86.run],
              by simpa [observeCode,seen,X86.run] using ObservedExecution.cons fetched stepOne seen (.nil _)⟩
          | cons j more =>
            obtain ⟨ret, hl, code, rip⟩ := linear i (by simp) s live loaded
            have next : returnAt base ((j :: more).length + 1) s =
                returnAt base (j :: more).length (X86.step i s) := by
              rw [returnAt]
              simp [Cpu.stopped, live, guard, fetched, ret]
            obtain ⟨run, observe⟩ := ih _ _ hl code (rip.trans (by rw [pc, BitVec.ofNat_add, BitVec.add_assoc])) tail
              (by simpa using ends) (fun ins member => linear ins (by simp [member]))
            refine ⟨?_,?_⟩
            · rw [List.length_cons, next, X86.run_cons]
              exact run
            · simpa only [observeCode, seen, Option.getD_some, X86.run_cons] using
                ObservedExecution.cons fetched stepOne seen observe
      · simp [hi, guard, bound] at decode

private theorem exit_fetch (base : Val) (s : Cpu) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x36e) :
    returnAt base 9 s = some (X86.run exitCode s) ∧
      ObservedExecution base s (observeCode exitCode s) (X86.run exitCode s) := by
  apply fetch_return base exitCode 0x36e s live loaded pc exit_decode (by decide +kernel)
  intro ins member st ok code
  simp only [exitCode, List.dropLast_cons₂, List.dropLast_singleton, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with h|h|h|h|h|h|h|h <;> subst ins <;>
    first | rw [status_step _ ok] | rw [free_step _ ok] | rw [pop_step _ _ _ ok]
  all_goals exact ⟨rfl, ok, code, rfl⟩

structure ReturnState (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp + 504)
  stack : out.regs.get .rsp = s.regs.get .rsp + 512
  status : out.regs.get .rax = 0
  mem : out.mem = s.mem
  r15 : out.regs.get .r15 = s.mem.readSize .q (s.regs.get .rsp + 456)
  r14 : out.regs.get .r14 = s.mem.readSize .q (s.regs.get .rsp + 464)
  r13 : out.regs.get .r13 = s.mem.readSize .q (s.regs.get .rsp + 472)
  r12 : out.regs.get .r12 = s.mem.readSize .q (s.regs.get .rsp + 480)
  rbp : out.regs.get .rbp = s.mem.readSize .q (s.regs.get .rsp + 488)
  rbx : out.regs.get .rbx = s.mem.readSize .q (s.regs.get .rsp + 496)


private structure Restoring (s out : Cpu) (offset : Nat) (values : Regs) : Prop where
  live : out.ms = none
  mem : out.mem = s.mem
  stack : out.regs.get .rsp = s.regs.get .rsp + BitVec.ofNat 64 offset
  regs : ∀ r, r ≠ .rsp → out.regs.get r = values.get r

attribute [local irreducible] X86.step

private theorem restore_start (s : Cpu) (live : s.ms = none) :
    Restoring s (X86.step freeInst (X86.step statusInst s)) 456 (s.regs.set .rax 0) := by
  have ok : (X86.step statusInst s).ms = none := by rw [status_step _ live]; exact live
  rw [free_step _ ok, status_step _ live]
  constructor
  · exact live
  · rfl
  · simp [Regs.get_set_ne]
  · intro r hr
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm hr)]

private theorem restore_pop (s mid : Cpu) (offset len : Nat) (values : Regs)
    (r : GPR) (other : r ≠ .rsp) (h : Restoring s mid offset values) :
    Restoring s (X86.step (popInst r len) mid) (offset+8)
      (values.set r (s.mem.readSize .q (s.regs.get .rsp + BitVec.ofNat 64 offset))) := by
  rw [pop_step _ _ _ h.live]
  constructor
  · exact h.live
  · exact h.mem
  · simp [Regs.get_set_ne _ _ _ _ other, h.stack, BitVec.ofNat_add, BitVec.add_assoc]
  · intro g hg
    by_cases same : r = g
    · subst g; simp [h.mem, h.stack]
    · simp [Regs.get_set_ne _ _ _ _ same, Regs.get_set_ne _ _ _ _ (Ne.symm hg), h.regs _ hg]

private def restored (s : Cpu) : Regs := Id.run do
  let regs := s.regs.set .rax 0
  let regs := regs.set .r15 (s.mem.readSize .q (s.regs.get .rsp + 456))
  let regs := regs.set .r14 (s.mem.readSize .q (s.regs.get .rsp + 464))
  let regs := regs.set .r13 (s.mem.readSize .q (s.regs.get .rsp + 472))
  let regs := regs.set .r12 (s.mem.readSize .q (s.regs.get .rsp + 480))
  let regs := regs.set .rbp (s.mem.readSize .q (s.regs.get .rsp + 488))
  let regs := regs.set .rbx (s.mem.readSize .q (s.regs.get .rsp + 496))
  return regs

private theorem restore_all (s : Cpu) (live : s.ms = none) :
    Restoring s (X86.run exitCode.dropLast s) 504 (restored s) := by
  have h0 := restore_start s live
  have h1 := restore_pop s _ _ 2 _ .r15 (by decide) h0
  have h2 := restore_pop s _ _ 2 _ .r14 (by decide) h1
  have h3 := restore_pop s _ _ 2 _ .r13 (by decide) h2
  have h4 := restore_pop s _ _ 2 _ .r12 (by decide) h3
  have h5 := restore_pop s _ _ 1 _ .rbp (by decide) h4
  have h6 := restore_pop s _ _ 1 _ .rbx (by decide) h5
  exact h6

private theorem return_from_frame (s mid : Cpu) (h : Restoring s mid 504 (restored s))
    (target : canonical (s.mem.readSize .q (s.regs.get .rsp + 504)) = true) :
    ReturnState s (X86.step retInst mid) := by
  have slot : mid.mem.readSize .q (mid.regs.get .rsp) = s.mem.readSize .q (s.regs.get .rsp + 504) := by
    rw [h.mem, h.stack]; rfl
  rw [ret_step _ h.live, slot, if_pos target]
  constructor
  · exact h.live
  · rfl
  · simp [h.stack, BitVec.add_assoc]
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .rax (by decide))
  · exact h.mem
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .r15 (by decide))
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .r14 (by decide))
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .r13 (by decide))
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .r12 (by decide))
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .rbp (by decide))
  · exact (by simpa [restored, Regs.get_set_ne] using h.regs .rbx (by decide))

def returnEvents (base sp : Val) : List Event :=
  [(base+0x36e,statusInst,[]),(base+0x373,freeInst,[]),
   (base+0x37a,popInst .r15 2,[⟨false,sp+456,8⟩]),
   (base+0x37c,popInst .r14 2,[⟨false,sp+464,8⟩]),
   (base+0x37e,popInst .r13 2,[⟨false,sp+472,8⟩]),
   (base+0x380,popInst .r12 2,[⟨false,sp+480,8⟩]),
   (base+0x382,popInst .rbp 1,[⟨false,sp+488,8⟩]),
   (base+0x383,popInst .rbx 1,[⟨false,sp+496,8⟩]),
   (base+0x384,retInst,[⟨false,sp+504,8⟩])]

private theorem exit_observation (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x36e) :
    observeCode exitCode s = returnEvents base (s.regs.get .rsp) := by
  simp [exitCode,observeCode,returnEvents,statusInst,freeInst,popInst,retInst,dataAccesses,operandAccess,
    X86.step,Cpu.stopped,live,wellFormed2,Operand.isMem, Cpu.readOperand, Cpu.writeOperand,
    Cpu.setReg, Cpu.setRip, Cpu.setFlags, Cpu.getReg, Cpu.popValue, Flags.addResult, Value.writeView,
    Size.bytes,pc,Regs.get_set_ne,BitVec.add_assoc]

theorem return_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x36e)
    (target : canonical (s.mem.readSize .q (s.regs.get .rsp + 504)) = true) :
    ∃ out, returnAt base 9 s = some out ∧ ReturnState s out ∧
      ObservedExecution base s (returnEvents base (s.regs.get .rsp)) out := by
  obtain ⟨run,observe⟩ := exit_fetch base s live loaded pc
  rw [exit_observation base s live pc] at observe
  exact ⟨_,run,return_from_frame s _ (restore_all s live) target,observe⟩

end Crypto.X86_64
