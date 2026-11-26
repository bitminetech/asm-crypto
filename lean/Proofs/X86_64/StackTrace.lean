import Proofs.X86_64.ControlFlow

namespace Crypto.X86_64
open X86

/-- Bytes below entry RSP owned at each instruction boundary. The incoming
eight-byte return slot lies immediately above this allocation. -/
def stackDepth : Nat → Nat
  | 0 | 0x384 => 0
  | 1 | 0x383 => 8
  | 2 | 0x382 => 16
  | 4 | 0x380 => 24
  | 6 | 0x37e => 32
  | 8 | 0x37c => 40
  | 10 | 0x37a => 48
  | _ => 504

private def sp (s : Cpu) := s.regs.get .rsp

private def pushes : List (GPR × Nat) := [(.rbx,1),(.rbp,1),(.r12,2),(.r13,2),(.r14,2),(.r15,2)]
private def updates : List (Instr × Val) :=
  (pushes.map fun (r,n) => (⟨.push .q (.reg r),n⟩,-8)) ++
  (pushes.map fun (r,n) => (⟨.pop .q (.reg r),n⟩,8)) ++
  [(⟨.bin .sub .q (.reg .rsp) (.imm 456),7⟩,-456),(⟨.bin .add .q (.reg .rsp) (.imm 456),7⟩,456)]

private theorem update_sp {i d} (h : (i,d) ∈ updates) (s : Cpu) (live : s.ms = none) :
    sp (X86.step i s) = sp s + d := by
  simp only [updates,pushes,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl⟩ := h
  all_goals simp (config := {decide := true}) [sp,X86.step,Cpu.stopped,live,Cpu.setRip,
    Cpu.push,Cpu.popValue,Cpu.writeOperand,Cpu.setReg,Cpu.writeMem,Size.bytes,
    wellFormed2,Operand.isMem,Cpu.readOperand,Cpu.getReg,Cpu.setFlags,Flags.subResult,Flags.addResult,
    Value.writeView,BitVec.sub_eq_add_neg]

private def validStackEdge (off : Nat) (i : Instr) (next : Val) : Bool :=
  let diff := BitVec.ofNat 64 (stackDepth off) - BitVec.ofNat 64 (stackDepth next.toNat)
  (decide (diff = 0) && keepsStack i) || updates.any (fun p => decide (i = p.1 ∧ diff = p.2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem stackEdges : codeLayout.all (fun p =>
    (successors p.1 p.2).all (validStackEdge p.1 p.2)) = true := by decide +kernel

private theorem depth_bound (pc : Nat) : stackDepth pc ≤ 504 := by unfold stackDepth; split <;> decide

/-- RSP sampled before every instruction in the given ISA instruction trace. -/
def stackTrace : List Instr → Cpu → List Val
  | [], _ => []
  | i :: rest, s => sp s :: stackTrace rest (X86.step i s)

private theorem stack_transition {base s i} (origin : Val) (fetched : fetch base s = some i)
    (start : (s.rip-base).toNat ∈ starts) (live : s.ms = none) (after : (X86.step i s).ms = none)
    (regular : isReturn i = false)
    (current : sp s = origin - BitVec.ofNat 64 (stackDepth (s.rip-base).toNat)) :
    sp (X86.step i s) = origin - BitVec.ofNat 64 (stackDepth ((X86.step i s).rip-base).toNat) := by
  let before := BitVec.ofNat 64 (stackDepth (s.rip-base).toNat)
  let beyond := BitVec.ofNat 64 (stackDepth ((X86.step i s).rip-base).toNat)
  have check := List.all_eq_true.mp (List.all_eq_true.mp stackEdges _ (decoded_boundary fetched start)) _
    (fetched_successor fetched live after regular)
  change (decide (before-beyond = 0) && keepsStack i ||
    updates.any (fun p => decide (i = p.1 ∧ before-beyond = p.2))) = true at check
  have effect : sp (X86.step i s) = sp s + (before-beyond) := by
    rcases Bool.or_eq_true_iff.mp check with plain | changed
    · obtain ⟨zero,kept⟩ := Bool.and_eq_true_iff.mp plain
      rw [of_decide_eq_true zero]
      change sp (X86.step i s) = sp s + 0#64
      rw [BitVec.add_zero]
      obtain ⟨form,h⟩ := fetched_scalar fetched
      obtain ⟨op,len⟩ := i
      change op = form.op at h
      subst op
      exact keep_stack form len s live kept
    · obtain ⟨⟨op,d⟩,member,h⟩ := List.any_eq_true.mp changed
      obtain ⟨rfl,hd⟩ := of_decide_eq_true h
      rw [hd]
      exact update_sp member s live
  change sp (X86.step i s) = origin-beyond
  change sp s = origin-before at current
  rw [effect,current,BitVec.sub_eq_add_neg before,← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_eq_add_neg origin]

attribute [local irreducible] X86.step codeLayout starts image

private theorem returnAt_stack {base n s out} (origin : Val) (start : (s.rip-base).toNat ∈ starts)
    (current : sp s = origin - BitVec.ofNat 64 (stackDepth (s.rip-base).toNat))
    (returned : returnAt base n s = some out) :
    ∃ trace, Execution base s trace out ∧ trace.length = n ∧
      stackTrace (trace.map Prod.snd) s =
        trace.map (fun e => origin - BitVec.ofNat 64 (stackDepth (e.1-base).toNat)) := by
  induction n generalizing s with
  | zero => simp [returnAt] at returned
  | succ n ih =>
    have live := returnAt_live returned
    rw [returnAt] at returned
    cases f : fetch base s with
    | none => simp [Cpu.stopped,live,f,guard] at returned
    | some i =>
      have one : stepLoaded base s = some (X86.step i s) := by simp [stepLoaded,Cpu.stopped,live,guard,f]
      cases r : isReturn i with
      | true =>
        cases n with
        | zero =>
          have eq : X86.step i s = out := by simpa [Cpu.stopped,live,f,guard,r] using returned
          subst out
          exact ⟨[(_,i)],.cons f one (.nil _),rfl,by simp [stackTrace,current]⟩
        | succ n => simp [Cpu.stopped,live,f,guard,r] at returned
      | false =>
        have tail : returnAt base n (X86.step i s) = some out := by simpa [Cpu.stopped,live,f,guard,r] using returned
        have next := returnAt_live tail
        obtain ⟨trace,actual,count,slots⟩ := ih (successor_start f live next r start)
          (stack_transition origin f start live next r current) tail
        exact ⟨(_,i)::trace,.cons f one actual,by simp [count],by simp [stackTrace,current,slots]⟩

/-- The actual stack pointer stays within 504 bytes below the entry pointer
at every instruction. Together with the eight-byte return slot this gives the
512-byte stack bound. The exact depth depends only on the decoded RIP. -/
theorem sha256_stack_bound {base s message extent} (entry : CallerEntry base s message extent) :
    ∃ out trace, Execution base s trace out ∧ CallResult s out message ∧ trace.length = callSteps message.bytes.size ∧
      stackTrace (trace.map Prod.snd) s =
        trace.map (fun e => s.regs.get .rsp - BitVec.ofNat 64 (stackDepth (e.1-base).toNat)) ∧
      ∀ p ∈ stackTrace (trace.map Prod.snd) s, ∃ used ≤ 504, p = s.regs.get .rsp - BitVec.ofNat 64 used := by
  obtain ⟨out,returned,result⟩ := sha256_serial _ _ _ _ entry
  obtain ⟨trace,actual,count,slots⟩ := returnAt_stack (s.regs.get .rsp)
    (by simpa [entry.pc] using entry_is_instruction_start) (by simp [entry.pc,sp,stackDepth]) returned
  refine ⟨out,trace,actual,result,count,slots,?_⟩
  rw [slots]
  intro p member
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
  exact ⟨_,depth_bound _,rfl⟩

end Crypto.X86_64
