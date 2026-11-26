import Proofs.X86_64.Observations

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

def DataByte (access : DataAccess) (p : Val) : Prop :=
  ∃ j < access.bytes, p = access.address + BitVec.ofNat 64 j

def ObservedByte (accesses : List DataAccess) (write : Bool) (p : Val) : Prop :=
  ∃ access ∈ accesses, access.write = write ∧ DataByte access p

/-- Each scalar instruction either preserves memory or performs one write.
The chosen value and address are independent of all unobserved memory. -/
inductive MemoryEffect where
  | none
  | write (size : Size) (address value : Val)

def MemoryEffect.apply : MemoryEffect → Mem → Mem
  | .none, m => m
  | .write sz addr value, m => m.writeSize sz addr value

def MemoryEffect.touches : MemoryEffect → Val → Prop
  | .none, _ => False
  | .write sz addr _, p => ∃ j < sz.bytes, p = addr + BitVec.ofNat 64 j


private theorem write_bytes_frame (m : Mem) (a p v : Val) (n : Nat)
    (outside : ∀ j < n, p ≠ a + BitVec.ofNat 64 j) : (m.writeN a v n).read p = m.read p := by
  induction n generalizing m a v with
  | zero => rfl
  | succ n ih =>
    rw [Mem.writeN, ih, Mem.read_write_ne]
    · simpa using outside 0 (Nat.zero_lt_succ n)
    · intro j hj
      simpa [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), Nat.add_comm] using outside (j+1) (by omega)

theorem MemoryEffect.frame (effect : MemoryEffect) (m : Mem) (p : Val)
    (outside : ¬ effect.touches p) : (effect.apply m).read p = m.read p := by
  cases effect with
  | none => rfl
  | write sz addr value =>
    apply write_bytes_frame
    intro j hj eq
    exact outside ⟨j, hj, eq⟩

private def replaceMem (s : Cpu) (m : Mem) : Cpu := {s with mem := m}

@[local simp] private theorem replace_mem (s : Cpu) : replaceMem s s.mem = s := by cases s; rfl
@[local simp] private theorem replace_mem_twice (s : Cpu) (m n : Mem) :
    replaceMem (replaceMem s m) n = replaceMem s n := by cases s; rfl
@[local simp] private theorem replace_cpu (s : Cpu) (m : Mem) :
    (replaceMem s m).mem = m := rfl
@[local simp] private theorem replace_getReg (s : Cpu) (m : Mem) (sz : Size) (r : GPR) (high : Bool) :
    (replaceMem s m).getReg sz r high = s.getReg sz r high := rfl
@[local simp] private theorem replace_flags (s : Cpu) (m : Mem) :
    (replaceMem s m).flags = s.flags := rfl
@[local simp] private theorem replace_regs (s : Cpu) (m : Mem) :
    (replaceMem s m).regs = s.regs := rfl
@[local simp] private theorem replace_pc (s : Cpu) (m : Mem) :
    (replaceMem s m).rip = s.rip := rfl
@[local simp] private theorem replace_stopped (s : Cpu) (m : Mem) :
    (replaceMem s m).stopped = s.stopped := rfl
@[local simp] private theorem replace_addr (s : Cpu) (m : Mem) (ea : Ea) (nr : Val) :
    ea.addr (replaceMem s m) nr = ea.addr s nr := by
  rw [Ea.addr_eq_segBase_add, Ea.addr_eq_segBase_add]
  cases ea.seg with
  | none => rfl
  | some seg => cases seg <;> rfl
@[local simp] private theorem replace_offset (s : Cpu) (m : Mem) (ea : Ea) (nr : Val) :
    ea.offset (replaceMem s m) nr = ea.offset s nr := rfl

@[local simp] private theorem move_pc (s : Cpu) (m : Mem) (p : Val) :
    (replaceMem s m).setRip p = replaceMem (s.setRip p) m := rfl
@[local simp] private theorem halt (s : Cpu) (m : Mem) (e : MsErr) :
    (replaceMem s m).halt e = replaceMem (s.halt e) m := by cases h : s.ms <;> simp [Cpu.halt, replaceMem, h]
@[local simp] private theorem move_checked_pc (s : Cpu) (m : Mem) (p : Val) :
    (replaceMem s m).setRipChecked p = replaceMem (s.setRipChecked p) m := by
  unfold Cpu.setRipChecked
  split <;> first | rfl | exact halt ..
@[local simp] private theorem write_reg (s : Cpu) (m : Mem) (sz : Size) (r : GPR) (v : Val) (h : Bool) :
    (replaceMem s m).setReg sz r v h = replaceMem (s.setReg sz r v h) m := rfl
@[local simp] private theorem set_flags (s : Cpu) (m : Mem) (f : Flags) :
    (replaceMem s m).setFlags f = replaceMem (s.setFlags f) m := rfl
@[local simp] private theorem undef_value (s : Cpu) (m : Mem) :
    (replaceMem s m).undefBit.1 = s.undefBit.1 := rfl
@[local simp] private theorem undef_state (s : Cpu) (m : Mem) :
    (replaceMem s m).undefBit.2 = replaceMem s.undefBit.2 m := rfl

private def operandEffect (s : Cpu) (sz : Size) (nr : Val) (value : Val) : Operand → MemoryEffect
  | .mem ea => .write sz (ea.addr s nr) value
  | _ => .none

@[local simp] private theorem operand_effect (s : Cpu) (m : Mem) (sz : Size) (nr : Val)
    (dst : Operand) (v : Val) :
    (replaceMem s m).writeOperand sz nr dst v =
      replaceMem (s.writeOperand sz nr dst v) ((operandEffect s sz nr v dst).apply m) := by
  cases dst <;> simp [Cpu.writeOperand, operandEffect, MemoryEffect.apply, Cpu.writeMem, replaceMem]
  case mem ea => rw [show ea.addr {s with mem := m} nr = ea.addr s nr from replace_addr ..]
  case reg => rfl
  case imm => cases h : s.ms <;> simp [Cpu.halt, h]

@[local simp] private theorem addr_set_flags (s : Cpu) (f : Flags) (ea : Ea) (nr : Val) :
    ea.addr (s.setFlags f) nr = ea.addr s nr := rfl
@[local simp] private theorem addr_undef (s : Cpu) (ea : Ea) (nr : Val) :
    ea.addr s.undefBit.2 nr = ea.addr s nr := rfl

def ReadsAgree (accesses : List DataAccess) (before after : Mem) : Prop :=
  ∀ p, ObservedByte accesses false p → after.read p = before.read p

private theorem reads_mem (s : Cpu) (m : Mem) (sz : Size) (addr : Val)
    (agree : ∀ j < sz.bytes, m.read (addr + BitVec.ofNat 64 j) = s.mem.read (addr + BitVec.ofNat 64 j)) :
    (replaceMem s m).readMem sz addr = s.readMem sz addr :=
  Mem.readN_congr _ _ _ _ agree

private theorem read_operand (s : Cpu) (m : Mem) (sz : Size) (nr : Val) (src : Operand)
    (agree : ∀ ea, src = .mem ea → (replaceMem s m).readMem sz (ea.addr s nr) = s.readMem sz (ea.addr s nr)) :
    (replaceMem s m).readOperand sz nr src = s.readOperand sz nr src := by
  cases src with
  | mem ea => simpa [Cpu.readOperand] using agree ea rfl
  | reg | imm => rfl

private theorem read_agree_mem {s : Cpu} {m : Mem} {accesses : List DataAccess}
    (agree : ReadsAgree accesses s.mem m) (sz : Size) (addr : Val)
    (present : (⟨false, addr, sz.bytes⟩ : DataAccess) ∈ accesses) :
    (replaceMem s m).readMem sz addr = s.readMem sz addr :=
  reads_mem s m sz addr (fun j hj => agree _ ⟨_, present, rfl, j, hj, rfl⟩)

private theorem read_agree_operand {s : Cpu} {m : Mem} {accesses : List DataAccess}
    (agree : ReadsAgree accesses s.mem m) (sz : Size) (nr : Val) (o : Operand)
    (present : ∀ a ∈ operandAccess s nr false sz o, a ∈ accesses) :
    (replaceMem s m).readOperand sz nr o = s.readOperand sz nr o :=
  read_operand s m sz nr o (fun ea eq => read_agree_mem agree sz _ (present _ (by simp [eq, operandAccess])))

private def Replay (accesses : List DataAccess) (old : Mem) (m : Mem) (original replaced : Cpu) : Prop :=
  ∃ effect : MemoryEffect,
    (∀ p, effect.touches p → ObservedByte accesses true p) ∧
    original.mem = effect.apply old ∧ replaced = replaceMem original (effect.apply m)

private theorem no_store {accesses old m original replaced} (unchanged : (original : Cpu).mem = old)
    (cpu : replaced = replaceMem original m) : Replay accesses old m original replaced :=
  ⟨.none, fun _ h => False.elim h, unchanged, cpu⟩

private theorem store_operand (accesses : List DataAccess) (s addressState : Cpu) (m : Mem)
    (sz : Size) (nr v : Val) (dst : Operand)
    (same : ∀ ea : Ea, ea.addr s nr = ea.addr addressState nr)
    (present : ∀ a ∈ operandAccess addressState nr true sz dst, a ∈ accesses) :
    Replay accesses s.mem m ((s.writeOperand sz nr dst v).setRip nr)
      (((replaceMem s m).writeOperand sz nr dst v).setRip nr) := by
  refine ⟨operandEffect s sz nr v dst, ?_, ?_, by rw [operand_effect, move_pc]⟩
  · intro p h
    cases dst with
    | mem ea =>
      refine ⟨⟨true, ea.addr addressState nr, sz.bytes⟩, present _ (by simp [operandAccess]), rfl, ?_⟩
      simpa [operandEffect, MemoryEffect.touches, DataByte, same] using h
    | reg | imm => exact False.elim h
  · cases dst <;> try rfl
    rename_i value
    cases h : s.ms <;> simp [Cpu.writeOperand, Cpu.halt, h, Cpu.setRip, operandEffect, MemoryEffect.apply]

private theorem store_push (accesses : List DataAccess) (s : Cpu) (m : Mem) (nr v : Val)
    (present : (⟨true, s.regs.get .rsp-8, 8⟩ : DataAccess) ∈ accesses) :
    Replay accesses s.mem m ((s.push .q v).setRip nr) (((replaceMem s m).push .q v).setRip nr) :=
  ⟨.write .q (s.regs.get .rsp-8) v, fun _ h => ⟨_, present, rfl, h⟩, rfl, rfl⟩

@[local simp] private theorem halt_mem (s : Cpu) (e : MsErr) : (s.halt e).mem = s.mem := by
  cases h : s.ms <;> simp [Cpu.halt, h]
@[local simp] private theorem checked_pc_mem (s : Cpu) (p : Val) : (s.setRipChecked p).mem = s.mem := by
  unfold Cpu.setRipChecked
  split <;> simp

set_option maxHeartbeats 3000000 in
theorem scalar_memory_effect (i : Instr) (s : Cpu) (m : Mem) (accesses : List DataAccess)
    (leaf : ScalarLeaf i) (known : dataAccesses i s = some accesses) (agree : ReadsAgree accesses s.mem m) :
    ∃ effect : MemoryEffect, (∀ p, effect.touches p → ObservedByte accesses true p) ∧
      (X86.step i s).mem = effect.apply s.mem ∧
      X86.step i {s with mem := m} = {(X86.step i s) with mem := effect.apply m} := by
  change Replay accesses s.mem m (X86.step i s) (X86.step i (replaceMem s m))
  obtain ⟨form,shape⟩ := leaf
  obtain ⟨op,len⟩ := i
  change op = form.op at shape
  subst op
  by_cases stopped : s.stopped = true
  · rw [X86.step_stopped _ _ stopped, X86.step_stopped _ _ (replace_stopped s m ▸ stopped)]
    exact no_store rfl rfl
  have live := Bool.eq_false_iff.mpr stopped
  cases form
  all_goals try cases ‹BinKind›
  all_goals try cases ‹Bool›
  all_goals simp only [ScalarForm.op, dataAccesses, Option.some.injEq] at known
  all_goals subst accesses
  all_goals simp only [ScalarForm.op, X86.step, replace_stopped, live, Bool.false_eq_true,
    ↓reduceIte, Op.lockIllegal, replace_pc]
  all_goals repeat (rw [read_agree_operand agree _ _ _ (by intro a member; first | simp [member] <;> done | simp [operandAccess] at member)])
  all_goals try
    simp only [Cpu.popValue, replace_regs, replace_flags]
    rw [read_agree_mem agree _ _ (by simp [Size.bytes])]
  all_goals try simp only [replace_flags, replace_offset, replace_regs, replace_getReg,
    undef_value, undef_state, set_flags, write_reg]
  all_goals repeat' first
    | (apply no_store
       · first | rfl | exact halt_mem .. | exact checked_pc_mem ..
       · first | rfl | simp <;> done | simp [replaceMem, Cpu.setReg] <;> done)
    | (apply store_operand _ _ s
       · intro ea
         first | rfl | simp
       · intro a member
         simp [member])
    | (apply store_push; simp)
    | split
  all_goals done

end Crypto.X86_64
