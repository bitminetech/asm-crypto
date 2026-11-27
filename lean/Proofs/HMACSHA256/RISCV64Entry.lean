import Proofs.HMACSHA256.RISCV64FrameTrace
import Proofs.HMACSHA256.RISCV64EntrySetup
import Proofs.HMACSHA256.RISCV64FramePermissions
import Proofs.HMACSHA256.RegionSlice
import Proofs.HMACSHA256.RISCV64EntryCalls
import Proofs.HMACSHA256.RISCV64Finish

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.ARM64.Imported (memoryBytes32 caller_region_contains_offset caller_outside_delta)
open Crypto.Baseline (Region)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells)

set_option maxHeartbeats 1800000 in
/-- The capacity failure path reaches the exact epilogue without invoking
either helper. Its only stores are the prologue's saved register slots. -/
theorem undersized_entry (s : CPU) (capacity count : Addr)
    (size : s.mem.read64 (s.reg 12#5) = capacity)
    (messageLength : s.mem.read64 (s.reg 11#5 + 16#64) = count)
    (metadataOutside : ∀ p, p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64 → ∀ i : Fin 8,
      104 ≤ (p + BitVec.ofNat 64 i.val - (s.reg 2#5 - 176#64 + 64#64)).toNat)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (short : capacity.toNat < 96 + count.toNat) :
    ∃ saved loaded checked out,
      runRange entry 0 14 s = some saved ∧
      runRange entry 0x1c 7 saved = some loaded ∧
      runGuard loaded = some checked ∧ checked.pc = s.pc + 0x112#64 ∧
      runRange entry 0x112 15 checked = some out ∧
      out.reg 10#5 = 1#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ p, 104 ≤ (p - (s.reg 2#5 - 176#64 + 64#64)).toNat → out.mem.cells p = s.mem.cells p) := by
  let save := enteredFrame .entry s
  have beforeRegs (reg : Reg) (other : reg ≠ 2#5) : save.reg reg = s.reg reg :=
    enteredFrame_reg _ _ _ other
  have fixed (p : Addr) (h : p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64) :
      save.mem.read64 p = s.mem.read64 p := by
    apply read64_eq_of_cells
    intro i
    exact enteredFrame_outside .entry s _ (metadataOutside p h i)
  have capacityAt : save.mem.read64 (save.reg 12#5) = capacity := by
    rw [beforeRegs _ (by decide), fixed _ (.inl rfl)]
    exact size
  have lengthAt : save.mem.read64 (save.reg 11#5 + 16#64) = count := by
    rw [beforeRegs _ (by decide), fixed _ (.inr rfl)]
    exact messageLength
  obtain ⟨loaded, checked, loads, guard, memory, status, stack, _, _, _, _, branch⟩ :=
    entry_capacity_branch save capacity count capacityAt lengthAt
  have reach : checked.pc = s.pc + 0x112#64 := by
    rw [branch, if_pos short, enteredFrame_pc, BitVec.add_assoc]
    rfl
  obtain ⟨sp, link, regs⟩ := epilogue_restores .entry s checked stack returnAligned
    (fun _ => congrArg (fun m : Memory => m.cells _) memory)
  have outStatus : (restoredFrame .entry checked).reg 10#5 = 1#64 := by
    have other : ∀ slot ∈ frameSlots, slot.register ≠ 10#5 := by decide +kernel
    rw [returned_other_register _ _ _ (by decide) other]
    exact status
  refine ⟨save, loaded, checked, restoredFrame .entry checked, enter_frame .entry s, loads, guard, reach,
    return_frame .entry checked, outStatus, sp, link, regs, ?_⟩
  intro p outside
  rw [restoredFrame_memory, memory]
  exact enteredFrame_outside .entry s p outside

/-- After the public capacity test succeeds, the actual direct call enters
the key helper with the original key pointer and the caller's stack K0 block. -/
theorem successful_key_setup (base : Addr) (s : CPU) (capacity count : Addr)
    (pc : s.pc = routineAddress base entry + 0x1c#64)
    (size : s.mem.read64 (s.reg 12#5) = capacity)
    (messageLength : s.mem.read64 (s.reg 11#5 + 16#64) = count)
    (enough : 96 + count.toNat ≤ capacity.toNat) :
    ∃ loaded checked called,
      runRange entry 0x1c 7 s = some loaded ∧ runGuard loaded = some checked ∧
      runRange entry 0x3e 3 checked = some called ∧
      called.pc = routineAddress base key ∧ called.reg 1#5 = routineAddress base entry + 0x46#64 ∧
      called.reg 10#5 = s.reg 10#5 ∧ called.reg 11#5 = s.reg 2#5 ∧ called.reg 2#5 = s.reg 2#5 ∧
      called.mem = s.mem ∧ checked.pc = routineAddress base entry + 0x3e#64 ∧
      checked.reg 18#5 = s.reg 11#5 ∧ checked.reg 19#5 = s.reg 12#5 ∧ checked.reg 20#5 = s.reg 13#5 := by
  obtain ⟨loaded, checked, setup, guard, mem, _, sp, keyAddr, msg, scratch, mac, branch⟩ :=
    entry_capacity_branch s capacity count size messageLength
  have branchEq : checked.pc = routineAddress base entry + 0x3e#64 := by
    rw [branch, if_neg (by omega), pc, BitVec.add_assoc]
    rfl
  obtain ⟨arg0, arg1, stack, link, callsMem⟩ := entry_key_arguments checked
  refine ⟨loaded, checked, entryKeyCall checked, setup, guard, entry_key_call checked,
    entry_key_target base checked branchEq, ?_, arg0.trans keyAddr, arg1.trans sp, stack.trans sp,
    callsMem.trans mem, branchEq, msg, scratch, mac⟩
  rw [link, branchEq, BitVec.add_assoc]
  rfl

set_option maxHeartbeats 1500000 in
/-- Return success through the decoded status instruction and native epilogue. -/
theorem entry_success_return (s finished : CPU)
    (stack : finished.reg 2#5 = s.reg 2#5 - 176#64)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (saved : ∀ i : Fin 104,
      let p := finished.reg 2#5 + BitVec.ofNat 64 (64 + i.val)
      finished.mem.cells p = (enteredFrame .entry s).mem.cells p) :
    ∃ status out, runRange entry 0x110 1 finished = some status ∧
      status.pc = finished.pc + 2#64 ∧ status.reg 2#5 = finished.reg 2#5 ∧
      runRange entry 0x112 15 status = some out ∧ out.reg 10#5 = 0#64 ∧
      out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      out.mem = finished.mem := by
  let status := (finished.advance 2).put 10#5 0#64
  have statusStack : status.reg 2#5 = finished.reg 2#5 := by
    simp (config := { decide := true }) only [status, reg_put, reg_advance, if_false]
  have stackReady : status.reg 2#5 = (enteredFrame .entry s).reg 2#5 :=
    (statusStack.trans stack).trans (enteredFrame_sp .entry s).symm
  have statusMemory : status.mem = finished.mem := rfl
  have ready (i : Fin 104) :
      let p := status.reg 2#5 + BitVec.ofNat 64 (HmacRoutine.savedOffset .entry + i.val)
      status.mem.cells p = (enteredFrame .entry s).mem.cells p := by
    dsimp only
    rw [statusStack, statusMemory]
    exact saved i
  obtain ⟨rsp, address, savedRegisters⟩ := epilogue_restores .entry s status stackReady returnAligned ready
  refine ⟨status, restoredFrame .entry status, entry_ok finished, rfl, statusStack,
    return_frame .entry status, ?_, rsp, address, savedRegisters,
    (restoredFrame_memory _ _).trans statusMemory⟩
  have preserved : ∀ slot ∈ frameSlots, slot.register ≠ 10#5 := by decide +kernel
  rw [returned_other_register _ _ _ (by decide) preserved]
  simp (config := { decide := true }) only [status, reg_put, if_true, if_false]

set_option maxHeartbeats 2100000 in
/-- Compose the linked finishing helper with the successful entry return.
The earlier entry stages provide the prepared list and the original MAC
pointer. The save-area premise is the entry's separate frame obligation. -/
theorem successful_return_after_inner {base : Addr} {s prepared bodyOut : CPU}
    (inputKey message : ByteList) (capacity : Nat)
    (pc : prepared.pc = routineAddress base entry + 0x104#64)
    (stack : prepared.reg 2#5 = (enteredFrame .entry s).reg 2#5)
    (mac : prepared.reg 20#5 = s.reg 13#5)
    (body : FinishBody base (enteredFrame .finish (entryFinishCall prepared)) bodyOut
      (hmacInner message (hmacKey inputKey) capacity) (hmacKey inputKey))
    (stackAvailable : 720 ≤ ((entryFinishCall prepared).reg 2#5).toNat)
    (callAligned : ((entryFinishCall prepared).reg 1#5).toNat % 2 = 0)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (macOffSaves : ∀ i : Fin 104, ¬ (⟨(entryFinishCall prepared).reg 12#5, 32⟩ : Region).Contains
      ((enteredFrame .finish (entryFinishCall prepared)).reg 2#5 + BitVec.ofNat 64 (128 + i.val)))
    (saved : ∀ i : Fin 104,
      let p := prepared.reg 2#5 + BitVec.ofNat 64 (64 + i.val)
      bodyOut.mem.cells p = (enteredFrame .entry s).mem.cells p) :
    ∃ finished status out,
      runRange entry 0x104 4 prepared = some (entryFinishCall prepared) ∧
      runRange finish 0 14 (entryFinishCall prepared) =
        some (enteredFrame .finish (entryFinishCall prepared)) ∧
      runRange finish 0xbc 15 bodyOut = some finished ∧ finished.pc = routineAddress base entry + 0x110#64 ∧
      runRange entry 0x110 1 finished = some status ∧ runRange entry 0x112 15 status = some out ∧
      out.reg 10#5 = 0#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 out.mem (s.reg 13#5) =
        (EthLib.Cryptography.Hash.Hmac.hmac32 inputKey.bytes message.bytes).map UInt8.toBitVec := by
  obtain ⟨finished, prologue, ret, stackOut, link, _, digest⟩ :=
    body.returned stackAvailable callAligned macOffSaves
  obtain ⟨_, _, outPtr, stackCall, retPC, _⟩ := entry_finish_arguments prepared
  have returned : finished.pc = routineAddress base entry + 0x110#64 := by
    rw [link, retPC, pc, BitVec.add_assoc]
    rfl
  have same := Option.some.inj (ret.symm.trans (return_frame .finish bodyOut))
  have cells : finished.mem = bodyOut.mem := by
    rw [same, restoredFrame_memory]
  have finishedStack : finished.reg 2#5 = s.reg 2#5 - 176#64 :=
    stackOut.trans (stackCall.trans (stack.trans (enteredFrame_sp .entry s)))
  obtain ⟨status, out, setStatus, _, _, leave, ok, rsp, address, registers, memory⟩ :=
    entry_success_return s finished finishedStack returnAligned (by
      intro i
      dsimp only
      rw [stackOut, stackCall, cells]
      exact saved i)
  refine ⟨finished, status, out, entry_finish_call prepared, prologue, ret, returned,
    setStatus, leave, ok, rsp, address, registers, ?_⟩
  rw [memory, ← mac, ← outPtr, ← hmacFinish_hmacInner inputKey message capacity]
  exact digest

set_option maxRecDepth 8192 in
def entryFrontEvents (base : Addr) (s : CPU) (capacity : Addr) : List (List Access) :=
  let text := routineAddress base entry
  prologueEvents .entry s.pc (s.reg 2#5) ++
    capacityEvents (text + 0x1c#64) (s.reg 12#5) (s.reg 11#5) ++ guardEvents (text + 0x2e#64) capacity.toNat

def entryBeforeKeyEvents (base : Addr) (s : CPU) (capacity : Addr) : List (List Access) :=
  let pc := routineAddress base entry + 0x3e#64
  entryFrontEvents base s capacity ++ [[.fetch pc 2], [.fetch (pc + 2#64) 2], [.fetch (pc + 4#64) 4]]

def entryReturnEvents (base : Addr) (s : CPU) : List (List Access) :=
  epilogueEvents .entry (routineAddress base entry + 0x112#64) (s.reg 2#5 - 176#64)

def entrySmallEvents (base : Addr) (s : CPU) (capacity : Addr) : List (List Access) :=
  entryFrontEvents base s capacity ++ entryReturnEvents base s

def entrySuccessReturnEvents (base : Addr) (s : CPU) : List (List Access) :=
  [[.fetch (routineAddress base entry + 0x110#64) 2]] ++ entryReturnEvents base s

theorem entry_finish_call_events (s : CPU) :
    runOpsEvents ((decodeRange entry 0x104 4).getD []) s =
      [[.fetch s.pc 4], [.fetch (s.pc + 4#64) 2], [.fetch (s.pc + 6#64) 2], [.fetch (s.pc + 8#64) 4]] := by
  rw [entry_finish_call_decoded, Option.getD_some]
  simp (config := {decide := true}) [runOpsEvents, Op.accesses, Op.width, Crypto.RISCV64.Op.accesses,
    Op.step, Instruction.step, BitVec.add_assoc]

set_option maxHeartbeats 2900000 in
/-- Fetch the prologue and the public capacity test on either branch. -/
theorem entry_prefix_fetched (base : Addr) (s saved prepared checked : CPU) (capacity : Addr)
    (pc : s.pc = routineAddress base entry)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (stackAligned : (s.reg 2#5 - 176#64).toNat % 8 = 0)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 176#64) 176 = true)
    (capacityRead : (Access.read (s.reg 12#5) .double).permitted s.mem = true)
    (countRead : (Access.read (s.reg 11#5 + 16#64) .double).permitted s.mem = true)
    (enter : runRange entry 0 14 s = some saved)
    (setup : runRange entry 0x1c 7 saved = some prepared)
    (guard : runGuard prepared = some checked) (capacityAt : prepared.reg 5#5 = capacity) :
    ProgramExecution base s (entryFrontEvents base s capacity) checked ∧
      (entryFrontEvents base s capacity).length ≤ 25 := by
  have savedEq : saved = enteredFrame .entry s :=
    Option.some.inj (enter.symm.trans (enter_frame .entry s))
  have setupEq : prepared = capacityState saved :=
    Option.some.inj (setup.symm.trans (entry_capacity_setup saved))
  have capAddr : saved.reg 12#5 = s.reg 12#5 := by
    rw [savedEq]
    exact enteredFrame_reg .entry s 12#5 (by decide)
  have msgAddr : saved.reg 11#5 = s.reg 11#5 := by
    rw [savedEq]
    exact enteredFrame_reg .entry s 11#5 (by decide)
  have savedPC : saved.pc = routineAddress base entry + 0x1c#64 := by
    rw [savedEq, enteredFrame_pc, pc]
  have setupPC : prepared.pc = routineAddress base entry + 0x2e#64 := by
    rw [setupEq]
    change saved.pc + 18#64 = _
    rw [savedPC, BitVec.add_assoc]
    rfl
  have readonly : RoutineReadOnly entry base s.mem := routine_readonly_of_exec exec
  have belongs : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨pro, na⟩ := run_range_observes belongs enter loaded readonly
    (frame_prologue_allowed .entry base s pc aligned exec stackAligned stackWrite) (entered_decoded .entry)
  obtain ⟨imageA, roA⟩ := pro.keeps_routine loaded readonly
  have keepsExec {final events} (execution : ProgramExecution base s events final) :
      final.mem.canExec (routineAddress base entry) entry.image.size = true :=
    (allPerm_eq_of_perm execution.perm _ _ _).trans exec
  have capOk : (Access.read (saved.reg 12#5) .double).permitted saved.mem = true := by
    rw [capAddr]
    simp only [Access.permitted, Bool.and_eq_true] at capacityRead ⊢
    exact ⟨capacityRead.1, (pro.permissions _ _).2 capacityRead.2⟩
  have msgOk : (Access.read (saved.reg 11#5 + 16#64) .double).permitted saved.mem = true := by
    rw [msgAddr]
    simp only [Access.permitted, Bool.and_eq_true] at countRead ⊢
    exact ⟨countRead.1, (pro.permissions _ _).2 countRead.2⟩
  have prepare := capacity_observes base saved prepared setup imageA roA
    (entry_capacity_allowed base saved savedPC aligned (keepsExec pro) capOk msgOk)
  have throughSetup := pro.append prepare
  obtain ⟨imageB, roB⟩ := throughSetup.keeps_routine loaded readonly
  have guardRun := runGuard_observes guard setupPC imageB roB aligned (keepsExec throughSetup)
  have throughGuard := throughSetup.append guardRun
  rw [enter_events, savedPC, capAddr, msgAddr, setupPC, capacityAt, List.append_assoc] at throughGuard
  rw [enter_events] at na
  refine ⟨throughGuard, ?_⟩
  simp only [entryFrontEvents, List.length_append, na, capacityEvents, List.length_cons, List.length_nil]
  have n : (guardEvents (routineAddress base entry + 0x2e#64) capacity.toNat).length ≤ 4 := by
    unfold guardEvents
    split <;> simp
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
/-- The success branch reaches the exact linked key helper. Its prologue
writes only the public entry's ABI save slots. -/
theorem entry_before_key_fetched (base : Addr) (s : CPU) (capacity count : Addr)
    (pc : s.pc = routineAddress base entry)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (stackAligned : (s.reg 2#5 - 176#64).toNat % 8 = 0)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 176#64) 176 = true)
    (capacityRead : (Access.read (s.reg 12#5) .double).permitted s.mem = true)
    (countRead : (Access.read (s.reg 11#5 + 16#64) .double).permitted s.mem = true)
    (size : s.mem.read64 (s.reg 12#5) = capacity)
    (messageLength : s.mem.read64 (s.reg 11#5 + 16#64) = count)
    (metadataOutside : ∀ p, p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64 → ∀ i : Fin 8,
      104 ≤ (p + BitVec.ofNat 64 i.val - (s.reg 2#5 - 176#64 + 64#64)).toNat)
    (enough : 96 + count.toNat ≤ capacity.toNat) :
    ∃ called, ProgramExecution base s (entryBeforeKeyEvents base s capacity) called ∧
      (entryBeforeKeyEvents base s capacity).length ≤ 28 ∧
      called.pc = routineAddress base key ∧ called.reg 1#5 = routineAddress base entry + 0x46#64 ∧
      called.reg 10#5 = s.reg 10#5 ∧ called.reg 11#5 = s.reg 2#5 - 176#64 ∧
      called.reg 2#5 = s.reg 2#5 - 176#64 ∧ called.mem = (enteredFrame .entry s).mem ∧
      called.reg 18#5 = s.reg 11#5 ∧ called.reg 19#5 = s.reg 12#5 ∧
      called.reg 20#5 = s.reg 13#5 := by
  let saved := enteredFrame .entry s
  have original (r : Reg) (other : r ≠ 2#5) : saved.reg r = s.reg r :=
    enteredFrame_reg .entry s r other
  have preserved (p : Addr) (which : p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64) :
      saved.mem.read64 p = s.mem.read64 p := by
    apply read64_eq_of_cells
    intro i
    exact enteredFrame_outside .entry s _ (metadataOutside p which i)
  have capacityValue : saved.mem.read64 (saved.reg 12#5) = capacity := by
    rw [original _ (by decide), preserved _ (.inl rfl)]
    exact size
  have countValue : saved.mem.read64 (saved.reg 11#5 + 16#64) = count := by
    rw [original _ (by decide), preserved _ (.inr rfl)]
    exact messageLength
  have savedPC : saved.pc = routineAddress base entry + 0x1c#64 := by
    rw [enteredFrame_pc, pc]
  obtain ⟨setup, checked, called, setupRun, guard, call, target, link, input, output, stack,
    memory, checkedPC, msg, scratch, mac⟩ :=
    successful_key_setup base saved capacity count savedPC capacityValue countValue enough
  have setupCap : setup.reg 5#5 = capacity := by
    have same := Option.some.inj (setupRun.symm.trans (entry_capacity_setup saved))
    rw [same, (entry_capacity_arguments saved).1]
    exact capacityValue
  obtain ⟨throughTest, na⟩ := entry_prefix_fetched base s saved setup checked capacity pc loaded aligned exec
    stackAligned stackWrite capacityRead countRead (enter_frame .entry s) setupRun guard setupCap
  have belongs : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  obtain ⟨image, readonly⟩ := throughTest.keeps_routine loaded (routine_readonly_of_exec exec)
  obtain ⟨throughCall, nb⟩ := run_range_observes belongs call image readonly
    (entry_key_call_allowed base checked checkedPC aligned
      ((allPerm_eq_of_perm throughTest.perm _ _ _).trans exec)) entry_key_call_decoded
  have callTrace : runOpsEvents ((decodeRange entry 0x3e 3).getD []) checked =
      [[.fetch checked.pc 2], [.fetch (checked.pc + 2#64) 2], [.fetch (checked.pc + 4#64) 4]] := by
    rw [entry_key_call_decoded, Option.getD_some]
    simp (config := {decide := true}) [runOpsEvents, Op.accesses, Op.width, Crypto.RISCV64.Op.accesses,
      Op.step, Instruction.step, BitVec.add_assoc]
  rw [entry_key_call_decoded, Option.getD_some, checkedPC] at callTrace
  rw [callTrace] at throughCall
  have calledEq : called = entryKeyCall checked :=
    Option.some.inj (call.symm.trans (entry_key_call checked))
  have savedSP : saved.reg 2#5 = s.reg 2#5 - 176#64 := enteredFrame_sp .entry s
  refine ⟨called, throughTest.append throughCall, ?_, target, link,
    input.trans (original _ (by decide)), output.trans savedSP, stack.trans savedSP,
    memory, ?_, ?_, ?_⟩
  · simp only [entryBeforeKeyEvents, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [calledEq]
    simpa (config := { decide := true }) only [entryKeyCall, setPC_reg, reg_put, if_false] using
      msg.trans (original _ (by decide))
  · rw [calledEq]
    simpa (config := { decide := true }) only [entryKeyCall, setPC_reg, reg_put, if_false] using
      scratch.trans (original _ (by decide))
  · rw [calledEq]
    simpa (config := { decide := true }) only [entryKeyCall, setPC_reg, reg_put, if_false] using
      mac.trans (original _ (by decide))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2900000 in
/-- The linked entry returns BUFFER_TOO_SMALL using the public header words.
Every fetch and data access is checked against the caller's grants. All
cells outside the reserved entry frame are preserved on this path. -/
theorem undersized_entry_fetched (base : Addr) (s : CPU) (capacity count : Addr)
    (pc : s.pc = routineAddress base entry)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (stackAvailable : 176 ≤ (s.reg 2#5).toNat)
    (stackAligned : (s.reg 2#5 - 176#64).toNat % 8 = 0)
    (stackRead : s.mem.canRead (s.reg 2#5 - 176#64) 176 = true)
    (stackWrite : s.mem.canWrite (s.reg 2#5 - 176#64) 176 = true)
    (capacityRead : (Access.read (s.reg 12#5) .double).permitted s.mem = true)
    (countRead : (Access.read (s.reg 11#5 + 16#64) .double).permitted s.mem = true)
    (size : s.mem.read64 (s.reg 12#5) = capacity)
    (messageLength : s.mem.read64 (s.reg 11#5 + 16#64) = count)
    (metadataSeparate : ∀ p, p = s.reg 12#5 ∨ p = s.reg 11#5 + 16#64 → ∀ i : Fin 8,
      ¬ (⟨s.reg 2#5 - 176#64, 176⟩ : Region).Contains (p + BitVec.ofNat 64 i.val))
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (short : capacity.toNat < 96 + count.toNat) :
    ∃ out, ProgramExecution base s (entrySmallEvents base s capacity) out ∧
      (entrySmallEvents base s capacity).length ≤ 40 ∧
      out.reg 10#5 = 1#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ p, ¬ (⟨s.reg 2#5 - 176#64, 176⟩ : Region).Contains p → out.mem.cells p = s.mem.cells p) := by
  let frame : Region := ⟨s.reg 2#5 - 176#64, 176⟩
  let slots := regionSlice frame 64 104
  have frameValid : frame.Valid := by
    change (s.reg 2#5 - 176#64).toNat + 176 ≤ 2 ^ 64
    rw [BitVec.toNat_sub]
    change (2 ^ 64 - 176 + (s.reg 2#5).toNat) % 2 ^ 64 + 176 ≤ 2 ^ 64
    have limit := (s.reg 2#5).isLt
    omega
  have fit : 64 + 104 ≤ frame.bytes := by change 64 + 104 ≤ 176; decide
  have slotValid : slots.Valid := regionSlice_valid frame 64 104 frameValid fit
  have away (p : Addr) (outside : ¬ frame.Contains p) :
      104 ≤ (p - (s.reg 2#5 - 176#64 + 64#64)).toNat :=
    caller_outside_delta slots slotValid p
      (fun inside => outside (regionSlice_inside frame 64 104 frameValid fit p inside))
  obtain ⟨saved, setup, checked, out, enter, prepareEntry, guard, atReturn, leave,
    status, restoredSP, link, regs, frameOut⟩ := undersized_entry s capacity count size messageLength
      (fun p addr i => away _ (metadataSeparate p addr i)) returnAligned short
  have setupEq : setup = capacityState saved :=
    Option.some.inj (prepareEntry.symm.trans (entry_capacity_setup saved))
  have savedEq : saved = enteredFrame .entry s :=
    Option.some.inj (enter.symm.trans (enter_frame .entry s))
  have checkedSP : checked.reg 2#5 = s.reg 2#5 - 176#64 := by
    obtain ⟨actual, run, _, _, stack, _⟩ := runGuard_result setup
    have eq : checked = actual := Option.some.inj (guard.symm.trans run)
    rw [eq, stack, setupEq, (entry_capacity_arguments saved).2.2.2.1, savedEq]
    exact enteredFrame_sp .entry s
  have readonly : RoutineReadOnly entry base s.mem := routine_readonly_of_exec exec
  have belongs : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  have setupCap : setup.reg 5#5 = capacity := by
    rw [setupEq, (entry_capacity_arguments saved).1, savedEq, enteredFrame_reg .entry s 12#5 (by decide)]
    rw [← size]
    apply read64_eq_of_cells
    intro i
    exact enteredFrame_outside .entry s _ (away _ (metadataSeparate _ (.inl rfl) i))
  obtain ⟨throughGuard, steps⟩ := entry_prefix_fetched base s saved setup checked capacity pc
    loaded aligned exec stackAligned stackWrite capacityRead countRead enter prepareEntry guard setupCap
  obtain ⟨imageC, roC⟩ := throughGuard.keeps_routine loaded readonly
  have savedRead : checked.mem.canRead (checked.reg 2#5) 176 = true := by
    rw [checkedSP]
    exact (throughGuard.permissions _ _).2 stackRead
  have retAllowed := frame_epilogue_allowed .entry base checked (pc ▸ atReturn)
    aligned ((allPerm_eq_of_perm throughGuard.perm _ _ _).trans exec)
    (checkedSP.symm ▸ stackAligned) savedRead
  obtain ⟨ret, nd⟩ := run_range_observes belongs leave imageC roC retAllowed (returned_decoded .entry)
  have atPC : checked.pc = routineAddress base entry + 0x112#64 := by rw [atReturn, pc]
  rw [return_events, atPC, checkedSP] at ret nd
  refine ⟨out, throughGuard.append ret, ?_, status, restoredSP, link, regs,
    fun p outside => frameOut p (away p outside)⟩
  simp only [entrySmallEvents, List.length_append, entryReturnEvents, nd]
  omega

set_option maxHeartbeats 1750000 in
/-- Check the precise fetches and the save-slot reads after the finish helper. -/
theorem entry_success_return_fetched (base : Addr) (s finished : CPU)
    (pc : finished.pc = routineAddress base entry + 0x110#64)
    (loaded : entry.Loaded (routineAddress base entry) finished.mem.read8)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : finished.mem.canExec (routineAddress base entry) entry.image.size = true)
    (stack : finished.reg 2#5 = s.reg 2#5 - 176#64)
    (stackAligned : (finished.reg 2#5).toNat % 8 = 0)
    (stackRead : finished.mem.canRead (finished.reg 2#5) 176 = true)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0)
    (saved : ∀ i : Fin 104,
      let p := finished.reg 2#5 + BitVec.ofNat 64 (64 + i.val)
      finished.mem.cells p = (enteredFrame .entry s).mem.cells p) :
    ∃ out, ProgramExecution base finished (entrySuccessReturnEvents base s) out ∧
      (entrySuccessReturnEvents base s).length = 16 ∧
      out.reg 10#5 = 0#64 ∧ out.reg 2#5 = s.reg 2#5 ∧ out.pc = s.reg 1#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      out.mem = finished.mem := by
  obtain ⟨status, out, setStatus, statusPC, statusSP, ret, ok, rsp, link, regs, memory⟩ :=
    entry_success_return s finished stack returnAligned saved
  have belongs : entry = entry ∨ entry = key ∨ entry = finish := .inl rfl
  have readonly : RoutineReadOnly entry base finished.mem := routine_readonly_of_exec exec
  obtain ⟨setOk, na⟩ := run_range_observes belongs setStatus loaded readonly
    (entry_ok_allowed base finished pc aligned exec) ok_decoded
  obtain ⟨next, nextReadOnly⟩ := setOk.keeps_routine loaded readonly
  have returnPC : status.pc = routineAddress base (HmacRoutine.entry.image) +
      BitVec.ofNat 64 HmacRoutine.entry.returnOffset := by
    rw [statusPC, pc, BitVec.add_assoc]
    rfl
  have readable : status.mem.canRead (status.reg 2#5) 176 = true := by
    rw [statusSP]
    exact (setOk.permissions _ _).2 stackRead
  obtain ⟨returned, nb⟩ := run_range_observes belongs ret next nextReadOnly
    (frame_epilogue_allowed .entry base status returnPC aligned
      ((allPerm_eq_of_perm setOk.perm _ _ _).trans exec) (statusSP.symm ▸ stackAligned) readable)
    (returned_decoded .entry)
  have first : runOpsEvents [.scalar ⟨.addi 10#5 0#5 0#64, 2⟩] finished =
      [[.fetch (routineAddress base entry + 0x110#64) 2]] := by
    change [[Access.fetch finished.pc 2]] = _
    rw [pc]
  rw [first] at setOk
  rw [return_events, returnPC, statusSP, stack] at returned nb
  have length : (entryReturnEvents base s).length = 15 := nb
  exact ⟨out, setOk.append returned, by
    simp only [entrySuccessReturnEvents, List.length_append, List.length_cons, List.length_nil, length],
    ok, rsp, link, regs, memory⟩

end Crypto.HMACSHA256.RISCV64
