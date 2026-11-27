import Proofs.HMACSHA256.RISCV64Guard
import Proofs.HMACSHA256.RISCV64Ranges

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private theorem capacity_setup_decoded : decodeRange entry 0x1c 7 = some [
    .scalar ⟨.add 9#5 0#5 10#5, 2⟩,
    .scalar ⟨.add 18#5 0#5 11#5, 2⟩,
    .scalar ⟨.add 19#5 0#5 12#5, 2⟩,
    .scalar ⟨.add 20#5 0#5 13#5, 2⟩,
    .scalar ⟨.addi 10#5 0#5 1#64, 2⟩,
    .scalar ⟨.load .double 5#5 19#5 0#64, 4⟩,
    .scalar ⟨.load .double 6#5 18#5 16#64, 4⟩] := by decide +kernel

def capacityState (s : CPU) : CPU :=
  let saved := (((s.put 9#5 (s.reg 10#5)).put 18#5 (s.reg 11#5)).put 19#5 (s.reg 12#5)).put
    20#5 (s.reg 13#5)
  (((saved.put 10#5 1#64).put 5#5 (s.mem.read64 (s.reg 12#5))).put
    6#5 (s.mem.read64 (s.reg 11#5 + 16#64))).advance 18

set_option maxHeartbeats 1400000 in
theorem entry_capacity_setup (s : CPU) :
    runRange entry 0x1c 7 s = some (capacityState s) := by
  unfold runRange
  rw [capacity_setup_decoded]
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  simp (config := { decide := true }) [List.foldl, runOps, Op.step, Instruction.step, Width.load,
    capacityState, zero]
  simp [CPU.advance, CPU.put, Vector.set_set, BitVec.add_assoc]

theorem entry_capacity_arguments (s : CPU) :
    (capacityState s).reg 5#5 = s.mem.read64 (s.reg 12#5) ∧
    (capacityState s).reg 6#5 = s.mem.read64 (s.reg 11#5 + 16#64) ∧
    (capacityState s).reg 10#5 = 1#64 ∧ (capacityState s).reg 2#5 = s.reg 2#5 ∧
    (capacityState s).mem = s.mem ∧
    (capacityState s).reg 9#5 = s.reg 10#5 ∧ (capacityState s).reg 18#5 = s.reg 11#5 ∧
    (capacityState s).reg 19#5 = s.reg 12#5 ∧ (capacityState s).reg 20#5 = s.reg 13#5 := by
  simp (config := { decide := true }) only [capacityState, reg_advance, reg_put, memory_advance,
    memory_put, if_true, if_false, and_true]

/-- From the decoded entry's argument setup to the capacity branch, the
guard checks the two actual header words and neither modifies memory nor
touches the caller's key. -/
theorem entry_capacity_branch (s : CPU) (capacity count : Addr)
    (sizeAt : s.mem.read64 (s.reg 12#5) = capacity)
    (countAt : s.mem.read64 (s.reg 11#5 + 16#64) = count) :
    ∃ checked out,
      runRange entry 0x1c 7 s = some checked ∧ runGuard checked = some out ∧
      out.mem = s.mem ∧ out.reg 10#5 = 1#64 ∧ out.reg 2#5 = s.reg 2#5 ∧
      out.reg 9#5 = s.reg 10#5 ∧ out.reg 18#5 = s.reg 11#5 ∧
      out.reg 19#5 = s.reg 12#5 ∧ out.reg 20#5 = s.reg 13#5 ∧
      out.pc = if capacity.toNat < 96 + count.toNat then s.pc + 0xf6#64 else s.pc + 34#64 := by
  obtain ⟨cap, len, status, rsp, cells, k, msg, work, mac⟩ := entry_capacity_arguments s
  obtain ⟨out, run, mem, result, sp, k0, msg0, work0, mac0, pc⟩ := runGuard_result (capacityState s)
  refine ⟨capacityState s, out, entry_capacity_setup s, run, mem.trans cells, result.trans status, sp.trans rsp,
    k0.trans k, msg0.trans msg, work0.trans work, mac0.trans mac, ?_⟩
  rw [pc, cap, len, sizeAt, countAt]
  change (if capacity.toNat < 96 + count.toNat then s.pc + 18#64 + 0xe4#64
    else s.pc + 18#64 + 16#64) = _
  simp only [BitVec.add_assoc] <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem entry_capacity_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x1c#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (capacity : (Access.read (s.reg 12#5) .double).permitted s.mem = true)
    (count : (Access.read (s.reg 11#5 + 16#64) .double).permitted s.mem = true) :
    RangeAllowed entry base 0x1c 7 s := by
  have capacityAt : (Access.read ((0 : Addr) + s.reg 12#5) .double).permitted s.mem = true := by
    change (Access.read (0#64 + s.reg 12#5) .double).permitted s.mem = true
    rwa [BitVec.zero_add]
  have countAt : (Access.read ((0 : Addr) + (s.reg 11#5 + 16#64)) .double).permitted s.mem = true := by
    change (Access.read (0#64 + (s.reg 11#5 + 16#64)) .double).permitted s.mem = true
    rwa [BitVec.zero_add]
  refine ⟨_, capacity_setup_decoded, ?_⟩
  hmac_range_permissions pc aligned exec pc pc pc pc

private def guardHead : List Op :=
  [.scalar ⟨.addi 7 0 96, 4⟩, .scalar ⟨.branch .ltu 5 7 0xe0, 4⟩]

private def guardTail : List Op :=
  [.sub 5 5 7, .scalar ⟨.branch .ltu 5 6 0xd8, 4⟩]

private theorem guardHead_decoded : decodeRange entry 0x2e 2 = some guardHead := by decide +kernel
private theorem guardTail_decoded : decodeRange entry 0x36 2 = some guardTail := by decide +kernel

set_option maxRecDepth 8192 in
private theorem guardHead_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x2e#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x2e 2 s := by
  refine ⟨guardHead, guardHead_decoded, ?_⟩
  unfold guardHead
  hmac_range_permissions pc aligned exec pc pc pc pc

set_option maxRecDepth 8192 in
private theorem guardTail_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x36#64)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x36 2 s := by
  refine ⟨guardTail, guardTail_decoded, ?_⟩
  unfold guardTail
  hmac_range_permissions pc aligned exec pc pc pc pc

def capacityEvents (pc scratch message : Addr) : List (List Access) :=
  [[.fetch pc 2], [.fetch (pc + 2#64) 2], [.fetch (pc + 4#64) 2],
   [.fetch (pc + 6#64) 2], [.fetch (pc + 8#64) 2],
   [.fetch (pc + 10#64) 4, .read scratch .double],
   [.fetch (pc + 14#64) 4, .read (message + 16#64) .double]]

set_option maxRecDepth 8192 in
theorem capacity_observes (base : Addr) (s out : CPU)
    (run : runRange entry 0x1c 7 s = some out)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (readonly : RoutineReadOnly entry base s.mem)
    (allowed : RangeAllowed entry base 0x1c 7 s) :
    ProgramExecution base s (capacityEvents s.pc (s.reg 12#5) (s.reg 11#5)) out := by
  have run := (run_range_observes (.inl rfl) run loaded readonly allowed capacity_setup_decoded).1
  have trace : runOpsEvents ((decodeRange entry 0x1c 7).getD []) s =
      capacityEvents s.pc (s.reg 12#5) (s.reg 11#5) := by
    rw [capacity_setup_decoded, Option.getD_some]
    simp (config := {decide := true}) [runOpsEvents, Op.accesses, Op.width, Op.step, Instruction.step,
      Crypto.RISCV64.Op.accesses, Width.load, capacityEvents, BitVec.add_assoc]
  rw [capacity_setup_decoded, Option.getD_some] at trace
  rwa [trace] at run

def guardEvents (pc : Addr) (capacity : Nat) : List (List Access) :=
  [[.fetch pc 4], [.fetch (pc + 4#64) 4]] ++
    if capacity < 96 then [] else [[.fetch (pc + 8#64) 4], [.fetch (pc + 12#64) 4]]

theorem runGuard_observes {base : Addr} {s out : CPU}
    (run : runGuard s = some out)
    (pc : s.pc = routineAddress base entry + 0x2e#64)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (readonly : RoutineReadOnly entry base s.mem)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    ProgramExecution base s (guardEvents s.pc (s.reg 5#5).toNat) out := by
  let mid := runOps guardHead s
  have head : runRange entry 0x2e 2 s = some mid := by
    simp only [runRange, guardHead_decoded, Option.map_some, mid]
  have tail : runRange entry 0x36 2 mid = some (runOps guardTail mid) := by
    simp only [runRange, guardTail_decoded, Option.map_some]
  obtain ⟨limit, checkCapacity, sub, checkCount⟩ := guard_decoded
  have splitRun : runGuard s =
      if mid.pc = s.pc + 8#64 then some (runOps guardTail mid) else some mid := by
    unfold runGuard
    rw [limit, checkCapacity, sub, checkCount]
    rfl
  have front := (run_range_observes (.inl rfl) head loaded readonly
    (guardHead_allowed base s pc aligned exec) guardHead_decoded).1
  have headTrace : runOpsEvents guardHead s = [[.fetch s.pc 4], [.fetch (s.pc + 4#64) 4]] := rfl
  have next : mid.pc = (if (s.reg 5#5).toNat < 96 then s.pc + 0xe4#64 else s.pc + 8#64) := by
    simp (config := {decide := true}) [-BitVec.toNat_add, mid, guardHead, runOps, Op.step,
      Instruction.step, Branch.taken, BitVec.ult, BitVec.add_assoc]
    have z : s.reg 0#5 = 0#64 := reg_zero s
    simp only [z, BitVec.zero_add, show (96#64).toNat = 96 from rfl]
    split
    · rfl
    · simp only [pc_advance, pc_put, BitVec.add_assoc]
      rfl
  by_cases small : (s.reg 5#5).toNat < 96
  · have apart : s.pc + 0xe4#64 ≠ s.pc + 8#64 :=
      fun eq => (by decide : 0xe4#64 ≠ 8#64) ((BitVec.add_right_inj s.pc).mp eq)
    rw [splitRun, next, if_pos small, if_neg apart] at run
    have same := Option.some.inj run
    subst out
    rw [guardEvents, if_pos small, List.append_nil, ← headTrace]
    exact front
  · have reach : mid.pc = s.pc + 8#64 := by simpa only [if_neg small] using next
    rw [splitRun, reach, if_pos rfl] at run
    have same := Option.some.inj run
    subst out
    have midPC : mid.pc = routineAddress base entry + 0x36#64 := by
      rw [reach, pc, BitVec.add_assoc]
      rfl
    have midExec : mid.mem.canExec (routineAddress base entry) entry.image.size = true :=
      (allPerm_eq_of_perm front.perm _ _ _).trans exec
    obtain ⟨nextImage, nextReadOnly⟩ := front.keeps_routine loaded readonly
    have suffix := (run_range_observes (.inl rfl) tail nextImage nextReadOnly
      (guardTail_allowed base mid midPC aligned midExec) guardTail_decoded).1
    have tailTrace : runOpsEvents guardTail mid = [[.fetch (s.pc + 8#64) 4], [.fetch (s.pc + 12#64) 4]] := by
      change [[Access.fetch mid.pc 4], [Access.fetch (mid.pc + 4#64) 4]] = _
      rw [reach, BitVec.add_assoc]
      rfl
    rw [guardEvents, if_neg small, ← headTrace, ← tailTrace]
    exact front.append suffix

theorem runGuard_executes {base : Addr} {s out : CPU}
    (run : runGuard s = some out)
    (pc : s.pc = routineAddress base entry + 0x2e#64)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read8)
    (readonly : RoutineReadOnly entry base s.mem)
    (aligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    ∃ events, ProgramExecution base s events out ∧ events.length ≤ 4 := by
  refine ⟨_, runGuard_observes run pc loaded readonly aligned exec, ?_⟩
  unfold guardEvents
  split <;> simp

end Crypto.HMACSHA256.RISCV64
