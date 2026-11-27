import Proofs.HMACSHA256.RISCV64Pad

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells writeWords writeWords_word writeWords_outside)

private def innerPrefixCode : List Op := [
  .scalar ⟨.load .double 5#5 19#5 0#64, 4⟩,
  .scalar ⟨.addi 5#5 5#5 (-8#64), 2⟩,
  .scalar ⟨.store .double 5#5 19#5 8#64, 4⟩,
  .scalar ⟨.addi 5#5 0#5 24#64, 2⟩,
  .scalar ⟨.store .double 5#5 19#5 16#64, 4⟩]

private def innerTailCode : List Op := [
  .scalar ⟨.load .double 6#5 18#5 16#64, 4⟩,
  .scalar ⟨.addi 5#5 6#5 64#64, 4⟩,
  .scalar ⟨.store .double 5#5 19#5 24#64, 4⟩]

theorem inner_header_decoded :
    decodeRange entry 0x46 8 = some (innerPrefixCode ++ innerTailCode) := by decide +kernel

private def innerHeaderWord (capacity count : Addr) (i : Nat) : Addr :=
  if i = 0 then capacity - 8#64 else if i = 1 then 24#64 else count + 64#64

def innerHeaderState (s : CPU) (count : Addr) : CPU :=
  let scratch := s.reg 19#5
  let m := writeWords s.mem (scratch + 8#64) (innerHeaderWord (s.mem.read64 scratch) count) 3
  setPC ((((s.put 5#5 24#64).put 6#5 count).put 5#5 (count + 64#64)).write m) (s.pc + 28#64)

private def innerPrefixState (s : CPU) (count : Addr) : CPU :=
  let scratch := s.reg 19#5
  setPC ((s.put 5#5 24#64).write (writeWords s.mem (scratch + 8#64)
    (innerHeaderWord (s.mem.read64 scratch) count) 2)) (s.pc + 16#64)

private theorem inner_prefix_exec (s : CPU) (count : Addr) :
    runOps innerPrefixCode s = innerPrefixState s count := by
  simp (config := { decide := true }) [innerPrefixCode, innerPrefixState, runOps, Op.step, Instruction.step,
    Width.load, Width.store, writeWords, innerHeaderWord, setPC, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  simp [CPU.advance, CPU.put, CPU.write, Vector.set_set, BitVec.add_assoc]

private theorem inner_tail_exec (s : CPU) (count : Addr)
    (countAt : s.mem.read64 (s.reg 18#5 + 16#64) = count) :
    runOps innerTailCode s =
      setPC (((s.put 6#5 count).put 5#5 (count + 64#64)).write
        (s.mem.write64 (s.reg 19#5 + 24#64) (count + 64#64))) (s.pc + 12#64) := by
  simp (config := { decide := true }) [innerTailCode, runOps, Op.step, Instruction.step, Width.load,
    Width.store, countAt, setPC, CPU.advance, CPU.put, CPU.write, BitVec.add_assoc]
  simp (config := { decide := true }) [CPU.reg, Vector.getElem_set]

set_option maxHeartbeats 1700000 in
/-- The first two header stores preserve the external message count,
which the entry then combines with the 64-byte ipad prefix. -/
theorem entry_inner_header (s : CPU) (count : Addr)
    (countAt : s.mem.read64 (s.reg 18#5 + 16#64) = count)
    (countOutside : ∀ i : Fin 8, 16 ≤
      (s.reg 18#5 + 16#64 + BitVec.ofNat 64 i.val - (s.reg 19#5 + 8#64)).toNat) :
    runRange entry 0x46 8 s = some (innerHeaderState s count) := by
  let mid := innerPrefixState s count
  have msg : mid.reg 18#5 = s.reg 18#5 := by simp (config := { decide := true }) [mid, innerPrefixState]
  have countAfter : mid.mem.read64 (mid.reg 18#5 + 16#64) = count := by
    rw [msg, ← countAt]
    apply read64_eq_of_cells
    intro i
    exact writeWords_outside _ _ _ 2 _ (countOutside i)
  unfold runRange
  rw [inner_header_decoded]
  have append : runOps (innerPrefixCode ++ innerTailCode) s = runOps innerTailCode mid := by
    simp only [runOps, List.foldl_append]
    exact congrArg (runOps innerTailCode) (inner_prefix_exec s count)
  rw [Option.map_some, append, inner_tail_exec mid count countAfter]
  simp (config := { decide := true }) [mid, innerPrefixState, innerHeaderState, writeWords, innerHeaderWord,
    setPC, CPU.put, CPU.write, BitVec.add_assoc]
  simp (config := { decide := true }) [CPU.reg, Vector.getElem_set]

set_option maxHeartbeats 1200000 in
theorem inner_header_values (s : CPU) (count : Addr) :
    (innerHeaderState s count).mem.read64 (s.reg 19#5 + 8#64) = s.mem.read64 (s.reg 19#5) - 8#64 ∧
    (innerHeaderState s count).mem.read64 (s.reg 19#5 + 16#64) = 24#64 ∧
    (innerHeaderState s count).mem.read64 (s.reg 19#5 + 24#64) = count + 64#64 := by
  simp only [innerHeaderState, setPC_mem, memory_write]
  let word := innerHeaderWord (s.mem.read64 (s.reg 19#5)) count
  let base := s.reg 19#5 + 8#64
  have first := writeWords_word s.mem base word 3 0 (by decide) (by decide)
  have second := writeWords_word s.mem base word 3 1 (by decide) (by decide)
  have third := writeWords_word s.mem base word 3 2 (by decide) (by decide)
  have address0 : base + BitVec.ofNat 64 (8 * 0) = base := BitVec.add_zero _
  have address1 : base + BitVec.ofNat 64 (8 * 1) = s.reg 19#5 + 16#64 := by
    change s.reg 19#5 + 8#64 + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have address2 : base + BitVec.ofNat 64 (8 * 2) = s.reg 19#5 + 24#64 := by
    change s.reg 19#5 + 8#64 + 16#64 = _
    rw [BitVec.add_assoc]
    rfl
  rw [address0] at first
  rw [address1] at second
  rw [address2] at third
  exact ⟨first, second, third⟩

theorem inner_header_outside (s : CPU) (count p : Addr)
    (outside : 24 ≤ (p - (s.reg 19#5 + 8#64)).toNat) :
    (innerHeaderState s count).mem.cells p = s.mem.cells p :=
  writeWords_outside _ _ _ 3 _ outside

theorem inner_mask_decoded : decodeRange entry 0x62 9 = some [
    .lui 28#5 0xd8e000#64,
    .scalar ⟨.addi 28#5 28#5 (-0x727#64), 4⟩,
    .scalar ⟨.slli 28#5 28#5 13#6, 2⟩,
    .scalar ⟨.addi 28#5 28#5 (-0x4e5#64), 4⟩,
    .scalar ⟨.slli 28#5 28#5 13#6, 2⟩,
    .scalar ⟨.addi 28#5 28#5 0x363#64, 4⟩,
    .scalar ⟨.slli 28#5 28#5 12#6, 2⟩,
    .scalar ⟨.addi 28#5 28#5 0x636#64, 4⟩,
    .scalar ⟨.addi 29#5 19#5 32#64, 4⟩] := by decide +kernel

def innerMaskState (s : CPU) : CPU :=
  ((s.put 28#5 0x3636363636363636#64).put 29#5 (s.reg 19#5 + 32#64)).advance 30

theorem entry_ipad_setup (s : CPU) : runRange entry 0x62 9 s = some (innerMaskState s) := by
  unfold runRange
  rw [inner_mask_decoded]
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, innerMaskState, BitVec.add_assoc]
  simp [CPU.advance, CPU.put, Vector.set_set, CPU.reg, BitVec.add_assoc]

theorem copy_setup_decoded : decodeRange entry 0xd0 3 = some [
    .scalar ⟨.load .double 30#5 18#5 8#64, 4⟩,
    .scalar ⟨.add 30#5 30#5 18#5, 2⟩,
    .scalar ⟨.addi 29#5 19#5 96#64, 4⟩] := by decide +kernel

def messageCopyState (s : CPU) : CPU :=
  ((s.put 30#5 (s.mem.read64 (s.reg 18#5 + 8#64) + s.reg 18#5)).put
    29#5 (s.reg 19#5 + 96#64)).advance 10

theorem entry_message_copy_setup (s : CPU) : runRange entry 0xd0 3 s = some (messageCopyState s) := by
  unfold runRange
  rw [copy_setup_decoded]
  simp (config := { decide := true }) [runOps, Op.step, Instruction.step, Width.load, messageCopyState]
  simp [CPU.advance, CPU.put, Vector.set_set, BitVec.add_assoc]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2900000 in
set_option linter.unusedSimpArgs false in
theorem entry_inner_header_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x46#64)
    (codeAligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (capacity : (Access.read (s.reg 19#5) .double).permitted s.mem = true)
    (count : (Access.read (s.reg 18#5 + 16#64) .double).permitted s.mem = true)
    (scratchAligned : (s.reg 19#5).toNat % 8 = 0)
    (scratchWrite : s.mem.canWrite (s.reg 19#5) 32 = true) :
    RangeAllowed entry base 0x46 8 s := by
  refine ⟨_, inner_header_decoded, ?_⟩
  simp only [innerPrefixCode, innerTailCode, List.cons_append, List.nil_append]
  hmac_range_permissions pc codeAligned exec pc pc scratchAligned scratchWrite

set_option maxRecDepth 8192
set_option maxHeartbeats 2900000
set_option linter.unusedSimpArgs false in
theorem entry_ipad_setup_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0x62#64)
    (codeAligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true) :
    RangeAllowed entry base 0x62 9 s := by
  refine ⟨_, inner_mask_decoded, ?_⟩
  hmac_range_permissions pc codeAligned exec pc pc pc pc

set_option linter.unusedSimpArgs false in
theorem entry_message_copy_setup_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base entry + 0xd0#64)
    (codeAligned : (routineAddress base entry).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base entry) entry.image.size = true)
    (offset : (Access.read (s.reg 18#5 + 8#64) .double).permitted s.mem = true) :
    RangeAllowed entry base 0xd0 3 s := by
  refine ⟨_, copy_setup_decoded, ?_⟩
  hmac_range_permissions pc codeAligned exec pc pc pc pc

def innerHeaderEvents (pc scratch msg : Addr) : List (List Access) :=
  [[.fetch pc 4, .read scratch .double], [.fetch (pc + 4#64) 2],
   [.fetch (pc + 6#64) 4, .write (scratch + 8#64) .double], [.fetch (pc + 10#64) 2],
   [.fetch (pc + 12#64) 4, .write (scratch + 16#64) .double],
   [.fetch (pc + 16#64) 4, .read (msg + 16#64) .double], [.fetch (pc + 20#64) 4],
   [.fetch (pc + 24#64) 4, .write (scratch + 24#64) .double]]

private theorem run_events_append (front rest : List Op) (s : CPU) :
    runOpsEvents (front ++ rest) s = runOpsEvents front s ++ runOpsEvents rest (runOps front s) := by
  induction front generalizing s with
  | nil => rfl
  | cons op tail ih =>
    change _ :: runOpsEvents (tail ++ rest) (op.step s) = _
    rw [ih]
    rfl

set_option maxRecDepth 8192 in
private theorem header_prefix_events (s : CPU) :
    runOpsEvents innerPrefixCode s =
      [[.fetch s.pc 4, .read (s.reg 19#5) .double], [.fetch (s.pc + 4#64) 2],
       [.fetch (s.pc + 6#64) 4, .write (s.reg 19#5 + 8#64) .double], [.fetch (s.pc + 10#64) 2],
       [.fetch (s.pc + 12#64) 4, .write (s.reg 19#5 + 16#64) .double]] := by
  simp (config := {decide := true}) [innerPrefixCode, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.load, Width.store, BitVec.add_assoc]

set_option maxRecDepth 8192 in
private theorem header_tail_events (s : CPU) :
    runOpsEvents innerTailCode s =
      [[.fetch s.pc 4, .read (s.reg 18#5 + 16#64) .double], [.fetch (s.pc + 4#64) 4],
       [.fetch (s.pc + 8#64) 4, .write (s.reg 19#5 + 24#64) .double]] := by
  simp (config := {decide := true}) [innerTailCode, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.load, Width.store, BitVec.add_assoc]

set_option maxRecDepth 8192 in
theorem inner_header_events (s : CPU) :
    runOpsEvents ((decodeRange entry 0x46 8).getD []) s = innerHeaderEvents s.pc (s.reg 19#5) (s.reg 18#5) := by
  rw [inner_header_decoded, Option.getD_some, run_events_append, header_prefix_events, header_tail_events,
    inner_prefix_exec s 0#64]
  simp (config := {decide := true}) only [innerPrefixState, setPC_pc, setPC_reg, reg_write, reg_put,
    if_false, BitVec.add_assoc]
  rfl

def innerMaskEvents (pc : Addr) : List (List Access) :=
  [(0, 4), (4, 4), (8, 2), (10, 4), (14, 2), (16, 4), (20, 2), (22, 4), (26, 4)].map
    fun (off, width) => [.fetch (pc + BitVec.ofNat 64 off) width]

theorem inner_mask_events (s : CPU) :
    runOpsEvents ((decodeRange entry 0x62 9).getD []) s = innerMaskEvents s.pc := by
  rw [inner_mask_decoded, Option.getD_some]
  simp (config := {decide := true}) [innerMaskEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, BitVec.add_assoc]

def messageCopySetupEvents (pc msg : Addr) : List (List Access) :=
  [[.fetch pc 4, .read (msg + 8#64) .double], [.fetch (pc + 4#64) 2], [.fetch (pc + 6#64) 4]]

theorem message_copy_setup_events (s : CPU) :
    runOpsEvents ((decodeRange entry 0xd0 3).getD []) s = messageCopySetupEvents s.pc (s.reg 18#5) := by
  rw [copy_setup_decoded, Option.getD_some]
  simp (config := {decide := true}) [messageCopySetupEvents, runOpsEvents, Op.accesses, Op.width,
    Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, Width.load, BitVec.add_assoc]

end Crypto.HMACSHA256.RISCV64
