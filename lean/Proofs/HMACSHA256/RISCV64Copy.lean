import Proofs.HMACSHA256.RISCV64Ranges

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private def wordCode : List Op := [
  .scalar ⟨.addi 31#5 0#5 8#64, 2⟩,
  .scalar ⟨.branch .ltu 6#5 31#5 20#64, 4⟩,
  .scalar ⟨.load .double 31#5 30#5 0#64, 4⟩,
  .scalar ⟨.store .double 31#5 29#5 0#64, 4⟩,
  .scalar ⟨.addi 30#5 30#5 8#64, 2⟩,
  .scalar ⟨.addi 29#5 29#5 8#64, 2⟩,
  .scalar ⟨.addi 6#5 6#5 (-8#64), 2⟩,
  .scalar ⟨.jump (-20#64), 2⟩]

private def byteCode : List Op := [
  .scalar ⟨.branch .eq 6#5 0#5 20#64, 4⟩,
  .scalar ⟨.load .byte 31#5 30#5 0#64, 4⟩,
  .scalar ⟨.store .byte 31#5 29#5 0#64, 4⟩,
  .scalar ⟨.addi 30#5 30#5 1#64, 2⟩,
  .scalar ⟨.addi 29#5 29#5 1#64, 2⟩,
  .scalar ⟨.addi 6#5 6#5 (-1#64), 2⟩,
  .scalar ⟨.jump (-18#64), 2⟩]

/-- A loop cycle is selected from the actual count. Only the taken
instructions are executed, including on the zero-count path. -/
def runWordCycle (routine : Routine) (off : Nat) (s : CPU) : Option CPU := do
  let first ← decodeRange routine off 2
  let checked := runOps first s
  if checked.pc = s.pc + 6#64 then
    return runOps (← decodeRange routine (off + 6) 6) checked
  else
    return checked

def runByteCycle (routine : Routine) (off : Nat) (s : CPU) : Option CPU := do
  let first ← decodeRange routine off 1
  let checked := runOps first s
  if checked.pc = s.pc + 4#64 then
    return runOps (← decodeRange routine (off + 4) 6) checked
  else
    return checked

private theorem word_fragments :
    (decodeRange entry 0xda 2 = some (wordCode.take 2) ∧
      decodeRange entry 0xe0 6 = some (wordCode.drop 2)) ∧
    (decodeRange key 0x54 2 = some (wordCode.take 2) ∧
      decodeRange key 0x5a 6 = some (wordCode.drop 2)) := by decide +kernel

private theorem byte_fragments :
    (decodeRange entry 0xf0 1 = some (byteCode.take 1) ∧
      decodeRange entry 0xf4 6 = some (byteCode.drop 1)) ∧
    (decodeRange key 0x6a 1 = some (byteCode.take 1) ∧
      decodeRange key 0x6e 6 = some (byteCode.drop 1)) := by decide +kernel

def advanceCopy (s : CPU) (value distance : Addr) (memory : Memory) : CPU :=
  let st := s.put 31#5 value
  let st := st.put 30#5 (s.reg 30#5 + distance)
  let st := st.put 29#5 (s.reg 29#5 + distance)
  let st := st.put 6#5 (s.reg 6#5 - distance)
  st.write memory

def wordCopy (s : CPU) : CPU :=
  let value := s.mem.read64 (s.reg 30#5)
  advanceCopy s value 8#64 (s.mem.write64 (s.reg 29#5) value)

def byteCopy (s : CPU) : CPU :=
  let value := s.mem.read8 (s.reg 30#5)
  advanceCopy s (value.zeroExtend 64) 1#64 (s.mem.write8 (s.reg 29#5) value)

set_option maxRecDepth 8192 in
private theorem word_cycle (routine : Routine) (off : Nat) (s : CPU)
    (head : decodeRange routine off 2 = some (wordCode.take 2))
    (tail : decodeRange routine (off + 6) 6 = some (wordCode.drop 2)) :
    runWordCycle routine off s = some (if (s.reg 6#5).toNat < 8 then
      { s.put 31#5 8#64 with pc := s.pc + 22#64 } else wordCopy s) := by
  have jump : s.pc + 22#64 ≠ s.pc + 6#64 :=
    fun eq => (by decide : 22#64 ≠ 6#64) ((BitVec.add_right_inj s.pc).mp eq)
  unfold runWordCycle
  rw [head, tail]
  have r0 : s.reg 0#5 = 0#64 := reg_zero s
  by_cases small : (s.reg 6#5).toNat < 8
  · simp (config := { decide := true }) [wordCode, runOps, Op.step, Instruction.step, Branch.taken,
      BitVec.ult, r0, small, jump, BitVec.add_assoc]
    rfl
  · simp (config := { decide := true }) [wordCode, runOps, Op.step, Instruction.step, Branch.taken,
      BitVec.ult, r0, small, Width.load, Width.store, wordCopy, advanceCopy, BitVec.add_assoc,
      BitVec.sub_eq_add_neg]
    simp [CPU.advance, CPU.write, CPU.put, Vector.set_set, BitVec.add_assoc]

set_option maxRecDepth 8192 in
private theorem byte_cycle (routine : Routine) (off : Nat) (s : CPU)
    (head : decodeRange routine off 1 = some (byteCode.take 1))
    (tail : decodeRange routine (off + 4) 6 = some (byteCode.drop 1)) :
    runByteCycle routine off s = some (if s.reg 6#5 = 0#64 then
      { s with pc := s.pc + 20#64 } else byteCopy s) := by
  have jump : s.pc + 20#64 ≠ s.pc + 4#64 :=
    fun eq => (by decide : 20#64 ≠ 4#64) ((BitVec.add_right_inj s.pc).mp eq)
  unfold runByteCycle
  rw [head, tail]
  have r0 : s.reg 0#5 = 0#64 := reg_zero s
  by_cases empty : s.reg 6#5 = 0#64
  · simp [byteCode, runOps, Op.step, Instruction.step, Branch.taken, r0, empty, jump]
  · simp (config := { decide := true }) [byteCode, runOps, Op.step, Instruction.step, Branch.taken,
      r0, empty, Width.load, Width.store, byteCopy, advanceCopy, BitVec.add_assoc,
      BitVec.sub_eq_add_neg, BitVec.truncate_eq_setWidth]
    simp [CPU.advance, CPU.write, CPU.put, BitVec.add_assoc]

theorem word_copies (s : CPU) :
    let out := if (s.reg 6#5).toNat < 8 then
      { s.put 31#5 8#64 with pc := s.pc + 22#64 } else wordCopy s
    runWordCycle entry 0xda s = some out ∧ runWordCycle key 0x54 s = some out :=
  ⟨word_cycle entry 0xda s word_fragments.1.1 word_fragments.1.2,
    word_cycle key 0x54 s word_fragments.2.1 word_fragments.2.2⟩

theorem byte_copies (s : CPU) :
    let out := if s.reg 6#5 = 0#64 then { s with pc := s.pc + 20#64 } else byteCopy s
    runByteCycle entry 0xf0 s = some out ∧ runByteCycle key 0x6a s = some out :=
  ⟨byte_cycle entry 0xf0 s byte_fragments.1.1 byte_fragments.1.2,
    byte_cycle key 0x6a s byte_fragments.2.1 byte_fragments.2.2⟩

open Crypto.HMACSHA256.ARM64 (writeWords writeWords_outside read64_eq_of_cells)

def wordCycles (message : Bool) (s : CPU) : Nat → Option CPU
  | 0 => some s
  | n + 1 => (wordCycles message s n).bind
      (if message then runWordCycle entry 0xda else runWordCycle key 0x54)

structure WordCopyPrefix (start out : CPU) (length words : Nat) : Prop where
  pc : out.pc = start.pc
  memory : out.mem = writeWords start.mem (start.reg 29#5)
    (fun j => start.mem.read64 (start.reg 30#5 + BitVec.ofNat 64 (8 * j))) words
  source : out.reg 30#5 = start.reg 30#5 + BitVec.ofNat 64 (8 * words)
  dest : out.reg 29#5 = start.reg 29#5 + BitVec.ofNat 64 (8 * words)
  count : out.reg 6#5 = BitVec.ofNat 64 (length - 8 * words)
  preserved : ∀ r, r ≠ 6#5 → r ≠ 29#5 → r ≠ 30#5 → r ≠ 31#5 → out.reg r = start.reg r

theorem word_copy_iterations (message : Bool) (s : CPU) (length words : Nat)
    (lengthReg : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (wordBound : 8 * words ≤ length) :
    ∃ out, wordCycles message s words = some out ∧ WordCopyPrefix s out length words := by
  induction words with
  | zero =>
    exact ⟨s, rfl, ⟨rfl, rfl, by simp, by simp, by simpa using lengthReg, fun _ _ _ _ _ => rfl⟩⟩
  | succ n ih =>
    obtain ⟨mid, prevRun, prev⟩ := ih (by omega)
    have threshold : ¬ (mid.reg 6#5).toNat < 8 := by
      rw [prev.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length - 8 * n < 2 ^ 64)]
      omega
    have next : (if message then runWordCycle entry 0xda else runWordCycle key 0x54) mid =
        some (wordCopy mid) := by
      cases message
      · simpa only [Bool.false_eq_true, if_false, threshold] using (word_copies mid).2
      · simpa only [if_true, threshold] using (word_copies mid).1
    have sourceWord : mid.mem.read64 (mid.reg 30#5) = s.mem.read64 (s.reg 30#5 + BitVec.ofNat 64 (8 * n)) := by
      rw [prev.source]
      apply read64_eq_of_cells
      intro i
      rw [prev.memory, BitVec.add_assoc, ← BitVec.ofNat_add]
      apply writeWords_outside
      have h := apart (8 * n + i.val) (by have := i.isLt; omega)
      omega
    refine ⟨wordCopy mid, ?_, ⟨prev.pc, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [wordCycles, prevRun, Option.bind_some, next]
    · change mid.mem.write64 (mid.reg 29#5) (mid.mem.read64 (mid.reg 30#5)) = _
      rw [sourceWord, prev.dest, prev.memory]
      rfl
    · change (wordCopy mid).reg 30#5 = _
      have address : (wordCopy mid).reg 30#5 = mid.reg 30#5 + 8#64 := by
        simp (config := { decide := true }) [wordCopy, advanceCopy]
      rw [address, prev.source]
      simp [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
    · have address : (wordCopy mid).reg 29#5 = mid.reg 29#5 + 8#64 := by
        simp (config := { decide := true }) [wordCopy, advanceCopy]
      rw [address, prev.dest]
      simp [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
    · have remaining : (wordCopy mid).reg 6#5 = mid.reg 6#5 - 8#64 := by
        simp (config := { decide := true }) [wordCopy, advanceCopy]
      rw [remaining, prev.count]
      have eq : length - 8 * n = (length - 8 * (n + 1)) + 8 := by omega
      nth_rw 1 [eq]
      simp only [BitVec.ofNat_add, BitVec.add_sub_cancel]
    · intro r c d src temp
      unfold wordCopy advanceCopy
      rw [reg_write, reg_put]
      by_cases zero : r = 0
      · subst r
        exact (reg_zero _).symm
      · rw [if_neg zero, if_neg c, reg_put, if_neg zero, if_neg d,
          reg_put, if_neg zero, if_neg src, reg_put, if_neg zero, if_neg temp]
        exact prev.preserved r c d src temp

theorem word_copy_to_tail (message : Bool) (s : CPU) (length : Nat)
    (lengthReg : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat) :
    ∃ out, wordCycles message s (length / 8 + 1) = some out ∧
      out.pc = s.pc + 22#64 ∧ out.reg 6#5 = BitVec.ofNat 64 (length % 8) ∧
      out.reg 30#5 = s.reg 30#5 + BitVec.ofNat 64 (8 * (length / 8)) ∧
      out.reg 29#5 = s.reg 29#5 + BitVec.ofNat 64 (8 * (length / 8)) ∧
      out.mem = writeWords s.mem (s.reg 29#5)
        (fun j => s.mem.read64 (s.reg 30#5 + BitVec.ofNat 64 (8 * j))) (length / 8) ∧
      (∀ r, r ≠ 6#5 → r ≠ 29#5 → r ≠ 30#5 → r ≠ 31#5 → out.reg r = s.reg r) := by
  obtain ⟨mid, ran, p⟩ := word_copy_iterations message s length (length / 8) lengthReg lengthBound
    apart (by omega)
  have rem : mid.reg 6#5 = BitVec.ofNat 64 (length % 8) := by
    rw [p.count]
    congr 1
    omega
  have isSmall : (mid.reg 6#5).toNat < 8 := by
    rw [rem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length % 8 < 2 ^ 64)]
    omega
  let out := { mid.put 31#5 8#64 with pc := mid.pc + 22#64 }
  have next : (if message then runWordCycle entry 0xda else runWordCycle key 0x54) mid =
      some out := by
    cases message
    · simpa only [Bool.false_eq_true, if_false, if_pos isSmall, out] using (word_copies mid).2
    · simpa only [if_true, if_pos isSmall, out] using (word_copies mid).1
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, p.memory, ?_⟩
  · simp only [wordCycles, ran, Option.bind_some, next]
  · exact congrArg (· + 22#64) p.pc
  · change (mid.put 31#5 8#64).reg 6#5 = _
    simpa (config := { decide := true }) using rem
  · change (mid.put 31#5 8#64).reg 30#5 = _
    simpa (config := { decide := true }) using p.source
  · change (mid.put 31#5 8#64).reg 29#5 = _
    simpa (config := { decide := true }) using p.dest
  · intro r c d src tmp
    change (mid.put 31#5 8#64).reg r = _
    rw [reg_put, if_neg tmp]
    split
    · rename_i zero
      rw [zero, reg_zero]
    · exact p.preserved r c d src tmp

def copyRoutine (message : Bool) : Routine := if message then entry else key

def copyOffset (message words : Bool) : Nat :=
  if words then (if message then 0xda else 0x54) else (if message then 0xf0 else 0x6a)

def copyWidth (words : Bool) : Width := if words then .double else .byte

def copyExits (words : Bool) (s : CPU) : Prop :=
  if words then (s.reg 6#5).toNat < 8 else s.reg 6#5 = 0#64

instance (words : Bool) (s : CPU) : Decidable (copyExits words s) := by
  cases words <;> simp only [copyExits, Bool.false_eq_true, if_false, if_true] <;> infer_instance

def runCopyCycle (message words : Bool) (s : CPU) : Option CPU :=
  if words then runWordCycle (copyRoutine message) (copyOffset message true) s
  else runByteCycle (copyRoutine message) (copyOffset message false) s

def copyHeadCount (words : Bool) : Nat := if words then 2 else 1
private def copyHeadBytes (words : Bool) : Nat := if words then 6 else 4
private def copyExitBytes (words : Bool) : Nat := if words then 22 else 20

private def copyHead (words : Bool) : List Op :=
  if words then wordCode.take 2 else byteCode.take 1

private def copyBody (words : Bool) : List Op :=
  if words then wordCode.drop 2 else byteCode.drop 1

private theorem copy_decoded (message words : Bool) :
    decodeRange (copyRoutine message) (copyOffset message words) (copyHeadCount words) =
      some (copyHead words) ∧
    decodeRange (copyRoutine message) (copyOffset message words + copyHeadBytes words) 6 =
      some (copyBody words) := by
  cases words <;> cases message
  · exact byte_fragments.2
  · exact byte_fragments.1
  · exact word_fragments.2
  · exact word_fragments.1

private theorem copyRoutine_supported (message : Bool) :
    copyRoutine message = entry ∨ copyRoutine message = key ∨ copyRoutine message = finish := by
  cases message
  · exact .inr (.inl rfl)
  · exact .inl rfl

private theorem byte_head_state (s : CPU) :
    runOps (copyHead false) s =
      if Branch.taken .eq (s.reg 6#5) (s.reg 0#5) then {s with pc := s.pc + 20#64}
      else s.advance 4 := rfl

private theorem word_head_state (s : CPU) :
    let first := (s.advance 2).put 31#5 (s.reg 0#5 + 8#64)
    runOps (copyHead true) s =
      if Branch.taken .ltu (first.reg 6#5) (first.reg 31#5) then {first with pc := first.pc + 20#64}
      else first.advance 4 := rfl

private theorem copy_head_regs_mem (words : Bool) (s : CPU) :
    let head := runOps (copyHead words) s
    head.reg 30#5 = s.reg 30#5 ∧ head.reg 29#5 = s.reg 29#5 ∧ head.mem = s.mem := by
  dsimp only
  cases words
  · rw [byte_head_state]
    split <;> exact ⟨rfl,rfl,rfl⟩
  · rw [word_head_state]
    split
    · change ((s.advance 2).put 31#5 (s.reg 0#5 + 8#64)).reg 30#5 = _ ∧
        ((s.advance 2).put 31#5 (s.reg 0#5 + 8#64)).reg 29#5 = _ ∧
        ((s.advance 2).put 31#5 (s.reg 0#5 + 8#64)).mem = _
      simp (config := {decide := true}) only [reg_advance, reg_put, memory_advance,
        memory_put, if_false, and_true]
    · simp (config := {decide := true}) only [reg_advance, reg_put, memory_advance,
        memory_put, if_false, and_true]

set_option maxRecDepth 8192 in
private theorem copy_head_pc (words : Bool) (s : CPU) :
    (runOps (copyHead words) s).pc =
      if copyExits words s then s.pc + BitVec.ofNat 64 (copyExitBytes words)
      else s.pc + BitVec.ofNat 64 (copyHeadBytes words) := by
  have zero : s.reg 0#5 = 0#64 := reg_zero s
  cases words
  · rw [byte_head_state]
    by_cases empty : s.reg 6#5 = 0#64 <;>
      simp (config := {decide := true}) [copyExits, copyExitBytes, copyHeadBytes,
        Branch.taken, zero, empty, pc_advance]
  · rw [word_head_state]
    simp (config := {decide := true}) only [reg_advance, reg_put, if_true, if_false,
      zero, BitVec.zero_add, Branch.taken, BitVec.ult, pc_advance, pc_put]
    by_cases small : (s.reg 6#5).toNat < 8 <;>
      simp (config := {decide := true}) [copyExits, copyExitBytes, copyHeadBytes,
        small, pc_advance, pc_put, BitVec.add_assoc]

set_option maxRecDepth 8192 in
private theorem copy_head_allowed (message words : Bool) (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message words))
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true) :
    RangeAllowed (copyRoutine message) base (copyOffset message words) (copyHeadCount words) s := by
  refine ⟨copyHead words, (copy_decoded message words).1, ?_⟩
  cases words <;> cases message
  all_goals
    simp only [copyRoutine, copyOffset, copyHead, if_true, if_false, Bool.false_eq_true,
      wordCode, byteCode, List.take_succ_cons, List.take_zero] at pc aligned exec ⊢
    hmac_range_permissions pc aligned exec pc pc pc pc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2600000 in
private theorem copy_body_allowed (message words : Bool) (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base (copyRoutine message) +
      BitVec.ofNat 64 (copyOffset message words + copyHeadBytes words))
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true)
    (source : (Access.read (s.reg 30#5) (copyWidth words)).permitted s.mem = true)
    (dest : (Access.write (s.reg 29#5) (copyWidth words)).permitted s.mem = true) :
    RangeAllowed (copyRoutine message) base (copyOffset message words + copyHeadBytes words) 6 s := by
  refine ⟨copyBody words, (copy_decoded message words).2, ?_⟩
  cases words <;> cases message
  all_goals
    simp only [copyRoutine, copyOffset, copyHeadBytes, copyBody, copyWidth, if_true, if_false,
      Bool.false_eq_true, wordCode, byteCode, List.drop_succ_cons, List.drop_zero]
      at pc aligned exec source dest ⊢
    hmac_range_permissions pc aligned exec pc pc pc pc

private def copyGuardEvents (words : Bool) (pc : Addr) : List (List Access) :=
  if words then [[.fetch pc 2], [.fetch (pc + 2#64) 4]] else [[.fetch pc 4]]

private def copyBodyEvents (words : Bool) (pc src dest : Addr) : List (List Access) :=
  [[.fetch pc 4, .read src (copyWidth words)],
   [.fetch (pc + 4#64) 4, .write dest (copyWidth words)],
   [.fetch (pc + 8#64) 2], [.fetch (pc + 10#64) 2],
   [.fetch (pc + 12#64) 2], [.fetch (pc + 14#64) 2]]

def copyCycleEvents (words : Bool) (pc src dest : Addr) (exits : Bool) : List (List Access) :=
  copyGuardEvents words pc ++
    if exits then [] else copyBodyEvents words (pc + BitVec.ofNat 64 (copyHeadBytes words)) src dest

theorem copy_exit_events (words : Bool) (pc src dest : Addr) :
    copyCycleEvents words pc src dest true = copyCycleEvents words pc 0#64 0#64 true := rfl

private theorem copy_guard_events (words : Bool) (s : CPU) :
    runOpsEvents (copyHead words) s = copyGuardEvents words s.pc := by
  cases words <;> rfl

set_option maxRecDepth 8192 in
private theorem copy_body_events (words : Bool) (s : CPU) :
    runOpsEvents (copyBody words) s = copyBodyEvents words s.pc (s.reg 30#5) (s.reg 29#5) := by
  cases words <;>
    simp (config := {decide := true}) only [runOpsEvents, copyBody, copyBodyEvents,
      wordCode, byteCode, List.drop_succ_cons, List.drop_zero, Bool.false_eq_true, if_true, if_false,
      Op.accesses, Op.width, Crypto.RISCV64.Op.accesses, Op.step, Instruction.step, pc_advance,
      pc_put, pc_write, reg_advance, reg_put, reg_write, BitVec.add_zero, BitVec.add_assoc]
  all_goals rfl

/-- Fetch one word or byte copy cycle. The source and destination need
permissions only when the guard takes the data path. The jump back to the
loop head is itself part of the checked range. -/
theorem copy_cycle_fetched (message words : Bool) (base : Addr) (s out : CPU)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message words))
    (loaded : (copyRoutine message).Loaded (routineAddress base (copyRoutine message)) s.mem.read8)
    (readonly : RoutineReadOnly (copyRoutine message) base s.mem)
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true)
    (data : ¬copyExits words s →
      (Access.read (s.reg 30#5) (copyWidth words)).permitted s.mem = true ∧
      (Access.write (s.reg 29#5) (copyWidth words)).permitted s.mem = true)
    (run : runCopyCycle message words s = some out) :
    ∃ events, ProgramExecution base s events out ∧
      events.length = copyHeadCount words + (if copyExits words s then 0 else 6) ∧
      events = copyCycleEvents words s.pc (s.reg 30#5) (s.reg 29#5) (decide (copyExits words s)) := by
  classical
  let r := copyRoutine message
  let offset := copyOffset message words
  let mid := runOps (copyHead words) s
  have head : runRange r offset (copyHeadCount words) s = some mid := by
    simp only [runRange, (copy_decoded message words).1, Option.map_some, mid, r, offset]
  have tail : runRange r (offset + copyHeadBytes words) 6 mid = some (runOps (copyBody words) mid) := by
    simp only [runRange, (copy_decoded message words).2, Option.map_some, r, offset]
  have cycle : runCopyCycle message words s =
      if mid.pc = s.pc + BitVec.ofNat 64 (copyHeadBytes words) then
        some (runOps (copyBody words) mid) else some mid := by
    have ⟨front, back⟩ := copy_decoded message words
    cases words
    · simp only [runCopyCycle, if_false, Bool.false_eq_true, runByteCycle,
        show copyHeadCount false = 1 from rfl, show copyHeadBytes false = 4 from rfl] at front back ⊢
      rw [front, back]
      rfl
    · simp only [runCopyCycle, if_true, runWordCycle,
        show copyHeadCount true = 2 from rfl, show copyHeadBytes true = 6 from rfl] at front back ⊢
      rw [front, back]
      rfl
  let first := runOpsEvents (copyHead words) s
  have ⟨front, frontLen⟩ := run_range_observes (copyRoutine_supported message)
    head loaded readonly (copy_head_allowed message words base s pc aligned exec) (copy_decoded message words).1
  by_cases exits : copyExits words s
  · have different : mid.pc ≠ s.pc + BitVec.ofNat 64 (copyHeadBytes words) := by
      have atExit : mid.pc = s.pc + BitVec.ofNat 64 (copyExitBytes words) := by
        simpa only [if_pos exits] using copy_head_pc words s
      rw [atExit]
      intro equal
      have widths := (BitVec.add_right_inj s.pc).mp equal
      cases words <;> contradiction
    rw [cycle, if_neg different] at run
    refine ⟨first, (Option.some.inj run) ▸ front,
      by simpa only [if_pos exits, Nat.add_zero] using frontLen, ?_⟩
    simp only [first, copy_guard_events, copyCycleEvents, decide_eq_true exits, if_true, List.append_nil]
  · have falls : mid.pc = s.pc + BitVec.ofNat 64 (copyHeadBytes words) := by
      simpa only [if_neg exits] using copy_head_pc words s
    have nextPC : mid.pc = routineAddress base r + BitVec.ofNat 64 (offset + copyHeadBytes words) := by
      rw [falls, pc, BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain ⟨src, dst, mem⟩ := copy_head_regs_mem words s
    change mid.reg 30#5 = s.reg 30#5 at src
    change mid.reg 29#5 = s.reg 29#5 at dst
    have nextRead : (Access.read (mid.reg 30#5) (copyWidth words)).permitted mid.mem = true := by
      rw [src, mem]
      exact (data exits).1
    have nextWrite : (Access.write (mid.reg 29#5) (copyWidth words)).permitted mid.mem = true := by
      rw [dst, mem]
      exact (data exits).2
    have nextExec : mid.mem.canExec (routineAddress base r) r.image.size = true := by
      rw [mem]
      exact exec
    obtain ⟨boundImage, ro⟩ := front.keeps_routine loaded readonly
    let last := runOpsEvents (copyBody words) mid
    have ⟨back, backLen⟩ := run_range_observes (copyRoutine_supported message)
      tail boundImage ro (copy_body_allowed message words base mid nextPC aligned nextExec nextRead nextWrite)
      (copy_decoded message words).2
    rw [cycle, if_pos falls] at run
    refine ⟨first ++ last, (Option.some.inj run) ▸ front.append back, ?_, ?_⟩
    · simp only [first, last, List.length_append, frontLen, backLen, if_neg exits]
    · simp only [first, last, copyCycleEvents, decide_eq_false exits, Bool.false_eq_true, if_false,
        copy_guard_events, copy_body_events, falls, src, dst]

end Crypto.HMACSHA256.RISCV64
