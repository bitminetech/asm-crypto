import Proofs.HMACSHA256.RISCV64CopyTail

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

def copyCycles (message words : Bool) (s : CPU) (n : Nat) : Option CPU :=
  if words then wordCycles message s n else byteCycles message s n

private theorem copyCycles_next (message words : Bool) (s : CPU) (n : Nat) :
    copyCycles message words s (n + 1) =
      (copyCycles message words s n).bind (runCopyCycle message words) := by
  cases words <;> cases message <;> rfl

private theorem copy_position (message words : Bool) (s : CPU) (length n : Nat)
    (count : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (fit : (copyWidth words).bytes * n ≤ length) :
    ∃ out, copyCycles message words s n = some out ∧
      out.pc = s.pc ∧ out.reg 6#5 = BitVec.ofNat 64 (length - (copyWidth words).bytes * n) ∧
      out.reg 30#5 = s.reg 30#5 + BitVec.ofNat 64 ((copyWidth words).bytes * n) ∧
      out.reg 29#5 = s.reg 29#5 + BitVec.ofNat 64 ((copyWidth words).bytes * n) := by
  cases words
  · have size : (copyWidth false).bytes = 1 := rfl
    rw [size, Nat.one_mul] at fit ⊢
    obtain ⟨out, run, post⟩ := byte_copy_iterations message s length n count lengthBound apart fit
    exact ⟨out, run, post.pc, post.count, post.source, post.dest⟩
  · obtain ⟨out, run, post⟩ := word_copy_iterations message s length n count lengthBound apart fit
    exact ⟨out, run, post.pc, post.count, post.source, post.dest⟩

private theorem copyExits_iff (words : Bool) (s : CPU) :
    copyExits words s ↔ (s.reg 6#5).toNat < (copyWidth words).bytes := by
  cases words
  · change s.reg 6#5 = 0#64 ↔ (s.reg 6#5).toNat < 1
    constructor
    · intro h
      rw [h]
      decide
    · intro h
      apply BitVec.eq_of_toNat_eq
      have z : (0#64).toNat = 0 := rfl
      omega
  · rfl

private theorem copyWidth_positive (words : Bool) : 0 < (copyWidth words).bytes := by
  cases words <;> decide

theorem ProgramExecution.preserves_copy_accesses {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (source dest : Addr) (width : Width)
    (data : (Access.read source width).permitted s.mem = true ∧
      (Access.write dest width).permitted s.mem = true) :
    (Access.read source width).permitted out.mem = true ∧
      (Access.write dest width).permitted out.mem = true := by
  obtain ⟨read, write⟩ := data
  simp only [Access.permitted, Bool.and_eq_true] at read write ⊢
  exact ⟨⟨read.1, (run.permissions _ _).2 read.2⟩, ⟨write.1, (run.permissions _ _).1.trans write.2⟩⟩

def takenCopyEvents (words : Bool) (pc src dest : Addr) : Nat → List (List Access)
  | 0 => []
  | n + 1 =>
    let offset := BitVec.ofNat 64 ((copyWidth words).bytes * n)
    takenCopyEvents words pc src dest n ++ copyCycleEvents words pc (src + offset) (dest + offset) false

def copyLoopEvents (words : Bool) (pc src dest : Addr) (steps : Nat) : List (List Access) :=
  takenCopyEvents words pc src dest steps ++ copyCycleEvents words pc 0#64 0#64 true

private theorem copy_iterations_fetched (message words : Bool) (base : Addr) (s : CPU)
    (length n : Nat)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message words))
    (loaded : (copyRoutine message).Loaded (routineAddress base (copyRoutine message)) s.mem.read8)
    (readonly : RoutineReadOnly (copyRoutine message) base s.mem)
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true)
    (count : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (fit : (copyWidth words).bytes * n ≤ length)
    (data : ∀ i, (copyWidth words).bytes * (i + 1) ≤ length →
      (Access.read (s.reg 30#5 + BitVec.ofNat 64 ((copyWidth words).bytes * i)) (copyWidth words)).permitted s.mem = true ∧
      (Access.write (s.reg 29#5 + BitVec.ofNat 64 ((copyWidth words).bytes * i)) (copyWidth words)).permitted s.mem = true) :
    ∃ out events, copyCycles message words s n = some out ∧ ProgramExecution base s events out ∧
      events.length = (copyHeadCount words + 6) * n ∧
      events = takenCopyEvents words s.pc (s.reg 30#5) (s.reg 29#5) n := by
  induction n with
  | zero =>
    have empty : copyCycles message words s 0 = some s := by cases words <;> rfl
    exact ⟨s, [], empty, .nil s, by simp, rfl⟩
  | succ n ih =>
    have inside : (copyWidth words).bytes * n ≤ length := by
      rw [Nat.mul_succ] at fit
      omega
    obtain ⟨mid, trace, preceding, execution, ntrace, observation⟩ := ih inside
    obtain ⟨expected, expectedRun, expectedPC, remaining, source, dest⟩ :=
      copy_position message words s length n count lengthBound apart inside
    have same : expected = mid := Option.some.inj (expectedRun.symm.trans preceding)
    subst expected
    obtain ⟨out, finished, _⟩ := copy_position message words s length (n + 1) count lengthBound apart fit
    have run : runCopyCycle message words mid = some out := by
      rw [copyCycles_next, preceding] at finished
      exact finished
    have stays : ¬copyExits words mid := by
      rw [copyExits_iff, remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : length -
        (copyWidth words).bytes * n < 2^64)]
      rw [Nat.mul_succ] at fit
      omega
    obtain ⟨image, code⟩ := execution.keeps_routine loaded readonly
    have nextExec : mid.mem.canExec (routineAddress base (copyRoutine message))
        (copyRoutine message).image.size = true := (allPerm_eq_of_perm execution.perm _ _ _).trans exec
    have grants : (Access.read (mid.reg 30#5) (copyWidth words)).permitted mid.mem = true ∧
        (Access.write (mid.reg 29#5) (copyWidth words)).permitted mid.mem = true := by
      rw [source, dest]
      exact execution.preserves_copy_accesses _ _ _ (data n fit)
    obtain ⟨cycle, next, ncycle, formula⟩ := copy_cycle_fetched message words base mid out
      (expectedPC.trans pc) image code aligned nextExec (fun _ => grants) run
    refine ⟨out, trace ++ cycle, finished, execution.append next, ?_, ?_⟩
    · simp only [List.length_append, ntrace, ncycle, if_neg stays, Nat.mul_succ]
    · rw [observation, formula, expectedPC, source, dest, decide_eq_false stays]
      rfl

set_option maxRecDepth 8192 in
/-- Lift the decoded word or byte loop to its fetched execution, including
the final guard that exits without touching the source or destination. -/
theorem copy_loop_fetched (message words : Bool) (base : Addr) (s out : CPU) (length : Nat)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message words))
    (loaded : (copyRoutine message).Loaded (routineAddress base (copyRoutine message)) s.mem.read8)
    (readonly : RoutineReadOnly (copyRoutine message) base s.mem)
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true)
    (count : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (data : ∀ i, (copyWidth words).bytes * (i + 1) ≤ length →
      (Access.read (s.reg 30#5 + BitVec.ofNat 64 ((copyWidth words).bytes * i)) (copyWidth words)).permitted s.mem = true ∧
      (Access.write (s.reg 29#5 + BitVec.ofNat 64 ((copyWidth words).bytes * i)) (copyWidth words)).permitted s.mem = true)
    (run : copyCycles message words s (length / (copyWidth words).bytes + 1) = some out) :
    ∃ events, ProgramExecution base s events out ∧
      events.length = (copyHeadCount words + 6) * (length / (copyWidth words).bytes) + copyHeadCount words ∧
      events = copyLoopEvents words s.pc (s.reg 30#5) (s.reg 29#5) (length / (copyWidth words).bytes) := by
  let n := length / (copyWidth words).bytes
  have divides := Nat.mod_add_div length (copyWidth words).bytes
  have small := Nat.mod_lt length (copyWidth_positive words)
  have fits : (copyWidth words).bytes * n ≤ length := by dsimp [n]; omega
  obtain ⟨mid, trace, preceding, execution, ntrace, prefixTrace⟩ :=
    copy_iterations_fetched message words base s length n pc loaded readonly aligned exec
      count lengthBound apart fits data
  obtain ⟨expected, expectedRun, expectedPC, remaining, _, _⟩ :=
    copy_position message words s length n count lengthBound apart fits
  have same : expected = mid := Option.some.inj (expectedRun.symm.trans preceding)
  subst expected
  change copyCycles message words s (n + 1) = some out at run
  rw [copyCycles_next, preceding] at run
  have exits : copyExits words mid := by
    rw [copyExits_iff, remaining, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : length - (copyWidth words).bytes * n < 2 ^ 64)]
    dsimp [n]
    omega
  obtain ⟨image, code⟩ := execution.keeps_routine loaded readonly
  have nextExec : mid.mem.canExec (routineAddress base (copyRoutine message))
      (copyRoutine message).image.size = true := (allPerm_eq_of_perm execution.perm _ _ _).trans exec
  obtain ⟨tail, last, ntail, exitTrace⟩ := copy_cycle_fetched message words base mid out
    (expectedPC.trans pc) image code aligned nextExec (fun stays => (stays exits).elim) run
  refine ⟨trace ++ tail, execution.append last, ?_, ?_⟩
  · simp only [List.length_append, ntrace, ntail, if_pos exits, Nat.add_zero, n]
  · rw [prefixTrace, exitTrace, expectedPC, decide_eq_true exits, copy_exit_events]
    rfl

theorem copy_accesses_of_grants {m : Memory} {src dst : Addr}
    {srcExtent dstExtent srcStart dstStart length : Nat}
    (srcAligned : src.toNat % 8 = 0) (dstAligned : dst.toNat % 8 = 0)
    (srcOffset : srcStart % 8 = 0) (dstOffset : dstStart % 8 = 0)
    (srcFits : srcStart + length ≤ srcExtent) (dstFits : dstStart + length ≤ dstExtent)
    (readable : m.canRead src srcExtent = true) (writable : m.canWrite dst dstExtent = true)
    (w : Bool) (off : Nat) (fits : off + (copyWidth w).bytes ≤ length)
    (align : off % (copyWidth w).bytes = 0) :
    (Access.read (src + BitVec.ofNat 64 (srcStart + off)) (copyWidth w)).permitted m = true ∧
    (Access.write (dst + BitVec.ofNat 64 (dstStart + off)) (copyWidth w)).permitted m = true := by
  have offsetAligned (n : Nat) (startAligned : n % 8 = 0) :
      (n + off) % (copyWidth w).bytes = 0 := by
    cases w
    · change (n + off) % 1 = 0
      omega
    · change (n + off) % 8 = 0
      change off % 8 = 0 at align
      omega
  have baseAligned (p : Addr) (h : p.toNat % 8 = 0) : p.toNat % (copyWidth w).bytes = 0 := by
    cases w
    · change p.toNat % 1 = 0
      omega
    · exact h
  have source : InRegion src srcExtent _ (copyWidth w) :=
    ⟨srcStart + off, by omega, offsetAligned _ srcOffset, rfl⟩
  have dest : InRegion dst dstExtent _ (copyWidth w) :=
    ⟨dstStart + off, by omega, offsetAligned _ dstOffset, rfl⟩
  exact ⟨source.permitted_read (baseAligned _ srcAligned) readable,
    dest.permitted_write (baseAligned _ dstAligned) writable⟩

def copyPayloadEvents (pc src dest : Addr) (length : Nat) : List (List Access) :=
  let offset := BitVec.ofNat 64 (8 * (length / 8))
  copyLoopEvents true pc src dest (length / 8) ++
    copyLoopEvents false (pc + 22#64) (src + offset) (dest + offset) (length % 8)

/-- Compose the word prefix and byte remainder against one source and one
destination. The word loop's final guard enters the decoded byte loop. -/
theorem copy_payload_fetched (message : Bool) (base : Addr) (s tail out : CPU) (length : Nat)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message true))
    (loaded : (copyRoutine message).Loaded (routineAddress base (copyRoutine message)) s.mem.read8)
    (readonly : RoutineReadOnly (copyRoutine message) base s.mem)
    (aligned : (routineAddress base (copyRoutine message)).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base (copyRoutine message)) (copyRoutine message).image.size = true)
    (count : s.reg 6#5 = BitVec.ofNat 64 length) (lengthBound : length < 2 ^ 64)
    (apart : ∀ i, i < length → length ≤ (s.reg 30#5 + BitVec.ofNat 64 i - s.reg 29#5).toNat)
    (data : ∀ w off, off + (copyWidth w).bytes ≤ length → off % (copyWidth w).bytes = 0 →
      (Access.read (s.reg 30#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted s.mem = true ∧
      (Access.write (s.reg 29#5 + BitVec.ofNat 64 off) (copyWidth w)).permitted s.mem = true)
    (words : wordCycles message s (length / 8 + 1) = some tail)
    (bytes : byteCycles message tail (length % 8 + 1) = some out) :
    ∃ events, ProgramExecution base s events out ∧
      events.length = 3 + 8 * (length / 8) + 7 * (length % 8) ∧
      events = copyPayloadEvents s.pc (s.reg 30#5) (s.reg 29#5) length := by
  have wordData : ∀ i, 8 * (i + 1) ≤ length →
      (Access.read (s.reg 30#5 + BitVec.ofNat 64 (8 * i)) .double).permitted s.mem = true ∧
      (Access.write (s.reg 29#5 + BitVec.ofNat 64 (8 * i)) .double).permitted s.mem = true := by
    intro i fits
    exact data true (8 * i) (by change 8 * i + 8 ≤ length; omega)
      (by change (8 * i) % 8 = 0; omega)
  obtain ⟨front, runWords, nfront, firstEvents⟩ := copy_loop_fetched message true base s tail length
    pc loaded readonly aligned exec count lengthBound apart wordData words
  obtain ⟨actualTail, actualWords, tailPC, remainder, tailSource, tailDest, _, _⟩ :=
    word_copy_to_tail message s length count lengthBound apart
  have sameTail : actualTail = tail := Option.some.inj (actualWords.symm.trans words)
  subst actualTail
  let split := 8 * (length / 8)
  have sum : split + length % 8 = length := by dsimp [split]; omega
  have tailApart (i : Nat) (inside : i < length % 8) :
      length % 8 ≤ (tail.reg 30#5 + BitVec.ofNat 64 i - tail.reg 29#5).toNat := by
    rw [tailSource, tailDest, BitVec.add_assoc, ← BitVec.ofNat_add]
    have outside := apart (split + i) (by omega)
    have within : split ≤ (s.reg 30#5 + BitVec.ofNat 64 (split + i) - s.reg 29#5).toNat := by omega
    rw [copy_offset_distance _ _ _ within]
    omega
  have byteData : ∀ i, 1 * (i + 1) ≤ length % 8 →
      (Access.read (tail.reg 30#5 + BitVec.ofNat 64 (1 * i)) .byte).permitted tail.mem = true ∧
      (Access.write (tail.reg 29#5 + BitVec.ofNat 64 (1 * i)) .byte).permitted tail.mem = true := by
    intro i fits
    rw [tailSource, tailDest, Nat.one_mul]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact runWords.preserves_copy_accesses _ _ _ (data false (split + i)
      (by change _ + 1 ≤ _; omega) (by change _ % 1 = 0; omega))
  obtain ⟨image, code⟩ := runWords.keeps_routine loaded readonly
  have tailAt : tail.pc = routineAddress base (copyRoutine message) +
      BitVec.ofNat 64 (copyOffset message false) := by
    rw [tailPC, pc, BitVec.add_assoc]
    have consecutive : BitVec.ofNat 64 (copyOffset message true) + 22#64 =
        BitVec.ofNat 64 (copyOffset message false) := by cases message <;> rfl
    rw [consecutive]
  have tailExec : tail.mem.canExec (routineAddress base (copyRoutine message))
      (copyRoutine message).image.size = true := (allPerm_eq_of_perm runWords.perm _ _ _).trans exec
  obtain ⟨back, runBytes, nback, finalEvents⟩ := copy_loop_fetched message false base tail out (length % 8)
    tailAt image code aligned tailExec remainder (by omega) tailApart byteData
    (by change copyCycles message false tail (length % 8 / 1 + 1) = some out
        simpa only [Nat.div_one] using bytes)
  refine ⟨front ++ back, runWords.append runBytes, ?_, ?_⟩
  · simp only [List.length_append, nfront, nback, copyHeadCount, copyWidth,
      if_true, if_false, Bool.false_eq_true, Width.bytes, Nat.div_one]
    omega
  · rw [firstEvents, finalEvents, tailPC, tailSource, tailDest]
    change copyLoopEvents true s.pc (s.reg 30#5) (s.reg 29#5) (length / 8) ++
      copyLoopEvents false (s.pc + 22#64) _ _ (length % 8 / 1) = _
    rw [Nat.div_one]
    rfl

end Crypto.HMACSHA256.RISCV64
