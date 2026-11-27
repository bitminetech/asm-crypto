import Proofs.HMACSHA256.ARM64Copy
import Proofs.HMACSHA256.EncodedByteList

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

def copyIterations (message wide : Bool) (s : Arm64.State) : Nat → Option Arm64.State
  | 0 => some s
  | n + 1 => (copyIterations message wide s n).bind (runCopyCycle message wide)

structure CopyPrefix (message : Bool) (before out : Arm64.State) (count : Nat) : Prop where
  pc : out.pc = before.pc
  source : out.readReg64 (copySource message) =
    before.readReg64 (copySource message) + BitVec.ofNat 64 count
  dest : out.readReg64 (copyDestination message) =
    before.readReg64 (copyDestination message) + BitVec.ofNat 64 count
  remaining : out.readReg64 (copyCount message) =
    before.readReg64 (copyCount message) - BitVec.ofNat 64 count
  bytes : ∀ i < count, out.mem.read8 (before.readReg64 (copyDestination message) + BitVec.ofNat 64 i) =
    before.mem.read8 (before.readReg64 (copySource message) + BitVec.ofNat 64 i)
  frame : ∀ p, count ≤ (p - before.readReg64 (copyDestination message)).toNat →
    out.mem.cells p = before.mem.cells p
  readable : ∀ p n, before.mem.canRead p n = true → out.mem.canRead p n = true
  writable : ∀ p n, out.mem.canWrite p n = before.mem.canWrite p n
  nonvolatile : nonvolatile out = nonvolatile before
  nonMemory : nonMemory out = nonMemory before

private theorem store_copy_byte (wide : Bool) (m : Arm64.Memory) (src dst : Addr) (i : Nat)
    (within : i < (copyWidth wide).bytes) :
    (m.writeSized (copyWidth wide) dst (m.readSized (copyWidth wide) false src)).read8
      (dst + BitVec.ofNat 64 i) = m.read8 (src + BitVec.ofNat 64 i) := by
  cases wide
  · change i < 1 at within
    have zero : i = 0 := by omega
    subst i
    simp [copyWidth, Arm64.Memory.writeSized, Arm64.Memory.readSized, BitVec.add_zero]
  · change i < 8 at within
    change (m.write64 dst (m.read64 src)).read8 (dst + BitVec.ofNat 64 i) =
      m.read8 (src + BitVec.ofNat 64 i)
    rw [write64_byte m dst (m.read64 src) ⟨i, within⟩, read64_byte m src ⟨i, within⟩]

private theorem copy_store_outside (wide : Bool) (m : Arm64.Memory) (dst p v : Addr)
    (outside : (copyWidth wide).bytes ≤ (p - dst).toNat) :
    (m.writeSized (copyWidth wide) dst v).cells p = m.cells p := by
  cases wide
  · apply cells_write8_outside
    intro hp
    subst p
    change 1 ≤ (dst - dst).toNat at outside
    simp at outside
  · exact write64_cells_outside m dst p v outside

private theorem copy_store_readable (wide : Bool) (m : Arm64.Memory) (dst v p : Addr) (n : Nat)
    (read : m.canRead p n = true) : (m.writeSized (copyWidth wide) dst v).canRead p n = true := by
  cases wide
  · exact canRead_write8 _ _ _ _ _ read
  · exact canRead_write64 _ _ _ _ _ read

private theorem copy_store_writable (wide : Bool) (m : Arm64.Memory) (dst v p : Addr) (n : Nat) :
    (m.writeSized (copyWidth wide) dst v).canWrite p n = m.canWrite p n := by
  cases wide
  · exact canWrite_write8 _ _ _ _ _
  · exact canWrite_write64 _ _ _ _ _

set_option maxHeartbeats 2400000 in
/-- All taken word or byte iterations share the same source and destination
grants. The induction reads each source byte from the initial input and
preserves every cell outside the prefix copied so far. -/
theorem copy_iterations (message wide : Bool) (s : Arm64.State) (length n : Nat)
    (count : s.readReg64 (copyCount message) = BitVec.ofNat 64 length)
    (lengthBound : length < 2 ^ 64) (fits : (copyWidth wide).bytes * n ≤ length)
    (apart : ∀ i < length, length ≤
      (s.readReg64 (copySource message) + BitVec.ofNat 64 i - s.readReg64 (copyDestination message)).toNat)
    (readable : ∀ i, i + (copyWidth wide).bytes ≤ length →
      s.mem.canRead (s.readReg64 (copySource message) + BitVec.ofNat 64 i) (copyWidth wide).bytes = true)
    (writable : ∀ i, i + (copyWidth wide).bytes ≤ length →
      s.mem.canWrite (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i) (copyWidth wide).bytes = true) :
    ∃ out, copyIterations message wide s n = some out ∧
      CopyPrefix message s out ((copyWidth wide).bytes * n) := by
  let width := (copyWidth wide).bytes
  induction n with
  | zero =>
    refine ⟨s, rfl, ⟨rfl, ?_, ?_, ?_, ?_, fun _ _ => rfl,
      fun _ _ h => h, fun _ _ => rfl, rfl, rfl⟩⟩
    · simp
    · simp
    · simp
    · intro i impossible
      simp at impossible
  | succ n ih =>
    let first := width * n
    have total : (copyWidth wide).bytes * (n + 1) = first + width :=
      Nat.mul_succ _ _
    rw [total] at fits
    have firstFits : first ≤ length := by omega
    have firstBound : first < 2 ^ 64 := Nat.lt_of_le_of_lt firstFits lengthBound
    obtain ⟨mid, prefixRun, before⟩ := ih firstFits
    have remaining : (mid.readReg64 (copyCount message)).toNat = length - first := by
      have eq := before.remaining
      change mid.readReg64 (copyCount message) =
        s.readReg64 (copyCount message) - BitVec.ofNat 64 first at eq
      rw [eq, count, BitVec.ofNat_sub_ofNat_of_le length first firstBound firstFits,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have src := before.source
    have dst := before.dest
    change mid.readReg64 (copySource message) = s.readReg64 (copySource message) + BitVec.ofNat 64 first at src
    change mid.readReg64 (copyDestination message) = s.readReg64 (copyDestination message) + BitVec.ofNat 64 first at dst
    have readStep : mid.mem.canRead (mid.readReg64 (copySource message)) width = true := by
      rw [src]
      exact before.readable _ _ (readable first fits)
    have writeStep : mid.mem.canWrite (mid.readReg64 (copyDestination message)) width = true := by
      rw [dst, before.writable]
      exact writable first fits
    obtain ⟨out, step, copied⟩ := copy_cycle_taken message wide mid (by rw [remaining]; change width ≤ _; omega)
      readStep writeStep
    refine ⟨out, by simp only [copyIterations, prefixRun, Option.bind_some, step], ?_⟩
    rw [total]
    refine ⟨copied.pc.trans before.pc, ?_, ?_, ?_, ?_, ?_,
      fun p k h => by rw [copied.memory]; exact copy_store_readable _ _ _ _ _ _ (before.readable p k h),
      fun p k => by rw [copied.memory, copy_store_writable, before.writable],
      copied.nonvolatile.trans before.nonvolatile, copied.nonMemory.trans before.nonMemory⟩
    · rw [copied.source, src, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [copied.dest, dst, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [copied.count, before.remaining, BitVec.sub_sub, BitVec.ofNat_add]
    · intro i inside
      by_cases early : i < first
      · have outOfStore := outside_span_of_offset (s.readReg64 (copyDestination message))
          i first width (.inl early) (by omega) (by omega)
        have unchanged := copy_store_outside wide mid.mem (mid.readReg64 (copyDestination message))
          (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i)
          (mid.mem.readSized (copyWidth wide) false (mid.readReg64 (copySource message)))
          (by rw [dst]; exact outOfStore)
        unfold Arm64.Memory.read8
        rw [copied.memory, unchanged]
        exact before.bytes i early
      let j := i - first
      have index : first + j = i := by dsimp [j]; omega
      have jFits : j < width := by omega
      have destByte : s.readReg64 (copyDestination message) + BitVec.ofNat 64 i =
          mid.readReg64 (copyDestination message) + BitVec.ofNat 64 j := by
        rw [dst, BitVec.add_assoc, ← BitVec.ofNat_add, index]
      have sourceByte : mid.readReg64 (copySource message) + BitVec.ofNat 64 j =
          s.readReg64 (copySource message) + BitVec.ofNat 64 i := by
        rw [src, BitVec.add_assoc, ← BitVec.ofNat_add, index]
      rw [destByte, copied.memory, store_copy_byte _ _ _ _ _ jFits, sourceByte]
      unfold Arm64.Memory.read8
      rw [before.frame _ (Nat.le_trans firstFits (apart i (by omega)))]
    · intro p off
      let d := (p - s.readReg64 (copyDestination message)).toNat
      have addresses := address_reconstruct (s.readReg64 (copyDestination message)) p
      have bound := (p - s.readReg64 (copyDestination message)).isLt
      have elsewhere := outside_span_of_offset (s.readReg64 (copyDestination message)) d first width
        (.inr off) (by omega) bound
      rw [addresses, ← dst] at elsewhere
      rw [copied.memory, copy_store_outside _ _ _ _ _ elsewhere]
      have lower : first ≤ d := by
        change first + width ≤ d at off
        omega
      exact before.frame p lower

def copyIterationEvents (wide : Bool) (pc sp src dst : Addr) : Nat → List InstructionObservation
  | 0 => []
  | n + 1 =>
    let offset := BitVec.ofNat 64 ((copyWidth wide).bytes * n)
    copyIterationEvents wide pc sp src dst n ++ copyCycleEvents wide true pc sp (src + offset) (dst + offset)

def copyPayloadEvents (pc sp src dst : Addr) (length : Nat) : List InstructionObservation :=
  let skip := BitVec.ofNat 64 (8 * (length / 8))
  copyIterationEvents true pc sp src dst (length / 8) ++ copyGuardEvents true false pc sp ++
  copyIterationEvents false (pc + 24#64) sp (src + skip) (dst + skip) (length % 8) ++
  copyGuardEvents false false (pc + 24#64) sp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2600000 in
/-- Fetch every taken copy cycle. The source grant and destination grant
used by the functional induction also establish that the final state of
each fetched cycle is running. -/
theorem copy_iterations_fetched (message wide : Bool) (base : Addr) (s out : Arm64.State)
    (length n : Nat)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message wide))
    (loaded : (programAt (copyRoutine message) (routineAddress base (copyRoutine message))).CodeLoaded s.mem)
    (running : s.status = .Running)
    (count : s.readReg64 (copyCount message) = BitVec.ofNat 64 length)
    (lengthBound : length < 2 ^ 64) (fits : (copyWidth wide).bytes * n ≤ length)
    (apart : ∀ i < length, length ≤
      (s.readReg64 (copySource message) + BitVec.ofNat 64 i - s.readReg64 (copyDestination message)).toNat)
    (readable : ∀ i, i + (copyWidth wide).bytes ≤ length →
      s.mem.canRead (s.readReg64 (copySource message) + BitVec.ofNat 64 i) (copyWidth wide).bytes = true)
    (writable : ∀ i, i + (copyWidth wide).bytes ≤ length →
      s.mem.canWrite (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i) (copyWidth wide).bytes = true)
    (executed : copyIterations message wide s n = some out) :
    let observations := copyIterationEvents wide s.pc s.sp
      (s.readReg64 (copySource message)) (s.readReg64 (copyDestination message)) n
    LinkedExecution base s observations out ∧ observations.length = (copyGuardCount wide + 4) * n := by
  induction n generalizing out with
  | zero =>
    have same : s = out := Option.some.inj executed
    subst out
    exact ⟨.nil _, (Nat.mul_zero _).symm⟩
  | succ n ih =>
    let width := (copyWidth wide).bytes
    let first := width * n
    have sum : width * (n + 1) = first + width := Nat.mul_succ _ _
    change width * (n + 1) ≤ length at fits
    rw [sum] at fits
    have frontFits : first ≤ length := by omega
    obtain ⟨mid, frontRun, before⟩ :=
      copy_iterations message wide s length n count lengthBound frontFits apart readable writable
    obtain ⟨actual, finalRun, after⟩ :=
      copy_iterations message wide s length (n + 1) count lengthBound (by rwa [sum]) apart readable writable
    have result : actual = out := Option.some.inj (finalRun.symm.trans executed)
    subst actual
    have outLive : out.status = .Running := by
      have same := congrArg Arm64.State.status after.nonMemory
      exact same.trans running
    obtain ⟨throughFront, nfront⟩ := ih mid frontFits frontRun
    have stage := before.pc.trans pc
    have left : runCopyCycle message wide mid = some out := by
      simpa only [copyIterations, frontRun, Option.bind_some] using executed
    have midCount : (mid.readReg64 (copyCount message)).toNat = length - first := by
      have remaining := before.remaining
      change mid.readReg64 (copyCount message) =
        s.readReg64 (copyCount message) - BitVec.ofNat 64 first at remaining
      rw [remaining, count, BitVec.ofNat_sub_ofNat_of_le length first (by omega) frontFits,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have taken : (copyWidth wide).bytes ≤ (mid.readReg64 (copyCount message)).toNat := by
      change width ≤ (mid.readReg64 (copyCount message)).toNat
      rw [midCount]
      omega
    have grants (_ : width ≤ (mid.readReg64 (copyCount message)).toNat) :
        mid.mem.canRead (mid.readReg64 (copySource message)) width = true ∧
        mid.mem.canWrite (mid.readReg64 (copyDestination message)) width = true := by
      rw [before.source, before.dest, before.writable]
      exact ⟨before.readable _ _ (readable first fits), writable first fits⟩
    obtain ⟨throughBack, nback⟩ := copy_cycle_fetched message wide base mid out stage
      (throughFront.keeps_code _ loaded) left outLive grants
    have sp : mid.sp = s.sp := by
      change (nonMemory mid).sp = (nonMemory s).sp
      rw [before.nonMemory]
    have decision : decide ((copyWidth wide).bytes ≤ (mid.readReg64 (copyCount message)).toNat) = true := by simp [taken]
    simp only [if_pos taken, decision, before.pc, before.source, before.dest, sp] at throughBack nback
    refine ⟨throughFront.append throughBack, ?_⟩
    simp only [copyIterationEvents, List.length_append, nfront, nback, Nat.mul_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
/-- Copy the word prefix and byte remainder, then fall through the final
zero-count check. The two exit checks introduce no memory effects. -/
theorem copy_payload (message : Bool) (base : Addr) (s : Arm64.State) (length : Nat)
    (pc : s.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message true))
    (loaded : (programAt (copyRoutine message) (routineAddress base (copyRoutine message))).CodeLoaded s.mem)
    (running : s.status = .Running)
    (count : s.readReg64 (copyCount message) = BitVec.ofNat 64 length)
    (lengthBound : length < 2 ^ 64)
    (apart : ∀ i < length, length ≤
      (s.readReg64 (copySource message) + BitVec.ofNat 64 i - s.readReg64 (copyDestination message)).toNat)
    (readable : ∀ w i, i + (copyWidth w).bytes ≤ length →
      s.mem.canRead (s.readReg64 (copySource message) + BitVec.ofNat 64 i) (copyWidth w).bytes = true)
    (writable : ∀ w i, i + (copyWidth w).bytes ≤ length →
      s.mem.canWrite (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i) (copyWidth w).bytes = true) :
    ∃ out,
      LinkedExecution base s (copyPayloadEvents s.pc s.sp (s.readReg64 (copySource message))
        (s.readReg64 (copyDestination message)) length) out ∧
      (copyPayloadEvents s.pc s.sp (s.readReg64 (copySource message))
        (s.readReg64 (copyDestination message)) length).length = 3 + 6 * (length / 8) + 5 * (length % 8) ∧
      out.pc = s.pc + 44#64 ∧ out.readReg64 (copyCount message) = 0#64 ∧
      (∀ i < length, out.mem.read8 (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i) =
        s.mem.read8 (s.readReg64 (copySource message) + BitVec.ofNat 64 i)) ∧
      (∀ p, length ≤ (p - s.readReg64 (copyDestination message)).toNat →
        out.mem.cells p = s.mem.cells p) ∧
      nonvolatile out = nonvolatile s ∧ nonMemory out = nonMemory s ∧
      (∀ p n, s.mem.canRead p n = true → out.mem.canRead p n = true) ∧
      (∀ p n, out.mem.canWrite p n = s.mem.canWrite p n) := by
  let prefixBytes := 8 * (length / 8)
  let tailBytes := length % 8
  have size : prefixBytes + tailBytes = length := by dsimp [prefixBytes, tailBytes]; omega
  have prefixFits : prefixBytes ≤ length := by omega
  obtain ⟨wordEnd, words, front⟩ := copy_iterations message true s length (length / 8) count lengthBound
    prefixFits apart (readable true) (writable true)
  have headCount : wordEnd.readReg64 (copyCount message) = BitVec.ofNat 64 tailBytes := by
    have rest := front.remaining
    change wordEnd.readReg64 (copyCount message) =
      s.readReg64 (copyCount message) - BitVec.ofNat 64 prefixBytes at rest
    rw [rest, count, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) prefixFits]
    rw [show length - prefixBytes = tailBytes by omega]
  have tailFits : tailBytes < 8 := Nat.mod_lt _ (by decide)
  have small : (wordEnd.readReg64 (copyCount message)).toNat < 8 := by
    rw [headCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact tailFits
  let byteStart := (wordEnd.setPState (Arm64.AddWithCarry64 (wordEnd.readReg64 (copyCount message))
    (~~~8#64) true).2).setPC (wordEnd.pc + 24#64)
  have leaveWords : runCopyCycle message true wordEnd = some byteStart := word_copy_exits _ _ small
  have tailSrc : byteStart.readReg64 (copySource message) =
      s.readReg64 (copySource message) + BitVec.ofNat 64 prefixBytes := front.source
  have tailDest : byteStart.readReg64 (copyDestination message) =
      s.readReg64 (copyDestination message) + BitVec.ofNat 64 prefixBytes := front.dest
  have tailLength : byteStart.readReg64 (copyCount message) = BitVec.ofNat 64 tailBytes := headCount
  have tailApart (i : Nat) (inside : i < tailBytes) :
      tailBytes ≤ (byteStart.readReg64 (copySource message) + BitVec.ofNat 64 i -
        byteStart.readReg64 (copyDestination message)).toNat := by
    rw [tailSrc, tailDest, BitVec.add_assoc, ← BitVec.ofNat_add]
    have h := apart (prefixBytes + i) (by omega)
    have low : prefixBytes ≤
        (s.readReg64 (copySource message) + BitVec.ofNat 64 (prefixBytes + i) -
          s.readReg64 (copyDestination message)).toNat := by omega
    rw [copy_offset_distance _ _ _ low]
    omega
  have readTail (i : Nat) (fits : i + (copyWidth false).bytes ≤ tailBytes) :
      byteStart.mem.canRead (byteStart.readReg64 (copySource message) + BitVec.ofNat 64 i)
        (copyWidth false).bytes = true := by
    change i + 1 ≤ tailBytes at fits
    rw [tailSrc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact front.readable _ _ (readable false (prefixBytes + i) (by change _ + 1 ≤ _; omega))
  have writeTail (i : Nat) (fits : i + (copyWidth false).bytes ≤ tailBytes) :
      byteStart.mem.canWrite (byteStart.readReg64 (copyDestination message) + BitVec.ofNat 64 i)
        (copyWidth false).bytes = true := by
    change i + 1 ≤ tailBytes at fits
    rw [tailDest, BitVec.add_assoc, ← BitVec.ofNat_add]
    change wordEnd.mem.canWrite _ _ = true
    rw [front.writable]
    exact writable false (prefixBytes + i) (by change _ + 1 ≤ _; omega)
  obtain ⟨byteEnd, bytes, back⟩ := copy_iterations message false byteStart tailBytes tailBytes
    tailLength (by omega) (by change 1 * tailBytes ≤ tailBytes; omega) tailApart readTail writeTail
  have empty : byteEnd.readReg64 (copyCount message) = 0#64 := by
    have rest := back.remaining
    change byteEnd.readReg64 (copyCount message) =
      byteStart.readReg64 (copyCount message) - BitVec.ofNat 64 (1 * tailBytes) at rest
    rw [rest, tailLength, Nat.one_mul, BitVec.sub_self]
  let out := byteEnd.setPC (byteEnd.pc + 20#64)
  have returned : runCopyCycle message false byteEnd = some out := byte_copy_exits _ _ empty
  have advance : out.pc = s.pc + 44#64 := by
    change byteEnd.pc + 20#64 = _
    rw [back.pc]
    change wordEnd.pc + 24#64 + 20#64 = _
    rw [front.pc, BitVec.add_assoc]
    rfl
  obtain ⟨byWord, wordCount⟩ :=
    copy_iterations_fetched message true base s wordEnd length (length / 8) pc loaded running
      count lengthBound prefixFits apart (readable true) (writable true) words
  have wordHead := front.pc.trans pc
  have wordLive : wordEnd.status = .Running :=
    (congrArg Arm64.State.status front.nonMemory).trans running
  have byteStartLive : byteStart.status = .Running := wordLive
  have wordLeaves : ¬(copyWidth true).bytes ≤ (wordEnd.readReg64 (copyCount message)).toNat :=
    Nat.not_le_of_gt small
  obtain ⟨exitWords, wordExitCount⟩ := copy_cycle_fetched message true base wordEnd byteStart
    wordHead (byWord.keeps_code _ loaded) leaveWords byteStartLive (fun h => (wordLeaves h).elim)
  have wordSP : wordEnd.sp = s.sp := by
    change (nonMemory wordEnd).sp = (nonMemory s).sp
    rw [front.nonMemory]
  have wordDecision : decide ((copyWidth true).bytes ≤ (wordEnd.readReg64 (copyCount message)).toNat) = false := by simp [wordLeaves]
  simp only [copyCycleEvents, if_neg wordLeaves, wordDecision, Bool.false_eq_true, if_false,
    List.append_nil, front.pc, wordSP, Nat.add_zero] at exitWords wordExitCount
  have beforeBytes := byWord.append exitWords
  have bytePC : byteStart.pc = routineAddress base (copyRoutine message) + BitVec.ofNat 64 (copyOffset message false) := by
    change wordEnd.pc + 24#64 = _
    rw [wordHead, BitVec.add_assoc]
    cases message <;> rfl
  obtain ⟨byByte, byteCount⟩ :=
    copy_iterations_fetched message false base byteStart byteEnd tailBytes tailBytes
      bytePC (beforeBytes.keeps_code _ loaded) byteStartLive tailLength (by omega)
      (by change 1 * tailBytes ≤ tailBytes; omega) tailApart readTail writeTail bytes
  have throughBytes := beforeBytes.append byByte
  have finalLive : out.status = .Running :=
    (congrArg Arm64.State.status back.nonMemory).trans byteStartLive
  have byteLeaves : ¬(copyWidth false).bytes ≤ (byteEnd.readReg64 (copyCount message)).toNat := by
    rw [empty]
    decide
  obtain ⟨exitBytes, byteExitCount⟩ := copy_cycle_fetched message false base byteEnd out
    (back.pc.trans bytePC) (throughBytes.keeps_code _ loaded) returned finalLive (fun h => (byteLeaves h).elim)
  have byteStartPC : byteStart.pc = s.pc + 24#64 := by
    change wordEnd.pc + 24#64 = _
    rw [front.pc]
  have byteStartSP : byteStart.sp = s.sp := wordSP
  have byteEndSP : byteEnd.sp = s.sp := by
    change (nonMemory byteEnd).sp = _
    rw [back.nonMemory]
    exact byteStartSP
  have byteDecision : decide ((copyWidth false).bytes ≤ (byteEnd.readReg64 (copyCount message)).toNat) = false := by simp [byteLeaves]
  simp only [copyCycleEvents, if_neg byteLeaves, byteDecision, Bool.false_eq_true, if_false,
    List.append_nil, back.pc, byteStartPC, byteEndSP, Nat.add_zero] at exitBytes byteExitCount
  rw [byteStartPC, byteStartSP, tailSrc, tailDest] at byByte byteCount
  have through := ((byWord.append exitWords).append byByte).append exitBytes
  have frontNV : nonvolatile byteStart = nonvolatile s := front.nonvolatile
  have tailWritten : (copyWidth false).bytes * tailBytes = tailBytes := Nat.one_mul _
  refine ⟨out, through, ?_, advance, empty, ?_, ?_,
    back.nonvolatile.trans frontNV, ?_,
    fun p n h => back.readable p n (front.readable p n h),
    fun p n => (back.writable p n).trans (front.writable p n)⟩
  · simp only [tailBytes, prefixBytes] at byteCount
    simp only [copyPayloadEvents, List.length_append, wordCount, wordExitCount, byteCount, byteExitCount,
      copyGuardCount, Bool.false_eq_true, if_false, if_true]
    change (2 + 4) * (length / 8) + (2 + 0) + (1 + 4) * tailBytes + (1 + 0) = _
    dsimp [tailBytes]
    omega
  · intro i inside
    by_cases early : i < prefixBytes
    · have away := outside_span_of_offset (s.readReg64 (copyDestination message)) i prefixBytes tailBytes
        (.inl early) (by omega) (by omega)
      have same := back.frame (s.readReg64 (copyDestination message) + BitVec.ofNat 64 i) (by
        rw [tailWritten, tailDest]
        exact away)
      change byteEnd.mem.read8 _ = _
      unfold Arm64.Memory.read8
      rw [same]
      exact front.bytes i early
    let j := i - prefixBytes
    have index : prefixBytes + j = i := by dsimp [j]; omega
    have jFits : j < tailBytes := by omega
    have destByte : byteStart.readReg64 (copyDestination message) + BitVec.ofNat 64 j =
        s.readReg64 (copyDestination message) + BitVec.ofNat 64 i := by
      rw [tailDest, BitVec.add_assoc, ← BitVec.ofNat_add, index]
    have sourceByte : byteStart.readReg64 (copySource message) + BitVec.ofNat 64 j =
        s.readReg64 (copySource message) + BitVec.ofNat 64 i := by
      rw [tailSrc, BitVec.add_assoc, ← BitVec.ofNat_add, index]
    have value := back.bytes j (by rw [tailWritten]; exact jFits)
    rw [destByte, sourceByte] at value
    change byteEnd.mem.read8 _ = _
    rw [value]
    change wordEnd.mem.read8 (s.readReg64 (copySource message) + BitVec.ofNat 64 i) = _
    exact read8_of_cell _ (front.frame _ (prefixFits.trans (apart i inside)))
  · intro p away
    have same := back.frame p (by
      rw [tailWritten, tailDest, copy_offset_distance _ _ _ (prefixFits.trans away)]
      omega)
    exact same.trans (front.frame p (prefixFits.trans away))
  · change nonMemory (byteEnd.setPC _) = _
    rw [nonMemory_pc, back.nonMemory, nonMemory_pc, nonMemory_pstate, front.nonMemory]

end Crypto.HMACSHA256.ARM64
