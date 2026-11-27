import Proofs.HMACSHA256.X86Repeat
import Proofs.HMACSHA256.LinkedExecution

namespace Crypto.HMACSHA256.X86_64

open X86

def loadedSteps (routine : Routine) (base : Address) (s : Cpu) : Nat → Option Cpu
  | 0 => some s
  | n + 1 => (loadedSteps routine base s n).bind (stepLoaded routine base)

/-- Execute the entire copied portion of a repeated move by fetching it from
the loaded routine on every iteration, including the final zero-count step. -/
theorem copy_loaded (routine : Routine) (base : Address) (off : Nat) (s : Cpu) (count : Nat)
    (decoded : decodeAt routine off = some copyByte) (addressable : off < 2 ^ 64)
    (within : off + 2 ≤ routine.image.size) (code : routine.Loaded base s.mem.read)
    (entryPC : s.rip = base + BitVec.ofNat 64 off) (canonicalPC : canonical s.rip = true)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 count) (bound : count < 2 ^ 64)
    (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (codeSeparate : ∀ i, i < routine.image.size →
      count ≤ (base + BitVec.ofNat 64 i - s.regs.get .rdi).toNat) :
    loadedSteps routine base s (count + 1) = some (copySteps s (count + 1)) := by
  have proofPrefix := copySteps_prefix s count
  have canFetch (n : Nat) (nBound : n ≤ count) :
      stepLoaded routine base (copySteps s n) = some (X86.step copyByte (copySteps s n)) := by
    have p := proofPrefix n live direction length bound separated nBound
    have stored : routine.Loaded base (copySteps s n).mem.read := by
      intro i hi
      exact (p.frame _ (nBound.trans (codeSeparate i hi))).trans (code i hi)
    have valid : canonical (copySteps s n).rip = true := by rw [p.rip]; exact canonicalPC
    exact step_at routine base _ off copyByte stored (p.rip.trans entryPC)
      addressable decoded (by decide) within p.live valid
  have partialRun (n : Nat) (nBound : n ≤ count) :
      loadedSteps routine base s n = some (copySteps s n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [loadedSteps, ih (by omega), Option.bind_some, canFetch n (by omega), copySteps]
  simp only [loadedSteps, partialRun count (by omega), Option.bind_some,
    canFetch count (by omega), copySteps]

set_option maxRecDepth 8192 in
theorem entry_message_copy_loaded (base : Address) (s : Cpu) (count : Nat)
    (code : entry.Loaded base s.mem.read)
    (entryPC : s.rip = base + 0xe9#64) (canonicalPC : canonical s.rip = true)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 count) (bound : count < 2 ^ 64)
    (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (codeSeparate : ∀ i, i < entry.image.size →
      count ≤ (base + BitVec.ofNat 64 i - s.regs.get .rdi).toNat) :
    loadedSteps entry base s (count + 1) = some (copySteps s (count + 1)) :=
  copy_loaded entry base 0xe9 s count repeat_decoded.1 (by decide) (by decide)
    code entryPC canonicalPC live direction length bound separated codeSeparate

set_option maxRecDepth 8192 in
theorem short_key_copy_loaded (base : Address) (s : Cpu) (count : Nat)
    (code : key.Loaded base s.mem.read)
    (entryPC : s.rip = base + 0x35#64) (canonicalPC : canonical s.rip = true)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 count) (bound : count ≤ 64)
    (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (codeSeparate : ∀ i, i < key.image.size →
      count ≤ (base + BitVec.ofNat 64 i - s.regs.get .rdi).toNat) :
    loadedSteps key base s (count + 1) = some (copySteps s (count + 1)) :=
  copy_loaded key base 0x35 s count repeat_decoded.2.1 (by decide) (by decide)
    code entryPC canonicalPC live direction length (by omega) separated codeSeparate

end Crypto.HMACSHA256.X86_64
