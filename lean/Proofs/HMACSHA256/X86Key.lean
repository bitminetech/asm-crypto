import Proofs.HMACSHA256.X86CallSites
import Proofs.HMACSHA256.X86FetchedCopy
import Proofs.HMACSHA256.Callee

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.ARM64.Imported (memoryBytes32 address_delta)

theorem long_call_decoded :
    decodeRange key 0x39 3 = some [
      ⟨.mov .q (.reg .rdi) (.reg .rbx), 3⟩,
      ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩,
      ⟨.call (.rel (-4020#64)), 5⟩] := by decide +kernel

def longKeyCall (s : Cpu) : Cpu :=
  let args := (s.regs.set .rdi (s.regs.get .rbx)).set .rsi (s.regs.get .rbp)
  (({ s with regs := args }.push .q (s.rip + 11#64)).setRip (s.rip - 4009#64))

theorem key_call (s : Cpu) (live : s.ms = none)
    (target : canonical (s.rip - 4009#64) = true) :
    runRange key 0x39 3 s = some (longKeyCall s) := by
  unfold runRange
  rw [long_call_decoded]
  let a : Cpu := { s with regs := s.regs.set .rdi (s.regs.get .rbx), rip := s.rip + 3#64 }
  let b : Cpu := { a with regs := a.regs.set .rsi (a.regs.get .rbp), rip := a.rip + 3#64 }
  have aStep : step ⟨.mov .q (.reg .rdi) (.reg .rbx), 3⟩ s = a := move_reg _ _ _ _ live
  have bStep : step ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩ a = b := move_reg _ _ _ _ live
  have link : b.rip + 5#64 = s.rip + 11#64 := by simp only [b, a, BitVec.add_assoc]; rfl
  have branch : b.rip + 5#64 + (-4020#64) = s.rip - 4009#64 := by
    rw [link, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  change some (step ⟨.call (.rel (-4020#64)), 5⟩
    (step ⟨.mov .q (.reg .rsi) (.reg .rbp), 3⟩ (step ⟨.mov .q (.reg .rdi) (.reg .rbx), 3⟩ s))) = _
  rw [aStep, bStep, direct_call b (-4020#64) live (by rw [branch]; exact target), branch, link]
  simp (config := { decide := true }) [longKeyCall, a, b, Regs.get_set_ne, Cpu.push, Cpu.setRip, Cpu.setReg,
    Cpu.writeMem]

theorem key_call_target (base : Val) (s : Cpu) (pc : s.rip = routineAddress base key + 0x39#64) :
    (longKeyCall s).rip = shaAddress base := by
  have relocation : BitVec.ofInt 64 key.offset + (0x39#64 + (-4009#64)) =
      BitVec.ofInt 64 sha256Offset := by decide +kernel
  change s.rip - 4009#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc, relocation]

private theorem key_output (s : Cpu) : (longKeyCall s).regs.get .rsi = s.regs.get .rbp := by
  simp (config := { decide := true }) [longKeyCall, Cpu.push, Cpu.setRip, Cpu.setReg, Cpu.writeMem,
    Regs.get_set_ne, Regs.get_set_same]

/-- After the clear and the long-key branch, the actual SHA-256 call fills
the first 32 bytes of K0 and its real frame preserves the trailing zeros. -/
theorem long_key_after_clear (base : Val) (s : Cpu) (input : ByteList) (extent : Nat)
    (authority : Crypto.Baseline.Authority) (long : 64 < input.bytes.size)
    (pc : s.rip = routineAddress base key + 0x39#64) (live : s.ms = none)
    (shaCanonical : canonical (shaAddress base) = true)
    (entry : PermissionEntry (shaAddress base) (longKeyCall s) input extent authority)
    (zeroTail : ∀ i : Fin 64, 32 ≤ i.val →
      (longKeyCall s).mem.read (s.regs.get .rbp + BitVec.ofNat 64 i.val) = 0#8)
    (offStack : ∀ i : Fin 64, 32 ≤ i.val →
      ¬ (stackRegion (longKeyCall s)).Contains (s.regs.get .rbp + BitVec.ofNat 64 i.val)) :
    ∃ out events, runRange key 0x39 3 s = some (longKeyCall s) ∧
      NativeSerial (shaAddress base) (longKeyCall s) out input extent authority events ∧
      (∀ i : Fin 64, out.mem.read (s.regs.get .rbp + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) := by
  obtain ⟨out, events, hashing, _⟩ := sha256_callee entry
  have branch : canonical (s.rip - 4009#64) = true := by
    change canonical (longKeyCall s).rip = true
    rw [key_call_target base s pc]
    exact shaCanonical
  refine ⟨out, events, key_call s live branch, hashing, ?_⟩
  intro i
  rw [hmacKey_long_byte input long entry.bound]
  by_cases first : i.val < 32
  · rw [if_pos first]
    let j : Fin 32 := ⟨i.val, first⟩
    have byte := congrArg (fun v : Vector (BitVec 8) 32 => v[j.val]) hashing.result.digest
    have index : i.val < (EthLib.Base.packBytes (sha256 input).2).size := by
      change i.val < (sha256 input).2.toArray.size
      rw [(sha256 input).2.size_toArray]
      exact first
    rw [getElem!_pos (EthLib.Base.packBytes (sha256 input).2) i.val index, ← key_output]
    simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map, byteView_read] using byte
  · rw [if_neg first]
    let p := s.regs.get .rbp + BitVec.ofNat 64 i.val
    have offOutput : ¬ (outputRegion (longKeyCall s)).Contains p := by
      intro inside
      change ((longKeyCall s).regs.get .rsi).toNat ≤ p.toNat ∧
        p.toNat < ((longKeyCall s).regs.get .rsi).toNat + 32 at inside
      rw [key_output] at inside
      have delta : (p - s.regs.get .rbp).toNat = i.val := by
        rw [show p - s.regs.get .rbp = BitVec.ofNat 64 i.val from address_delta _ _,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      rw [BitVec.toNat_sub] at delta
      have max := (s.regs.get .rbp).isLt
      omega
    rw [hashing.result.frame p offOutput (offStack i (by omega))]
    exact zeroTail i (by omega)

/-- The loaded repeated copy writes the actual short key and preserves all
the zero padding left by the clear. The return path starts at the next
instruction with the direction flag preserved by the copy. -/
theorem short_key_after_clear (base : Val) (s : Cpu) (input : ByteList)
    (short : input.bytes.size ≤ 64)
    (code : key.Loaded base s.mem.read) (pc : s.rip = base + 0x35#64)
    (canonicalPC : canonical s.rip = true) (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 input.bytes.size)
    (payload : ∀ i, i < input.bytes.size →
      s.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i) = input.bytes[i]!.toBitVec)
    (zeroTail : ∀ i : Fin 64, input.bytes.size ≤ i.val →
      s.mem.read (s.regs.get .rdi + BitVec.ofNat 64 i.val) = 0#8)
    (separated : ∀ i, i < input.bytes.size →
      input.bytes.size ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (codeSeparate : ∀ i, i < key.image.size →
      input.bytes.size ≤ (base + BitVec.ofNat 64 i - s.regs.get .rdi).toNat) :
    ∃ out, loadedSteps key base s (input.bytes.size + 1) = some out ∧
      out.rip = base + 0x37#64 ∧ out.ms = none ∧
      (∀ i : Fin 64, out.mem.read (s.regs.get .rdi + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) := by
  have executed := short_key_copy_loaded base s input.bytes.size code pc canonicalPC live direction
    length short separated codeSeparate
  obtain ⟨next, outLive, _, bytes, frame⟩ := copy_done s input.bytes.size live direction length (by omega) separated
  have nextPc : (copySteps s (input.bytes.size + 1)).rip = base + 0x37#64 := by
    rw [next, pc, BitVec.add_assoc]
    rfl
  refine ⟨copySteps s (input.bytes.size + 1), executed, nextPc, outLive, ?_⟩
  intro i
  rw [hmacKey_short_byte input short i]
  by_cases front : i.val < input.bytes.size
  · rw [if_pos front, bytes _ front]
    exact payload _ front
  · rw [if_neg front]
    have off : input.bytes.size ≤ (s.regs.get .rdi + BitVec.ofNat 64 i.val - s.regs.get .rdi).toNat := by
      rw [address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    rw [frame _ off]
    exact zeroTail i (by omega)

end Crypto.HMACSHA256.X86_64
