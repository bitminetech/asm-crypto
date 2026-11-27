import Proofs.HMACSHA256.X86Code
import Proofs.ARM64.ImportedMemory

namespace Crypto.HMACSHA256.X86_64

open X86
open Crypto.ARM64.Imported (address_delta)

def copyByte : Instr := ⟨.repstrop .rep .movs .b, 2⟩

def storeWord : Instr := ⟨.repstrop .rep .stos .q, 3⟩

theorem repeat_decoded :
    decodeAt entry 0xe9 = some copyByte ∧ decodeAt key 0x35 = some copyByte ∧
    decodeAt key 0x1e = some storeWord := by decide +kernel

private theorem readByte_value (m : Mem) (p : Val) :
    m.readSize .b p = (m.read p).setWidth 64 := by
  simp [Mem.readSize, Mem.readN, Size.bytes]

private theorem writeByte_value (m : Mem) (p : Val) (v : BitVec 8) :
    m.writeSize .b p (v.setWidth 64) = m.write p v := by
  simp [Mem.writeSize, Mem.writeN, Size.bytes, BitVec.setWidth_setWidth_of_le]

theorem copyByte_empty (s : Cpu) (live : s.ms = none) (count : s.regs.get .rcx = 0) :
    X86.step copyByte s = { s with rip := s.rip + 2#64 } := by
  simp (config := { decide := true }) [copyByte, X86.step, Cpu.stopped, Cpu.setRip, live, count]

/-- A repeated move with DF clear, as required by the core ABI. One
nonempty model step writes one byte and stays at the prefix instruction. -/
theorem copyByte_step (s : Cpu) (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx ≠ 0#64) :
    X86.step copyByte s = { s with
      regs := (((s.regs.set .rsi (s.regs.get .rsi + 1#64)).set .rdi
        (s.regs.get .rdi + 1#64)).set .rcx (s.regs.get .rcx - 1#64))
      mem := s.mem.write (s.regs.get .rdi) (s.mem.read (s.regs.get .rsi)) } := by
  simp (config := { decide := true }) [copyByte, X86.step, Cpu.stopped, Cpu.setRip, live, count,
    RepPrefix.terminates, stringIter, direction, Size.bytes, Cpu.readMem, Cpu.writeMem,
    Cpu.setReg, Value.writeView, readByte_value, writeByte_value]

theorem storeWord_empty (s : Cpu) (live : s.ms = none) (count : s.regs.get .rcx = 0) :
    X86.step storeWord s = { s with rip := s.rip + 3#64 } := by
  simp (config := { decide := true }) [storeWord, X86.step, Cpu.stopped, Cpu.setRip, live, count]

theorem storeWord_step (s : Cpu) (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx ≠ 0#64) :
    X86.step storeWord s = { s with
      regs := (s.regs.set .rdi (s.regs.get .rdi + 8#64)).set .rcx (s.regs.get .rcx - 1#64)
      mem := s.mem.writeSize .q (s.regs.get .rdi) (s.regs.get .rax) } := by
  simp (config := { decide := true }) [storeWord, X86.step, Cpu.stopped, Cpu.setRip, live, count,
    RepPrefix.terminates, stringIter, direction, Size.bytes, Cpu.writeMem,
    Cpu.setReg, Cpu.getReg, Value.writeView, Value.trunc]
  rw [show Size.q.mask = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

def copySteps (s : Cpu) : Nat → Cpu
  | 0 => s
  | n + 1 => X86.step copyByte (copySteps s n)

structure CopyPrefix (start out : Cpu) (count copied : Nat) : Prop where
  rip : out.rip = start.rip
  live : out.ms = none
  flags : out.flags = start.flags
  source : out.regs.get .rsi = start.regs.get .rsi + BitVec.ofNat 64 copied
  dest : out.regs.get .rdi = start.regs.get .rdi + BitVec.ofNat 64 copied
  remaining : out.regs.get .rcx = BitVec.ofNat 64 (count - copied)
  otherRegs : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → out.regs.get r = start.regs.get r
  bytes : ∀ i, i < copied → out.mem.read (start.regs.get .rdi + BitVec.ofNat 64 i) =
    start.mem.read (start.regs.get .rsi + BitVec.ofNat 64 i)
  frame : ∀ p, copied ≤ (p - start.regs.get .rdi).toNat → out.mem.read p = start.mem.read p

/-- The same REP MOVSB fragment copies short keys and arbitrary admitted
message lengths. The disjoint source remains stable during every iteration. -/
theorem copySteps_prefix (s : Cpu) (count copied : Nat)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 count) (bound : count < 2 ^ 64)
    (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (copiedBound : copied ≤ count) : CopyPrefix s (copySteps s copied) count copied := by
  induction copied with
  | zero =>
    exact ⟨rfl, live, rfl, by simp [copySteps], by simp [copySteps],
      by simpa [copySteps] using length, fun _ _ _ _ => rfl, fun _ h => by omega, fun _ _ => rfl⟩
  | succ n ih =>
    let mid := copySteps s n
    have prev := ih (by omega)
    have countPos : mid.regs.get .rcx ≠ 0 := by
      rw [prev.remaining]
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : count - n < 2 ^ 64)] at eqNat
      change count - n = 0 at eqNat
      omega
    have flag : mid.flags.df = false := by rw [prev.flags]; exact direction
    have go := copyByte_step mid prev.live flag countPos
    change CopyPrefix s (X86.step copyByte mid) count (n + 1)
    rw [go]
    have remaining : BitVec.ofNat 64 (count - n) - 1#64 =
        BitVec.ofNat 64 (count - (n + 1)) := by
      have h : count - n = (count - (n + 1)) + 1 := by omega
      nth_rw 1 [h]
      simp only [BitVec.ofNat_add, BitVec.add_sub_cancel]
    have src := prev.frame (s.regs.get .rsi + BitVec.ofNat 64 n)
      (Nat.le_trans (by omega) (separated n (by omega)))
    refine ⟨prev.rip, prev.live, prev.flags, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hs : mid.regs.get .rsi = s.regs.get .rsi + BitVec.ofNat 64 n := prev.source
      simp [hs, BitVec.ofNat_add, BitVec.add_assoc]
    · have hd : mid.regs.get .rdi = s.regs.get .rdi + BitVec.ofNat 64 n := prev.dest
      simp [hd, BitVec.ofNat_add, BitVec.add_assoc]
    · have hc : mid.regs.get .rcx = BitVec.ofNat 64 (count - n) := prev.remaining
      simpa only [Regs.get_set_same, hc] using remaining
    · intro reg notSI notDI notCX
      change ((((mid.regs.set .rsi (mid.regs.get .rsi + 1#64)).set .rdi
        (mid.regs.get .rdi + 1#64)).set .rcx (mid.regs.get .rcx - 1#64)).get reg) = _
      rw [Regs.get_set_ne _ _ _ _ (Ne.symm notCX), Regs.get_set_ne _ _ _ _ (Ne.symm notDI),
        Regs.get_set_ne _ _ _ _ (Ne.symm notSI)]
      exact prev.otherRegs reg notSI notDI notCX
    · intro i small
      change (mid.mem.write (mid.regs.get .rdi) (mid.mem.read (mid.regs.get .rsi))).read _ = _
      rw [prev.dest, prev.source, src]
      by_cases last : i = n
      · subst i
        exact Mem.read_write_same _ _ _
      · have different : s.regs.get .rdi + BitVec.ofNat 64 i ≠
            s.regs.get .rdi + BitVec.ofNat 64 n := by
          intro eq
          have ineq := (BitVec.add_right_inj _).mp eq
          have numbers := congrArg BitVec.toNat ineq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at numbers
          exact last numbers
        rw [Mem.read_write_ne _ _ _ _ different]
        exact prev.bytes i (by omega)
    · intro p away
      change (mid.mem.write (mid.regs.get .rdi) (mid.mem.read (mid.regs.get .rsi))).read p = _
      have different : p ≠ mid.regs.get .rdi := by
        intro eq
        rw [eq, prev.dest, address_delta, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at away
        omega
      rw [Mem.read_write_ne _ _ _ _ different]
      exact prev.frame p (by omega)

theorem copy_done (s : Cpu) (count : Nat) (live : s.ms = none)
    (direction : s.flags.df = false) (length : s.regs.get .rcx = BitVec.ofNat 64 count)
    (bound : count < 2 ^ 64) (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat) :
    let after := copySteps s (count + 1)
    after.rip = s.rip + 2#64 ∧ after.ms = none ∧ after.flags = s.flags ∧
      (∀ i, i < count → after.mem.read (s.regs.get .rdi + BitVec.ofNat 64 i) =
        s.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i)) ∧
      (∀ p, count ≤ (p - s.regs.get .rdi).toNat → after.mem.read p = s.mem.read p) := by
  have prev := copySteps_prefix s count count live direction length bound separated (Nat.le_refl _)
  dsimp only [copySteps]
  have empty : (copySteps s count).regs.get .rcx = 0 := by rw [prev.remaining, Nat.sub_self]; rfl
  simp only [copyByte_empty _ prev.live empty]
  exact ⟨congrArg (· + 2#64) prev.rip, prev.live, prev.flags, prev.bytes, prev.frame⟩

theorem copy_done_register (s : Cpu) (count : Nat) (live : s.ms = none)
    (direction : s.flags.df = false) (length : s.regs.get .rcx = BitVec.ofNat 64 count)
    (bound : count < 2 ^ 64) (separated : ∀ i, i < count →
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 i - s.regs.get .rdi).toNat)
    (r : GPR) (rsi : r ≠ .rsi) (rdi : r ≠ .rdi) (rcx : r ≠ .rcx) :
    (copySteps s (count + 1)).regs.get r = s.regs.get r := by
  have prev := copySteps_prefix s count count live direction length bound separated (Nat.le_refl _)
  change (X86.step copyByte (copySteps s count)).regs.get r = _
  have empty : (copySteps s count).regs.get .rcx = 0#64 := by rw [prev.remaining, Nat.sub_self]
  rw [copyByte_empty _ prev.live empty]
  exact prev.otherRegs r rsi rdi rcx

end Crypto.HMACSHA256.X86_64
