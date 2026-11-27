import Proofs.HMACSHA256.X86FetchedCopy
import Proofs.HMACSHA256.ARM64Memory
import Proofs.X86_64.Memory64

namespace Crypto.HMACSHA256.X86_64

open X86
open Crypto.X86_64 (byteView byteView_read byteView_write64)
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_byte writeWords_outside)

def storeSteps (s : Cpu) : Nat → Cpu
  | 0 => s
  | n + 1 => X86.step storeWord (storeSteps s n)

structure ZeroPrefix (start out : Cpu) (n : Nat) : Prop where
  rip : out.rip = start.rip
  live : out.ms = none
  flags : out.flags = start.flags
  dest : out.regs.get .rdi = start.regs.get .rdi + BitVec.ofNat 64 (8 * n)
  count : out.regs.get .rcx = BitVec.ofNat 64 (8 - n)
  accumulator : out.regs.get .rax = 0#64
  memory : byteView out.mem = writeWords (byteView start.mem) (start.regs.get .rdi) (fun _ => 0#64) n

theorem zero_prefix (s : Cpu) (n : Nat) (bound : n ≤ 8)
    (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx = 8#64) (zero : s.regs.get .rax = 0#64) :
    ZeroPrefix s (storeSteps s n) n := by
  induction n with
  | zero =>
    exact ⟨rfl, live, rfl, by simp [storeSteps], count, zero, rfl⟩
  | succ n ih =>
    let mid := storeSteps s n
    have p := ih (by omega)
    have remaining : mid.regs.get .rcx = BitVec.ofNat 64 (8 - n) := p.count
    have nonempty : mid.regs.get .rcx ≠ 0#64 := by
      rw [remaining]
      intro eq
      have ordinary := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 - n < 2 ^ 64)] at ordinary
      change 8 - n = 0 at ordinary
      omega
    have df : mid.flags.df = false := by rw [p.flags]; exact direction
    change ZeroPrefix s (X86.step storeWord mid) (n + 1)
    rw [storeWord_step mid p.live df nonempty]
    refine ⟨p.rip, p.live, p.flags, ?_, ?_, ?_, ?_⟩
    · have old := p.dest
      change mid.regs.get .rdi = _ at old
      simp [old, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
    · simp only [Regs.get_set_same, remaining]
      have eq : 8 - n = (8 - (n + 1)) + 1 := by omega
      nth_rw 1 [eq]
      simp only [BitVec.ofNat_add, BitVec.add_sub_cancel]
    · exact p.accumulator
    · change byteView (mid.mem.writeSize .q (mid.regs.get .rdi) (mid.regs.get .rax)) = _
      rw [byteView_write64, p.dest, p.accumulator, p.memory]
      rfl

/-- The helper's REP STOSQ clears 64 bytes and preserves every byte outside
the output block. The initial contents of that block may be arbitrary. -/
theorem clear_key_block (s : Cpu) (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx = 8#64) (zero : s.regs.get .rax = 0#64) :
    let out := storeSteps s 9
    out.rip = s.rip + 3#64 ∧ out.ms = none ∧
      (∀ i : Fin 64, out.mem.read (s.regs.get .rdi + BitVec.ofNat 64 i.val) = 0#8) ∧
      (∀ p, 64 ≤ (p - s.regs.get .rdi).toNat → out.mem.read p = s.mem.read p) := by
  have p := zero_prefix s 8 (by decide) live direction count zero
  have empty : (storeSteps s 8).regs.get .rcx = 0#64 := p.count
  dsimp only
  rw [show storeSteps s 9 = X86.step storeWord (storeSteps s 8) from rfl,
    storeWord_empty _ p.live empty]
  refine ⟨congrArg (· + 3#64) p.rip, p.live, ?_, ?_⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have wrote := writeWords_byte (byteView s.mem) (s.regs.get .rdi) (fun _ => 0#64)
      8 (i.val / 8) byte lt (by decide)
    have address : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    change (storeSteps s 8).mem.read _ = _
    rw [← byteView_read, p.memory]
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, address, BitVec.extractLsb'_zero] using wrote
  · intro address outside
    change (storeSteps s 8).mem.read address = s.mem.read address
    rw [← byteView_read, p.memory, ← byteView_read]
    unfold Arm64.Memory.read8
    rw [writeWords_outside _ _ _ 8 _ outside]

set_option maxRecDepth 8192 in
theorem key_clear_loaded (base : Address) (s : Cpu)
    (code : key.Loaded base s.mem.read)
    (pc : s.rip = base + 0x1e#64) (valid : canonical s.rip = true)
    (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx = 8#64) (zero : s.regs.get .rax = 0#64)
    (outside : ∀ j, j < key.image.size →
      64 ≤ (base + BitVec.ofNat 64 j - s.regs.get .rdi).toNat) :
    loadedSteps key base s 9 = some (storeSteps s 9) := by
  have iterate (n : Nat) (nBound : n ≤ 8) :
      stepLoaded key base (storeSteps s n) = some (X86.step storeWord (storeSteps s n)) := by
    have p := zero_prefix s n nBound live direction count zero
    have loaded : key.Loaded base (storeSteps s n).mem.read := by
      intro j hj
      let address := base + BitVec.ofNat 64 j
      have away : 8 * n ≤ (address - s.regs.get .rdi).toNat := by
        have h := outside j hj
        change 64 ≤ (address - s.regs.get .rdi).toNat at h
        omega
      have preserved : (storeSteps s n).mem.read address = s.mem.read address := by
        rw [← byteView_read, p.memory, ← byteView_read]
        unfold Arm64.Memory.read8
        rw [writeWords_outside _ _ _ n _ away]
      exact preserved.trans (code j hj)
    have entryPC : (storeSteps s n).rip = base + 0x1e#64 := p.rip.trans pc
    have canonicalPC : canonical (storeSteps s n).rip = true := by rw [p.rip]; exact valid
    exact step_at key base _ 0x1e storeWord loaded entryPC (by decide)
      repeat_decoded.2.2 (by decide) (by decide) p.live canonicalPC
  have ran (n : Nat) (nBound : n ≤ 8) : loadedSteps key base s n = some (storeSteps s n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [loadedSteps, ih (by omega), Option.bind_some, iterate n (by omega), storeSteps]
  change (loadedSteps key base s 8).bind (stepLoaded key base) = _
  rw [ran 8 (by decide), Option.bind_some, iterate 8 (by decide)]
  rfl

theorem clear_key_registers (s : Cpu) (live : s.ms = none) (direction : s.flags.df = false)
    (count : s.regs.get .rcx = 8#64) (zero : s.regs.get .rax = 0#64) :
    (storeSteps s 9).flags.df = false ∧
    ∀ r, r ≠ .rdi → r ≠ .rcx → (storeSteps s 9).regs.get r = s.regs.get r := by
  have keep (n : Nat) (bound : n ≤ 8) (r : GPR) (rdi : r ≠ .rdi) (rcx : r ≠ .rcx) :
      (storeSteps s n).regs.get r = s.regs.get r := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let mid := storeSteps s n
      have p := zero_prefix s n (by omega) live direction count zero
      have remaining : mid.regs.get .rcx ≠ 0#64 := by
        rw [p.count]
        intro h
        have eq := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 - n < 2 ^ 64)] at eq
        change 8 - n = 0 at eq
        omega
      change (step storeWord mid).regs.get r = s.regs.get r
      rw [storeWord_step mid p.live (p.flags.symm ▸ direction) remaining]
      simp only [Regs.get_set_ne _ _ _ _ rdi.symm, Regs.get_set_ne _ _ _ _ rcx.symm]
      exact ih (by omega)
  have p := zero_prefix s 8 (by decide) live direction count zero
  have empty : (storeSteps s 8).regs.get .rcx = 0#64 := p.count
  change (step storeWord (storeSteps s 8)).flags.df = false ∧ _
  rw [storeWord_empty _ p.live empty]
  refine ⟨p.flags.symm ▸ direction, ?_⟩
  intro r rdi rcx
  change (step storeWord (storeSteps s 8)).regs.get r = s.regs.get r
  rw [storeWord_empty _ p.live empty]
  exact keep 8 (by decide) r rdi rcx

end Crypto.HMACSHA256.X86_64
