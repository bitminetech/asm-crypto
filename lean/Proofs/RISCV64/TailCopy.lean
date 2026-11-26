import Proofs.RISCV64.RegisterFrame
import Proofs.ARM64.ImportedTailCopy

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (read8_write8 cells_write8_outside byte128_address_inj
  address_delta)

def tailGuard : Instruction := ⟨.branch .geu 30 7 24, 4⟩
def tailBack : Instruction := ⟨.jump (-22), 2⟩

def copyByte : List Instruction :=
  [⟨.add 31 28 30, 4⟩, ⟨.load .byte 5 31 0, 4⟩, ⟨.add 31 29 30, 4⟩,
   ⟨.store .byte 5 31 0, 4⟩, ⟨.addi 30 30 1, 2⟩]

def tailCycle : List Instruction := tailGuard :: (copyByte ++ [tailBack])

def tailPrefix : Nat → List Instruction
  | 0 => []
  | n+1 => tailPrefix n ++ tailCycle

def tailCode (count : Nat) : List Instruction := tailPrefix count ++ [tailGuard]

private theorem tailGuard_decoded : decodeAt 0x52 = some tailGuard := by decide +kernel
private theorem tailBack_decoded : decodeAt 0x68 = some tailBack := by decide +kernel
private theorem copyByte_decoded : decodeSeq 0x56 5 = some copyByte := by decide +kernel

private theorem tail_taken (s : CPU) (n rem : Nat)
    (nb : n < 64) (rb : rem < 64)
    (idx : s.reg 30#5 = BitVec.ofNat 64 n) (len : s.reg 7#5 = BitVec.ofNat 64 rem) :
    Branch.taken .geu (s.reg 30#5) (s.reg 7#5) = decide (rem ≤ n) := by
  unfold Branch.taken
  rw [idx, len, BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2^64), Nat.mod_eq_of_lt (by omega : rem < 2^64)]
  by_cases h : n < rem <;> simp [h, show rem ≤ n ↔ ¬n < rem by omega]

private theorem tail_no_return (n : Nat) (i : Instruction) (hi : i ∈ tailPrefix n) :
    i.op ≠ .ret := by
  induction n with
  | zero => simp [tailPrefix] at hi
  | succ n ih =>
    rcases List.mem_append.mp hi with before | one
    · exact ih before
    · have check : tailCycle.all (fun j => !(j.op == .ret)) = true := by decide
      simpa using List.all_eq_true.mp check i one

private theorem tail_registers (s : CPU) (r : Reg)
    (copyPublic : r = 7 ∨ r = 28 ∨ r = 29) :
    (run tailCycle s).reg r = s.reg r := by
  apply run_reg_unchanged
  intro i hi
  rcases copyPublic with rfl | rfl | rfl
  all_goals
    first
    | have check : tailCycle.all (fun j => !(j.op.destination == some 7)) = true := by decide
      simpa using List.all_eq_true.mp check i hi
    | have check : tailCycle.all (fun j => !(j.op.destination == some 28)) = true := by decide
      simpa using List.all_eq_true.mp check i hi
    | have check : tailCycle.all (fun j => !(j.op.destination == some 29)) = true := by decide
      simpa using List.all_eq_true.mp check i hi

private theorem run_cons (i : Instruction) (code : List Instruction) (s : CPU) :
    run (i :: code) s = run code (i.step s) := rfl

set_option maxHeartbeats 3000000 in
private theorem tail_cycle (base : Addr) (s : CPU) (n rem : Nat)
    (more : n < rem) (rb : rem < 64) (pc : s.pc = base + 0x52)
    (idx : s.reg 30 = BitVec.ofNat 64 n) (len : s.reg 7 = BitVec.ofNat 64 rem) :
    let out := run tailCycle s
    ImageExecution base s tailCycle out ∧ out.pc = base + 0x52 ∧
      out.reg 30 = BitVec.ofNat 64 (n + 1) ∧
      out.mem = s.mem.write8 (s.reg 29 + BitVec.ofNat 64 n)
        (s.mem.read8 (s.reg 28 + BitVec.ofNat 64 n)) := by
  have branch := tail_taken s n rem (by omega) rb idx len
  have falls : tailGuard.step s = s.advance 4 := by
    simp [tailGuard, Instruction.step, branch, show ¬rem ≤ n by omega]
  have start : (tailGuard.step s).pc = base + 0x56 := by rw [falls, pc_advance, pc, BitVec.add_assoc]; rfl
  have linear : copyByte.all Instruction.linear = true := by decide
  have dataPath := ImageExecution.linear_run base (tailGuard.step s) copyByte 0x56 start
    (by decide) copyByte_decoded linear
  have jumpPC : (run copyByte (tailGuard.step s)).pc = base + 0x68 := by
    rw [linear_end_pc _ _ linear, start, BitVec.add_assoc]; rfl
  have jump : ImageExecution base (run copyByte (tailGuard.step s)) [tailBack]
      (tailBack.step (run copyByte (tailGuard.step s))) :=
    .cons (by rw [offset_eq jumpPC (by decide)]; exact tailBack_decoded) (by simp) (.nil _)
  have finish := dataPath.append jump (fun i hi => Instruction.linear_ne_return (List.all_eq_true.mp linear i hi))
  refine ⟨.cons (by rw [offset_eq pc (by decide)]; exact tailGuard_decoded)
    (by simp [tailGuard]) finish, ?_⟩
  dsimp only
  rw [tailCycle, run_cons, falls]
  change s.reg 30#5 = BitVec.ofNat 64 n at idx
  simp (config := { decide := true }) [run, copyByte, tailBack, Instruction.step, pc,
    BitVec.add_assoc, Width.load, Width.store, idx, BitVec.ofNat_add]
  simp [CPU.reg, CPU.put]

private structure CopyPrefix (base : Addr) (s out : CPU) (rem n : Nat) : Prop where
  pc : out.pc = base + 0x52
  index : out.reg 30 = BitVec.ofNat 64 n
  limit : out.reg 7 = BitVec.ofNat 64 rem
  input : out.reg 28 = s.reg 28
  padding : out.reg 29 = s.reg 29
  copied : ∀ j, j < n → out.mem.read8 (s.reg 29 + BitVec.ofNat 64 j) =
    s.mem.read8 (s.reg 28 + BitVec.ofNat 64 j)
  frame : ∀ p, n ≤ (p - s.reg 29).toNat → out.mem.cells p = s.mem.cells p

private theorem copy_prefix (base : Addr) (s : CPU) (rem : Nat) (rb : rem < 64)
    (pc : s.pc = base + 0x52) (idx : s.reg 30 = 0) (len : s.reg 7 = BitVec.ofNat 64 rem)
    (apart : ∀ t : Fin rem, 128 ≤ (s.reg 28 + BitVec.ofNat 64 t.val - s.reg 29).toNat)
    (n : Nat) (bound : n ≤ rem) :
    ∃ out, ImageExecution base s (tailPrefix n) out ∧ CopyPrefix base s out rem n := by
  induction n with
  | zero =>
    exact ⟨s, .nil _, ⟨pc, idx, len, rfl, rfl, fun _ h => by omega, fun _ _ => rfl⟩⟩
  | succ n ih =>
    obtain ⟨mid, prior, h⟩ := ih (by omega)
    obtain ⟨cycle, pos, count, write⟩ :=
      tail_cycle base mid n rem (by omega) rb h.pc h.index h.limit
    let out := run tailCycle mid
    have data : out.mem = mid.mem.write8 (s.reg 29 + BitVec.ofNat 64 n)
        (mid.mem.read8 (s.reg 28 + BitVec.ofNat 64 n)) := by
      simpa only [h.input, h.padding] using write
    have source : mid.mem.read8 (s.reg 28 + BitVec.ofNat 64 n) =
        s.mem.read8 (s.reg 28 + BitVec.ofNat 64 n) := by
      have sep := apart ⟨n, by omega⟩
      change 128 ≤ (s.reg 28 + BitVec.ofNat 64 n - s.reg 29).toNat at sep
      unfold Arm64.Memory.read8
      rw [h.frame _ (by omega)]
    refine ⟨out, prior.append cycle (tail_no_return n),
      ⟨pos, count, (tail_registers mid 7 (Or.inl rfl)).trans h.limit,
        (tail_registers mid 28 (Or.inr (Or.inl rfl))).trans h.input,
        (tail_registers mid 29 (Or.inr (Or.inr rfl))).trans h.padding, ?_, ?_⟩⟩
    · intro j hj
      have address : (s.reg 29 + BitVec.ofNat 64 j = s.reg 29 + BitVec.ofNat 64 n) ↔ j = n :=
        byte128_address_inj (s.reg 29) ⟨j, by omega⟩ ⟨n, by omega⟩
      rw [data, read8_write8]
      by_cases same : j = n
      · subst j
        rw [if_pos rfl, source]
      · rw [if_neg (fun h => same (address.mp h))]
        exact h.copied j (by omega)
    · intro p outside
      rw [data]
      have ne : p ≠ s.reg 29 + BitVec.ofNat 64 n := by
        intro eq
        rw [eq, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2^64)] at outside
        omega
      exact (cells_write8_outside _ _ _ _ ne).trans (h.frame p (by omega))

/-- Copy the tail bytes through their exact fetched loop. A zero-length tail
takes the exit branch before any data access. -/
theorem tail_copied (base : Addr) (s : CPU) (rem : Nat) (rb : rem < 64)
    (pc : s.pc = base + 0x52) (idx : s.reg 30 = 0) (len : s.reg 7 = BitVec.ofNat 64 rem)
    (apart : ∀ t : Fin rem, 128 ≤ (s.reg 28 + BitVec.ofNat 64 t.val - s.reg 29).toNat) :
    ∃ out, ImageExecution base s (tailCode rem) out ∧ out.pc = base + 0x6a ∧
      (∀ j, j < rem → out.mem.read8 (s.reg 29 + BitVec.ofNat 64 j) =
        s.mem.read8 (s.reg 28 + BitVec.ofNat 64 j)) ∧
      (∀ p, rem ≤ (p - s.reg 29).toNat → out.mem.cells p = s.mem.cells p) := by
  obtain ⟨mid, path, h⟩ := copy_prefix base s rem rb pc idx len apart rem (by omega)
  let out := tailGuard.step mid
  have one : ImageExecution base mid [tailGuard] out :=
    .cons (by rw [offset_eq h.pc (by decide)]; exact tailGuard_decoded) (by simp) (.nil _)
  have go := tail_taken mid rem rem rb rb h.index h.limit
  have result : out = { mid with pc := base + 0x6a } := by
    simp [out, tailGuard, Instruction.step, go, h.pc, BitVec.add_assoc]
  refine ⟨out, path.append one (tail_no_return rem), ?_⟩
  rw [result]
  exact ⟨rfl, h.copied, h.frame⟩

theorem tail_keeps (n : Nat) (r : Reg)
    (cycle : tailCycle.all (fun i => i.op.destination != some r) = true) :
    (tailCode n).all (fun i => i.op.destination != some r) = true := by
  have guard : tailGuard.op.destination != some r := by simp [tailGuard, Op.destination]
  induction n with
  | zero => simp [tailCode, tailPrefix, guard]
  | succ n ih =>
    simp only [tailCode, List.all_append, List.all_cons, List.all_nil, Bool.and_true, guard] at ih ⊢
    simp only [tailPrefix, List.all_append, cycle, Bool.and_true, ih]

end Crypto.RISCV64
