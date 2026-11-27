import Proofs.HMACSHA256.X86Ranges
import Proofs.HMACSHA256.X86Pad

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (DataAccess)

set_option maxRecDepth 8192
set_option maxHeartbeats 3800000
set_option linter.unusedSimpArgs false

def padWordEvents (outer : Bool) (pc src dst : Val) (n : Nat) : List Event :=
  let len := loadBytes outer n
  let srcDisp := BitVec.ofNat 64 (8 * n)
  let dstDisp := BitVec.ofNat 64 (destOffset outer + 8 * n)
  List.zipWith (fun (ip, data) instruction => (ip, instruction, data))
    [(pc, [⟨false, src + srcDisp, 8⟩]), (pc + BitVec.ofNat 64 len, []),
     (pc + BitVec.ofNat 64 len + 3#64, [⟨true, dst + dstDisp, 8⟩])]
    (padWord outer n)

def x86PadEvents (outer : Bool) (pc src dst : Val) : Nat → List Event
  | 0 => []
  | n + 1 => x86PadEvents outer pc src dst n ++
      padWordEvents outer (pc + BitVec.ofNat 64 (padBytes outer n)) src dst n

private theorem pad_word_facts (outer : Bool) (n : Nat) (s : Cpu)
    (live : s.ms = none) (direction : s.flags.df = false) :
    ((rangeStates (padWord outer n) s).map Cpu.rip = rangeAddresses s.rip (padWord outer n)) ∧
    (∀ t ∈ rangeStates (padWord outer n) s, t.ms = none ∧ t.flags.df = false) ∧
    rangeEvents (padWord outer n) s =
      padWordEvents outer s.rip (s.regs.get (sourceReg outer)) (s.regs.get (destReg outer)) n := by
  cases outer <;>
    simp (config := {decide := true}) [padWord, padWordEvents, rangeStates, rangeEvents, rangeAddresses,
      localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, load_word, xor_word,
      Cpu.undefBit, Regs.get_set_ne, Flags.logic, Flags.fromResult, live, direction,
      loadBytes, sourceReg, destReg, destOffset, Size.bytes, show (0 : Val) = 0#64 from rfl]

private theorem pad_code_bytes (outer : Bool) (n : Nat) :
    ((padCode outer n).map Instr.len).sum = padBytes outer n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [padCode, padBytes, List.map_append, List.sum_append, ih]
    unfold padWord
    simp

theorem pad_code_facts (outer : Bool) (n : Nat) (s : Cpu)
    (live : s.ms = none) (direction : s.flags.df = false) (count : n ≤ 8)
    (apart : ∀ i : Fin 64, 64 ≤
      (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val - padDestination s outer).toNat) :
    ((rangeStates (padCode outer n) s).map Cpu.rip = rangeAddresses s.rip (padCode outer n)) ∧
    (∀ t ∈ rangeStates (padCode outer n) s, t.ms = none ∧ t.flags.df = false) ∧
    rangeEvents (padCode outer n) s =
      x86PadEvents outer s.rip (s.regs.get (sourceReg outer)) (s.regs.get (destReg outer)) n := by
  induction n with
  | zero => exact ⟨rfl, by simp [padCode, rangeStates], rfl⟩
  | succ n ih =>
    let mid := X86.run (padCode outer n) s
    obtain ⟨frontPC, frontLive, frontEvents⟩ := ih (by omega)
    have prev := pad_run_prefix s outer n live (by omega) apart
    obtain ⟨backPC, backLive, backEvents⟩ :=
      pad_word_facts outer n mid prev.live (prev.direction.trans direction)
    have src : mid.regs.get (sourceReg outer) = s.regs.get (sourceReg outer) :=
      prev.regs _ (by cases outer <;> decide)
    have dst : mid.regs.get (destReg outer) = s.regs.get (destReg outer) :=
      prev.regs _ (by cases outer <;> decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [padCode, rangeStates_append, rangeAddresses_append, List.map_append, frontPC,
        backPC, pad_code_bytes, prev.pc]
    · intro t seen
      rw [padCode, rangeStates_append] at seen
      rcases List.mem_append.mp seen with before | after
      · exact frontLive t before
      · exact backLive t after
    · rw [padCode, rangeEvents_append, frontEvents, backEvents, prev.pc, src, dst]
      rfl

private theorem pad_word_known (outer : Bool) (n : Nat) :
    ∀ i ∈ padWord outer n, LocalInstruction i ∧ 0 < i.len := by
  intro i seen
  unfold padWord at seen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at seen
  rcases seen with rfl | rfl | rfl
  · refine ⟨.scalar ⟨.mov _ _ _, rfl⟩, ?_⟩
    change 0 < loadBytes outer n
    cases outer <;> simp [loadBytes]
  · exact ⟨.scalar ⟨.bin _ _ _ _, rfl⟩, by change 0 < 3; decide⟩
  · exact ⟨.scalar ⟨.mov _ _ _, rfl⟩, by change 0 < 5; decide⟩

private theorem pad_code_known (outer : Bool) (n : Nat) :
    ∀ i ∈ padCode outer n, LocalInstruction i ∧ 0 < i.len := by
  induction n with
  | zero => simp [padCode]
  | succ n ih =>
    intro i seen
    rcases List.mem_append.mp seen with good | good
    · exact ih i good
    · exact pad_word_known outer n i good

private theorem pad_rights (outer : Bool) (n : Nat) (pc src dst : Val) (authority : Authority)
    (read : ∀ j < 8 * n, canonical (src + BitVec.ofNat 64 j) = true ∧ authority.readable (src + BitVec.ofNat 64 j))
    (write : ∀ j < 8 * n, canonical (dst + BitVec.ofNat 64 (destOffset outer + j)) = true ∧
      authority.writable (dst + BitVec.ofNat 64 (destOffset outer + j))) :
    ∀ e ∈ x86PadEvents outer pc src dst n, ∀ a ∈ e.2.2, ∀ p, DataByte a p →
      canonical p = true ∧ if a.write then authority.writable p else authority.readable p := by
  induction n with
  | zero => simp [x86PadEvents]
  | succ n ih =>
    intro e event a observed p hit
    rcases List.mem_append.mp event with more | last
    · exact ih (fun j h => read j (by omega)) (fun j h => write j (by omega)) e more a observed p hit
    · simp only [padWordEvents, padWord, List.zipWith, List.mem_cons,
        List.not_mem_nil, or_false] at last
      rcases last with h | h | h <;> rw [h] at observed
      · obtain rfl : a = ⟨false, src + BitVec.ofNat 64 (8 * n), 8⟩ := List.mem_singleton.mp observed
        obtain ⟨k, hk, rfl⟩ := hit
        change k < 8 at hk
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact read _ (by omega)
      · exact False.elim (List.not_mem_nil observed)
      · obtain rfl : a = ⟨true, dst + BitVec.ofNat 64 (destOffset outer + 8 * n), 8⟩ :=
          List.mem_singleton.mp observed
        obtain ⟨k, hk, rfl⟩ := hit
        change k < 8 at hk
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
        exact write _ (by omega)

theorem pad_range_ready (outer : Bool) (base : Val) (s : Cpu) (authority : Authority)
    (live : s.ms = none) (direction : s.flags.df = false)
    (apart : ∀ i : Fin 64, 64 ≤
      (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val - padDestination s outer).toNat)
    (pc : s.rip = routineAddress base (if outer then finish else entry) +
      BitVec.ofNat 64 (if outer then 0x45 else 0x72))
    (text : ∀ j < (if outer then finish else entry).image.size,
      canonical (routineAddress base (if outer then finish else entry) + BitVec.ofNat 64 j) = true ∧
      authority.executable (routineAddress base (if outer then finish else entry) + BitVec.ofNat 64 j))
    (read : ∀ j < 64, canonical (s.regs.get (sourceReg outer) + BitVec.ofNat 64 j) = true ∧
      authority.readable (s.regs.get (sourceReg outer) + BitVec.ofNat 64 j))
    (write : ∀ j < 64, canonical (padDestination s outer + BitVec.ofNat 64 j) = true ∧
      authority.writable (padDestination s outer + BitVec.ofNat 64 j)) :
    RangeReady (if outer then finish else entry) base authority (if outer then 0x45 else 0x72) s (padCode outer 8) := by
  obtain ⟨pcs, productive, obs⟩ := pad_code_facts outer 8 s live direction (by decide) apart
  refine range_ready_of_events (by cases outer; exact entry_pad_decoded; exact finish_pad_decoded)
    (by cases outer <;> decide +kernel) (by cases outer <;> decide +kernel)
    (pad_code_known outer 8) text (pc ▸ pcs) productive ?_
  rw [obs]
  apply pad_rights _ _ _ _ _ _ read
  intro j hj
  simpa only [padDestination, BitVec.ofNat_add, BitVec.add_assoc] using write j hj

end Crypto.HMACSHA256.X86_64
