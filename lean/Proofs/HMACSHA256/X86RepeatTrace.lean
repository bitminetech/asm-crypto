import Proofs.HMACSHA256.X86Ranges
import Proofs.HMACSHA256.X86Zero

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (DataAccess)

private theorem rep_rights {authority : Authority} {s : Cpu} {i : Instr}
    {accesses : List DataAccess}
    (fetch : ∀ p, DataByte ⟨false, s.rip, i.len⟩ p → canonical p = true ∧ authority.executable p)
    (touches : ∀ a ∈ accesses, ∀ p, DataByte a p → canonical p = true ∧
      if a.write then authority.writable p else authority.readable p) :
    PermittedAccesses authority s i accesses := ⟨fetch, touches⟩

private theorem repeat_fetched {base : Val} {authority : Authority} {r : Routine} {off count : Nat}
    {start : Cpu} {i : Instr} (states : Nat → Cpu) (data : Nat → List DataAccess)
    (starts : states 0 = start)
    (advances : ∀ j ≤ count, states (j + 1) = step i (states j))
    (observe : ∀ j ≤ count, localAccesses (states j) i = some (data j))
    (publicPC : ∀ j ≤ count, (states j).rip = start.rip)
    (live : ∀ j ≤ count, (states j).ms = none)
    (direction : ∀ j ≤ count, (states j).flags.df = false)
    (runAt : start.rip = routineAddress base r + BitVec.ofNat 64 off)
    (body : r = entry ∨ r = key ∨ r = finish) (known : LocalInstruction i)
    (bounds : off < 2 ^ 64 ∧ 0 < i.len ∧ off + i.len ≤ r.image.size)
    (decoded : decodeAt r off = some i) (loaded : r.Loaded (routineAddress base r) start.mem.read)
    (readonly : ∀ j < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 j))
    (exec : ∀ p, DataByte ⟨false, start.rip, i.len⟩ p → canonical p = true ∧ authority.executable p)
    (rights : ∀ j ≤ count, ∀ a ∈ data j, ∀ p, DataByte a p → canonical p = true ∧
      if a.write then authority.writable p else authority.readable p) :
    LinkedExecution base authority start
      ((List.range (count + 1)).map (fun j => (start.rip, i, data j))) (states (count + 1)) := by
  suffices ∀ n ≤ count + 1, LinkedExecution base authority start
      ((List.range n).map (fun j => (start.rip, i, data j))) (states n) from this _ (Nat.le_refl _)
  intro n bounded
  induction n with
  | zero =>
    simpa only [starts, List.range_zero, List.map_nil] using
      (LinkedExecution.nil (base := base) (authority := authority) start)
  | succ j ih =>
    have jBound : j ≤ count := by omega
    have earlier := ih (by omega)
    have atPC := publicPC j jBound
    have permissions : PermittedAccesses authority (states j) i (data j) := by
      apply rep_rights
      · rw [atPC]; exact exec
      · exact rights j jBound
    have run := hmac_step_fetched base authority r off (states j) i (data j) body
      (earlier.keeps_routine r loaded readonly) (atPC.trans runAt) bounds.1 decoded bounds.2.1 bounds.2.2
      known (live j jBound) (direction j jBound) (observe j jBound) permissions
    rw [atPC, ← advances j jBound] at run
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact earlier.append (.localStep run (.nil _))

def copyData (src dst : Val) (count j : Nat) : List DataAccess :=
  if j < count then
    [⟨false, src + BitVec.ofNat 64 j, 1⟩, ⟨true, dst + BitVec.ofNat 64 j, 1⟩]
  else []

def copyEvents (pc src dst : Val) (count : Nat) : List Event :=
  (List.range (count + 1)).map fun j => (pc, copyByte, copyData src dst count j)

private theorem counter_eq_zero {v : Val} {count j : Nat}
    (remaining : v = BitVec.ofNat 64 (count - j)) (bound : count < 2 ^ 64) (jBound : j ≤ count) :
    v = 0#64 ↔ ¬ j < count := by
  rw [remaining]
  constructor
  · intro eq
    have num := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : count - j < 2 ^ 64)] at num
    change count - j = 0 at num
    omega
  · intro done
    rw [show count - j = 0 by omega]

private theorem data_byte_single {write : Bool} {addr p : Val} (seen : DataByte ⟨write, addr, 1⟩ p) :
    p = addr := by
  obtain ⟨i, hi, rfl⟩ := seen
  change i < 1 at hi
  have : i = 0 := by omega
  subst i
  simp

theorem copy_fetched_observes {base : Val} {authority : Authority} {r : Routine} {off count : Nat}
    (s : Cpu) (body : r = entry ∨ r = key ∨ r = finish)
    (decoded : decodeAt r off = some copyByte)
    (bounds : off < 2 ^ 64 ∧ off + 2 ≤ r.image.size)
    (pc : s.rip = routineAddress base r + BitVec.ofNat 64 off)
    (loaded : r.Loaded (routineAddress base r) s.mem.read)
    (text : ∀ i < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 i))
    (fetch : ∀ p, DataByte ⟨false, s.rip, 2⟩ p → canonical p = true ∧ authority.executable p)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = BitVec.ofNat 64 count) (bound : count < 2 ^ 64)
    (separated : ∀ j < count,
      count ≤ (s.regs.get .rsi + BitVec.ofNat 64 j - s.regs.get .rdi).toNat)
    (read : ∀ j < count, canonical (s.regs.get .rsi + BitVec.ofNat 64 j) = true ∧
      authority.readable (s.regs.get .rsi + BitVec.ofNat 64 j))
    (write : ∀ j < count, canonical (s.regs.get .rdi + BitVec.ofNat 64 j) = true ∧
      authority.writable (s.regs.get .rdi + BitVec.ofNat 64 j)) :
    LinkedExecution base authority s (copyEvents s.rip (s.regs.get .rsi) (s.regs.get .rdi) count)
      (copySteps s (count + 1)) := by
  have pref := copySteps_prefix s count
  have completed (j : Nat) (hj : j ≤ count) := pref j live direction length bound separated hj
  refine repeat_fetched (copySteps s) (copyData (s.regs.get .rsi) (s.regs.get .rdi) count)
    rfl (fun _ _ => rfl) ?_ (fun j hj => (completed j hj).rip) (fun j hj => (completed j hj).live)
    (fun j hj => (completed j hj).flags.symm ▸ direction) pc body (.copy rfl)
    ⟨bounds.1, by decide, bounds.2⟩ decoded loaded text fetch ?_
  · intro j hj
    have p := completed j hj
    have empty := counter_eq_zero p.remaining bound hj
    by_cases active : j < count
    · have nz : (copySteps s j).regs.get .rcx ≠ 0#64 := fun h => empty.mp h active
      simp only [localAccesses, copyByte, copyData, if_neg nz, if_pos active, p.source, p.dest]
    · have eq := empty.mpr active
      simp only [localAccesses, copyByte, copyData, if_pos eq, if_neg active]
  · intro j _ a seen p hit
    by_cases active : j < count
    · simp only [copyData, if_pos active, List.mem_cons, List.not_mem_nil, or_false] at seen
      rcases seen with h | h <;> subst a
      · rw [data_byte_single hit]; exact read j active
      · rw [data_byte_single hit]; exact write j active
    · simp [copyData, active] at seen

def clearKeyData (dst : Val) (j : Nat) : List DataAccess :=
  if j < 8 then [⟨true, dst + BitVec.ofNat 64 (8 * j), 8⟩] else []

def clearKeyEvents (pc dst : Val) : List Event :=
  (List.range 9).map fun j => (pc, storeWord, clearKeyData dst j)

theorem key_clear_fetched_observes {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x1e#64)
    (loaded : key.Loaded (routineAddress base key) s.mem.read)
    (text : ∀ i < key.image.size, ¬ authority.writable (routineAddress base key + BitVec.ofNat 64 i))
    (fetch : ∀ p, DataByte ⟨false, s.rip, 3⟩ p → canonical p = true ∧ authority.executable p)
    (live : s.ms = none) (direction : s.flags.df = false)
    (length : s.regs.get .rcx = 8#64) (zero : s.regs.get .rax = 0#64)
    (write : ∀ j < 64, canonical (s.regs.get .rdi + BitVec.ofNat 64 j) = true ∧
      authority.writable (s.regs.get .rdi + BitVec.ofNat 64 j)) :
    LinkedExecution base authority s (clearKeyEvents s.rip (s.regs.get .rdi)) (storeSteps s 9) := by
  have pref (j : Nat) (hj : j ≤ 8) := zero_prefix s j hj live direction length zero
  refine repeat_fetched (off := 0x1e) (count := 8) (storeSteps s) (clearKeyData (s.regs.get .rdi))
    rfl (fun _ _ => rfl) ?_ (fun j hj => (pref j hj).rip) (fun j hj => (pref j hj).live)
    (fun j hj => (pref j hj).flags.symm ▸ direction) pc (.inr (.inl rfl)) (.clear rfl)
    ⟨by decide, by decide, by decide⟩ repeat_decoded.2.2 loaded text fetch ?_
  · intro j hj
    have p := pref j hj
    have empty := counter_eq_zero p.count (by decide) hj
    by_cases active : j < 8
    · have nz : (storeSteps s j).regs.get .rcx ≠ 0#64 := fun h => empty.mp h active
      simp only [localAccesses, storeWord, clearKeyData, if_neg nz, if_pos active, p.dest]
    · have eq := empty.mpr active
      simp only [localAccesses, storeWord, clearKeyData, if_pos eq, if_neg active]
  · intro j _ a present p seen
    by_cases active : j < 8
    · simp only [clearKeyData, if_pos active, List.mem_singleton] at present
      subst a
      obtain ⟨i, hi, rfl⟩ := seen
      change i < 8 at hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact write _ (by omega)
    · simp [clearKeyData, active] at present

end Crypto.HMACSHA256.X86_64
