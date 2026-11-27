import Proofs.HMACSHA256.X86Program

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.ARM64.Imported (DataAccess)
open Crypto.Baseline (Authority Region)

theorem ProgramStep.keeps_routine {base : Val} {authority : Authority} {start out : Cpu}
    {event : Event} (run : ProgramStep base authority start event out) (r : Routine)
    (code : r.Loaded (routineAddress base r) start.mem.read)
    (readOnlyCode : ∀ i < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 i)) :
    r.Loaded (routineAddress base r) out.mem.read := by
  intro i hi
  have allowed : ∀ a ∈ event.2.2, ∀ p, DataByte a p → a.write = true → authority.writable p := by
    cases run with
    | localStep _ _ _ _ _ _ rights =>
      intro a present p touched writes
      simpa only [writes, if_true] using (rights.2 a present p touched).2
  rw [run.frame _ (fun ⟨a, present, writes, touched⟩ => readOnlyCode _ hi (allowed a present _ touched writes))]
  exact code i hi

private theorem sha_preserves_unwritten {base : Val} {s out : Cpu} {events : List Event}
    (run : ObservedExecution base s events out) (p : Val)
    (outside : ∀ e ∈ events, ¬ ObservedByte e.2.2 true p) : out.mem.read p = s.mem.read p := by
  induction run with
  | nil => rfl
  | @cons s next out i accesses tail fetched ran observed _ ih =>
    have live : s.stopped = false := by
      cases h : s.stopped
      · rfl
      · simp [Crypto.X86_64.stepLoaded, h, guard] at ran
    have same : X86.step i s = next := by
      simpa [Crypto.X86_64.stepLoaded, live, guard, fetched] using ran
    obtain ⟨patch, touched, memory, _⟩ := scalar_memory_effect i s s.mem accesses
      (fetched_scalar fetched) observed (fun _ _ => rfl)
    rw [same] at memory
    exact (ih (fun e present => outside e (List.mem_cons_of_mem _ present))).trans (by
      rw [memory]
      exact patch.frame _ p (fun hit => outside _ List.mem_cons_self (touched p hit)))

theorem LinkedExecution.keeps_routine {base : Val} {authority : Authority} {s out : Cpu}
    {events : List Event} (run : LinkedExecution base authority s events out) (r : Routine)
    (code : r.Loaded (routineAddress base r) s.mem.read)
    (readOnlyCode : ∀ i < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 i)) :
    r.Loaded (routineAddress base r) out.mem.read := by
  induction run with
  | nil => exact code
  | localStep head _ ih => exact ih (head.keeps_routine r code readOnlyCode)
  | shaCall callee _ ih =>
    apply ih
    intro i hi
    have preserve := sha_preserves_unwritten callee.execution (routineAddress base r + BitVec.ofNat 64 i)
      (fun e present ⟨a, member, writes, touched⟩ =>
        readOnlyCode i hi (by simpa only [writes, if_true] using (callee.data e present a member _ touched).2))
    rw [preserve]
    exact code i hi

theorem decode_range_cons {r : Routine} {off n : Nat} {i : Instr} {tail : List Instr}
    (decoded : decodeRange r off (n + 1) = some (i :: tail)) :
    decodeAt r off = some i ∧ decodeRange r (off + i.len) n = some tail := by
  cases actual : decodeAt r off with
  | none => simp [decodeRange, actual] at decoded
  | some head =>
    cases following : decodeRange r (off + head.len) n with
    | none => simp [decodeRange, actual, following] at decoded
    | some rest =>
      have equal : head = i ∧ rest = tail := by simpa [decodeRange, actual, following] using decoded
      obtain ⟨rfl, rfl⟩ := equal
      exact ⟨rfl, following⟩

theorem fetch_rights {r : Routine} {base : Val} {authority : Authority} {off len : Nat}
    (right : ∀ i < r.image.size, canonical (routineAddress base r + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r + BitVec.ofNat 64 i))
    (within : off + len ≤ r.image.size)
    (p : Val) (seen : DataByte ⟨false, routineAddress base r + BitVec.ofNat 64 off, len⟩ p) :
    canonical p = true ∧ authority.executable p := by
  obtain ⟨i, hi, rfl⟩ := seen
  change i < len at hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact right _ (by omega)

/-- All rejected addresses are explicit. The proof of a range supplies its
actual sequential fetch positions and the permissions for the actual data
operands in each intermediate state. -/
def RangeReady (r : Routine) (base : Val) (authority : Authority) (off : Nat) (s : Cpu) : List Instr → Prop
  | [] => True
  | i :: tail =>
    s.rip = routineAddress base r + BitVec.ofNat 64 off ∧ off < 2 ^ 64 ∧
    decodeAt r off = some i ∧ 0 < i.len ∧ off + i.len ≤ r.image.size ∧
    LocalInstruction i ∧ s.ms = none ∧ s.flags.df = false ∧
    (∃ accesses, localAccesses s i = some accesses ∧ PermittedAccesses authority s i accesses) ∧
    RangeReady r base authority (off + i.len) (step i s) tail

def rangeEvents : List Instr → Cpu → List Event
  | [], _ => []
  | i :: tail, s => (s.rip, i, (localAccesses s i).getD []) :: rangeEvents tail (step i s)

/-- Expected instruction states in a decoded range. The final instruction may
transfer control. The address, machine status and direction flag at every
instruction that actually executes remain explicit. -/
def rangeStates : List Instr → Cpu → List Cpu
  | [], _ => []
  | i :: tail, s => s :: rangeStates tail (step i s)

def rangeAddresses (pc : Val) : List Instr → List Val
  | [] => []
  | i :: tail => pc :: rangeAddresses (pc + BitVec.ofNat 64 i.len) tail

/-- The expected observations of a decoded block with statically placed
instructions and explicitly specified data accesses. Theorem proofs must
identify this list with the events generated by the decoded steps. -/
def staticEvents (pc : Val) (code : List Instr) (accesses : List (List DataAccess)) : List Event :=
  List.zip (rangeAddresses pc code) (List.zip code accesses)

theorem rangeEvents_append (front rest : List Instr) (s : Cpu) :
    rangeEvents (front ++ rest) s = rangeEvents front s ++ rangeEvents rest (X86.run front s) := by
  induction front generalizing s with
  | nil => rfl
  | cons i tail ih =>
    change _ :: rangeEvents (tail ++ rest) (step i s) = _
    rw [ih]
    rfl

theorem rangeStates_append (front rest : List Instr) (s : Cpu) :
    rangeStates (front ++ rest) s = rangeStates front s ++ rangeStates rest (X86.run front s) := by
  induction front generalizing s with
  | nil => rfl
  | cons i tail ih =>
    change _ :: rangeStates (tail ++ rest) (step i s) = _
    rw [ih]
    rfl

theorem rangeAddresses_append (front rest : List Instr) (pc : Val) :
    rangeAddresses pc (front ++ rest) =
      rangeAddresses pc front ++ rangeAddresses (pc + BitVec.ofNat 64 (front.map Instr.len).sum) rest := by
  induction front generalizing pc with
  | nil => simp [rangeAddresses]
  | cons i tail ih =>
    simp only [List.cons_append, rangeAddresses, ih, List.map_cons, List.sum_cons, BitVec.ofNat_add,
      BitVec.add_assoc]

theorem local_accesses_defined {i : Instr} (known : LocalInstruction i) (s : Cpu) :
    ∃ accesses, localAccesses s i = some accesses := by
  cases known with
  | scalar form =>
    rw [scalar_accesses form]
    exact scalar_accesses_defined i s form
  | call d eq => subst i; exact ⟨_, rfl⟩
  | copy eq => subst i; exact ⟨_, rfl⟩
  | clear eq => subst i; exact ⟨_, rfl⟩

theorem range_ready_of_events {r : Routine} {base : Val} {authority : Authority} {off : Nat}
    {s : Cpu} {ops : List Instr}
    (decoded : decodeRange r off ops.length = some ops)
    (addressable : r.image.size < 2 ^ 64) (fits : off + (ops.map Instr.len).sum ≤ r.image.size)
    (known : ∀ i ∈ ops, LocalInstruction i ∧ 0 < i.len)
    (code : ∀ i < r.image.size, canonical (routineAddress base r + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r + BitVec.ofNat 64 i))
    (pcs : (rangeStates ops s).map Cpu.rip = rangeAddresses (routineAddress base r + BitVec.ofNat 64 off) ops)
    (ready : ∀ t ∈ rangeStates ops s, t.ms = none ∧ t.flags.df = false)
    (data : ∀ event ∈ rangeEvents ops s, ∀ a ∈ event.2.2, ∀ p, DataByte a p →
      canonical p = true ∧ if a.write then authority.writable p else authority.readable p) :
    RangeReady r base authority off s ops := by
  induction ops generalizing s off with
  | nil => trivial
  | cons i tail ih =>
    have count : (i :: tail).length = tail.length + 1 := rfl
    rw [count] at decoded
    obtain ⟨head, suffix⟩ := decode_range_cons decoded
    have width := (known i List.mem_cons_self).2
    have form := (known i List.mem_cons_self).1
    have running := ready s List.mem_cons_self
    change s.rip :: _ = (routineAddress base r + BitVec.ofNat 64 off) :: _ at pcs
    obtain ⟨pc, next⟩ := List.cons.inj pcs
    have each : off + i.len ≤ r.image.size := by simp only [List.map_cons, List.sum_cons] at fits; omega
    obtain ⟨accesses, observe⟩ := local_accesses_defined form s
    refine ⟨pc, by omega, head, width, each, form, running.1, running.2, ⟨accesses, observe, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [pc]
        exact fetch_rights code each
      · intro a ha p whereAt
        apply data (s.rip, i, accesses) _ a ha p whereAt
        simp only [rangeEvents, observe, Option.getD_some, List.mem_cons, true_or]
    · apply ih suffix (by simp only [List.map_cons, List.sum_cons] at fits; omega)
        (fun j hj => known j (List.mem_cons_of_mem _ hj))
      · simpa only [BitVec.ofNat_add, BitVec.add_assoc] using next
      · intro t ht
        exact ready t (List.mem_cons_of_mem _ ht)
      · intro event occurred a has p whereAt
        exact data event (List.mem_cons_of_mem _ occurred) a has p whereAt

theorem ready_range_executes (r : Routine) (base : Val) (authority : Authority) (off : Nat) (s : Cpu)
    (ops : List Instr) (body : r = entry ∨ r = key ∨ r = finish)
    (code : r.Loaded (routineAddress base r) s.mem.read)
    (readOnlyCode : ∀ i < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 i))
    (ready : RangeReady r base authority off s ops) :
    LinkedExecution base authority s (rangeEvents ops s) (X86.run ops s) := by
  induction ops generalizing off s with
  | nil => exact .nil s
  | cons i tail ih =>
    obtain ⟨pc, addressable, decoded, positive, within, form, live, direction, ⟨accesses, obs, rights⟩, rest⟩ := ready
    have localStep := hmac_step_fetched base authority r off s i accesses body code pc addressable
      decoded positive within form live direction obs rights
    have following := ih (off + i.len) (step i s) (localStep.keeps_routine r code readOnlyCode) rest
    simpa only [rangeEvents, obs, Option.getD_some] using LinkedExecution.localStep localStep following

theorem run_range_observes {r : Routine} {base : Val} {authority : Authority} {off count : Nat}
    {s out : Cpu} {ops : List Instr} (body : r = entry ∨ r = key ∨ r = finish)
    (code : r.Loaded (routineAddress base r) s.mem.read)
    (readOnlyCode : ∀ i < r.image.size, ¬ authority.writable (routineAddress base r + BitVec.ofNat 64 i))
    (decoded : decodeRange r off count = some ops) (run : runRange r off count s = some out)
    (ready : RangeReady r base authority off s ops) :
    LinkedExecution base authority s (rangeEvents ops s) out := by
  have steps : X86.run ops s = out := by simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using run
  rw [← steps]
  exact ready_range_executes r base authority off s ops body code readOnlyCode ready

end Crypto.HMACSHA256.X86_64
