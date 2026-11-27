import Proofs.HMACSHA256.X86CallSites
import Proofs.HMACSHA256.LinkedExecution
import Proofs.HMACSHA256.X86ShaEntry

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.ARM64.Imported (DataAccess)
open Crypto.Baseline (Authority)

inductive LocalInstruction (i : Instr) : Prop where
  | scalar (form : ScalarLeaf i)
  | call (disp : Val) (form : i = ⟨.call (.rel disp), 5⟩)
  | copy (form : i = copyByte)
  | clear (form : i = storeWord)

def localAccesses (s : Cpu) (i : Instr) : Option (List DataAccess) :=
  match i.op with
  | .call (.rel _) => some [⟨true, s.regs.get .rsp - 8#64, 8⟩]
  | .repstrop .rep .movs .b => some (if s.regs.get .rcx = 0#64 then [] else
      [⟨false, s.regs.get .rsi, 1⟩, ⟨true, s.regs.get .rdi, 1⟩])
  | .repstrop .rep .stos .q => some (if s.regs.get .rcx = 0#64 then [] else
      [⟨true, s.regs.get .rdi, 8⟩])
  | _ => dataAccesses i s

theorem scalar_accesses {s : Cpu} {i : Instr} (scalar : ScalarLeaf i) :
    localAccesses s i = dataAccesses i s := by
  rcases i with ⟨op, len⟩
  obtain ⟨form, shape⟩ := scalar
  change op = form.op at shape
  subst op
  cases form <;> rfl

def PermittedAccesses (authority : Authority) (s : Cpu) (i : Instr) (accesses : List DataAccess) : Prop :=
  (∀ p, DataByte ⟨false, s.rip, i.len⟩ p → canonical p = true ∧ authority.executable p) ∧
  (∀ a ∈ accesses, ∀ p, DataByte a p → canonical p = true ∧
    if a.write then authority.writable p else authority.readable p)

@[simp] theorem localAccesses_overlay (s : Cpu) (m : Mem) (i : Instr) :
    localAccesses {s with mem := m} i = localAccesses s i := by
  rcases i with ⟨op, len⟩
  cases op
  case call target => cases target <;> rfl
  case repstrop rep kind width => cases rep <;> cases kind <;> cases width <;> rfl
  all_goals rfl

/-- A HMAC-local instruction is fetched from the recorded bytes. Its
observation includes the stack write of CALL and the individual accesses
of each modeled repeat step. -/
inductive ProgramStep (base : Val) (authority : Authority) : Cpu → Event → Cpu → Prop where
  | localStep {r : Routine} {s : Cpu} {i : Instr} {accesses : List DataAccess}
      (body : r = entry ∨ r = key ∨ r = finish)
      (fetched : r.fetch (decodeAt r) Instr.len (routineAddress base r) s.rip s.mem.read = some i)
      (known : LocalInstruction i) (live : s.ms = none) (direction : s.flags.df = false)
      (data : localAccesses s i = some accesses)
      (allowed : PermittedAccesses authority s i accesses) :
      ProgramStep base authority s (s.rip, i, accesses) (step i s)

/-- A linked HMAC execution uses the existing checked SHA-256 executions at
the actual call targets. Ordinary instructions are checked byte by byte
against the surrounding HMAC image with the same authority. -/
inductive LinkedExecution (base : Val) (authority : Authority) : Cpu → List Event → Cpu → Prop where
  | nil (s : Cpu) : LinkedExecution base authority s [] s
  | localStep {s next out : Cpu} {event : Event} {tail : List Event}
      (head : ProgramStep base authority s event next)
      (rest : LinkedExecution base authority next tail out) :
      LinkedExecution base authority s (event :: tail) out
  | shaCall {s next out : Cpu} {msg : Crypto.Reference.ByteList} {extent : Nat} {events tail : List Event}
      (callee : NativeSerial (shaAddress base) s next msg extent authority events)
      (rest : LinkedExecution base authority next tail out) :
      LinkedExecution base authority s (events ++ tail) out

theorem LinkedExecution.append {base : Val} {authority : Authority} {s mid out : Cpu}
    {x y : List Event} (front : LinkedExecution base authority s x mid)
    (tail : LinkedExecution base authority mid y out) : LinkedExecution base authority s (x ++ y) out := by
  induction front with
  | nil => exact tail
  | localStep head _ ih => exact .localStep head (ih tail)
  | shaCall callee _ ih => rw [List.append_assoc]; exact .shaCall callee (ih tail)

theorem hmac_step_fetched (base : Val) (authority : Authority) (r : Routine) (off : Nat) (s : Cpu)
    (i : Instr) (accesses : List DataAccess) (body : r = entry ∨ r = key ∨ r = finish)
    (loaded : r.Loaded (routineAddress base r) s.mem.read)
    (pc : s.rip = routineAddress base r + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt r off = some i) (positive : 0 < i.len) (within : off + i.len ≤ r.image.size)
    (localForm : LocalInstruction i) (live : s.ms = none) (direction : s.flags.df = false)
    (data : localAccesses s i = some accesses) (allowed : PermittedAccesses authority s i accesses) :
    ProgramStep base authority s (s.rip, i, accesses) (step i s) :=
  .localStep body (r.fetch_at _ _ _ _ _ _ _ loaded pc addressable decoded positive within)
    localForm live direction data allowed

private theorem copy_effect (s : Cpu) (other : Mem) (accesses : List DataAccess)
    (live : s.ms = none) (direction : s.flags.df = false)
    (data : localAccesses s copyByte = some accesses) (reads : ReadsAgree accesses s.mem other) :
    ∃ effect : MemoryEffect, (∀ p, effect.touches p → ObservedByte accesses true p) ∧
      (step copyByte s).mem = effect.apply s.mem ∧
      step copyByte {s with mem := other} = {(step copyByte s) with mem := effect.apply other} := by
  by_cases empty : s.regs.get .rcx = 0#64
  · rw [copyByte_empty s live empty, copyByte_empty {s with mem := other} live empty]
    exact ⟨.none, fun _ h => h.elim, rfl, rfl⟩
  have memory : other.read (s.regs.get .rsi) = s.mem.read (s.regs.get .rsi) := by
    apply reads
    simp only [localAccesses, copyByte, storeWord, if_neg empty, Option.some.injEq] at data
    subst accesses
    exact ⟨⟨false, s.regs.get .rsi, 1⟩, by simp, rfl, 0, by change 0 < 1; decide, by simp⟩
  rw [copyByte_step s live direction empty, copyByte_step {s with mem := other} live direction empty]
  let effect := MemoryEffect.write .b (s.regs.get .rdi) ((s.mem.read (s.regs.get .rsi)).setWidth 64)
  have write (m : Mem) : effect.apply m = m.write (s.regs.get .rdi) (s.mem.read (s.regs.get .rsi)) := by
    simp [effect, MemoryEffect.apply, Mem.writeSize, Mem.writeN, Size.bytes, BitVec.setWidth_setWidth_of_le]
  refine ⟨effect, ?_, (write _).symm, ?_⟩
  · intro p hit
    simp only [localAccesses, copyByte, storeWord, if_neg empty, Option.some.injEq] at data
    subst accesses
    exact ⟨⟨true, s.regs.get .rdi, 1⟩, by simp, rfl, hit⟩
  · simp only [write, memory]

private theorem clear_effect (s : Cpu) (other : Mem) (accesses : List DataAccess)
    (live : s.ms = none) (direction : s.flags.df = false)
    (data : localAccesses s storeWord = some accesses) :
    ∃ effect : MemoryEffect, (∀ p, effect.touches p → ObservedByte accesses true p) ∧
      (step storeWord s).mem = effect.apply s.mem ∧
      step storeWord {s with mem := other} = {(step storeWord s) with mem := effect.apply other} := by
  by_cases empty : s.regs.get .rcx = 0#64
  · rw [storeWord_empty s live empty, storeWord_empty {s with mem := other} live empty]
    exact ⟨.none, fun _ h => h.elim, rfl, rfl⟩
  rw [storeWord_step s live direction empty, storeWord_step {s with mem := other} live direction empty]
  refine ⟨.write .q (s.regs.get .rdi) (s.regs.get .rax), ?_, rfl, rfl⟩
  intro p hit
  simp only [localAccesses, copyByte, storeWord, if_neg empty, Option.some.injEq] at data
  subst accesses
  exact ⟨⟨true, s.regs.get .rdi, 8⟩, by simp, rfl, hit⟩

private theorem call_effect (s : Cpu) (other : Mem) (accesses : List DataAccess)
    (disp : Val) (live : s.ms = none) (data : localAccesses s ⟨.call (.rel disp), 5⟩ = some accesses) :
    ∃ effect : MemoryEffect, (∀ p, effect.touches p → ObservedByte accesses true p) ∧
      (step ⟨.call (.rel disp), 5⟩ s).mem = effect.apply s.mem ∧
      step ⟨.call (.rel disp), 5⟩ {s with mem := other} =
        {(step ⟨.call (.rel disp), 5⟩ s) with mem := effect.apply other} := by
  by_cases valid : canonical (s.rip + 5#64 + disp) = true
  · rw [direct_call s disp live valid, direct_call {s with mem := other} disp live valid]
    refine ⟨.write .q (s.regs.get .rsp - 8#64) (s.rip + 5#64), ?_, rfl, rfl⟩
    intro p hit
    change some [⟨true, s.regs.get .rsp - 8#64, 8⟩] = some accesses at data
    injection data with eq
    subst accesses
    exact ⟨⟨true, s.regs.get .rsp - 8#64, 8⟩, by simp, rfl, hit⟩
  · refine ⟨.none, fun _ h => h.elim, ?_, ?_⟩ <;>
      simp [X86.step, Cpu.stopped, live, Cpu.halt, valid, MemoryEffect.apply]

theorem local_memory_effect (i : Instr) (s : Cpu) (other : Mem) (accesses : List DataAccess)
    (form : LocalInstruction i) (live : s.ms = none) (direction : s.flags.df = false)
    (data : localAccesses s i = some accesses) (reads : ReadsAgree accesses s.mem other) :
    ∃ effect : MemoryEffect, (∀ p, effect.touches p → ObservedByte accesses true p) ∧
      (step i s).mem = effect.apply s.mem ∧
      step i {s with mem := other} = {(step i s) with mem := effect.apply other} := by
  cases form with
  | scalar known => exact scalar_memory_effect i s other accesses known (scalar_accesses known ▸ data) reads
  | call disp equation => subst i; exact call_effect s other accesses disp live data
  | copy equation => subst i; exact copy_effect s other accesses live direction data reads
  | clear equation => subst i; exact clear_effect s other accesses live direction data

theorem ProgramStep.frame {base : Val} {authority : Authority} {s out : Cpu} {event : Event}
    (run : ProgramStep base authority s event out) (p : Val)
    (outside : ¬ ObservedByte event.2.2 true p) : out.mem.read p = s.mem.read p := by
  cases run with
  | localStep _ _ form live direction data _ =>
    obtain ⟨effect, touches, written, _⟩ := local_memory_effect _ s s.mem _ form live direction data (fun _ _ => rfl)
    rw [written]
    exact effect.frame _ _ (fun h => outside (touches p h))

end Crypto.HMACSHA256.X86_64
