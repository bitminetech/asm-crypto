import Proofs.HMACSHA256.LinkedExecution
import Models.RISCV64SHA256Fetch
import Proofs.ARM64.ImportedZeroPad
import Proofs.ARM64.ImportedFetchMemory

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.ARM64.Imported (canRead_write8 canRead_write32 canRead_write64)

def routineAddress (base : Addr) (routine : Routine) : Addr :=
  base + BitVec.ofInt 64 routine.offset

def shaAddress (base : Addr) : Addr := base + BitVec.ofInt 64 sha256Offset

def Op.accesses (op : Op) (s : CPU) : List Access :=
  let data := match op with
    | .scalar i => i.op.accesses s
    | _ => []
  .fetch s.pc op.width :: data

/-- One observed instruction in the linked Linux program. Calls are ordinary
JAL instructions. Instruction execution subsequently fetches from the called
body, including the existing SHA-256 executable model. -/
inductive ProgramStep (base : Addr) : CPU → List Access → CPU → Prop where
  | hmac {r : Routine} {s : CPU} {op : Op}
      (body : r = entry ∨ r = key ∨ r = finish)
      (fetched : r.fetch (decodeAt r) Op.width (routineAddress base r) s.pc s.mem.read8 = some op)
      (allowed : (op.accesses s).all (Access.permitted s.mem) = true) :
      ProgramStep base s (op.accesses s) (op.step s)
  | sha {s after : CPU} {trace : List Access} {returned : Bool}
      (step : checkedStep (shaAddress base) s = some (after, trace, returned)) :
      ProgramStep base s trace after

/-- A trace records one list per instruction, so its length bounds the modeled
instruction count, even for instructions with multiple memory accesses. -/
inductive ProgramExecution (base : Addr) : CPU → List (List Access) → CPU → Prop where
  | nil (s : CPU) : ProgramExecution base s [] s
  | cons {s next after : CPU} {event : List Access} {trace : List (List Access)}
      (head : ProgramStep base s event next) (tail : ProgramExecution base next trace after) :
      ProgramExecution base s (event :: trace) after

theorem ProgramExecution.append {base : Addr} {s mid out : CPU} {before after : List (List Access)}
    (one : ProgramExecution base s before mid) (two : ProgramExecution base mid after out) :
    ProgramExecution base s (before ++ after) out := by
  induction one with
  | nil => exact two
  | cons head _ ih => exact .cons head (ih two)

theorem sha_segment {base : Addr} {s out : CPU} {fuel : Nat}
    (run : runUntilReturn (shaAddress base) s fuel = some out) :
    ∃ trace, ProgramExecution base s trace out ∧ trace.length ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [runUntilReturn] at run
  | succ n ih =>
    cases step : checkedStep (shaAddress base) s with
    | none => simp [runUntilReturn, step] at run
    | some value =>
      obtain ⟨next, trace, returned⟩ := value
      cases returned
      · have tail : runUntilReturn (shaAddress base) next n = some out := by
          simpa [runUntilReturn, step] using run
        obtain ⟨rest, path, bound⟩ := ih tail
        exact ⟨trace :: rest, .cons (.sha step) path, by simp; omega⟩
      · have same : next = out := by simpa [runUntilReturn, step] using run
        subst out
        exact ⟨[trace], .cons (.sha step) (.nil _), by simp⟩

theorem hmac_step_fetched (base : Addr) (r : Routine) (s : CPU) (off : Nat)
    (op : Op) (body : r = entry ∨ r = key ∨ r = finish)
    (loaded : r.Loaded (routineAddress base r) s.mem.read8)
    (pc : s.pc = routineAddress base r + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt r off = some op) (positive : 0 < op.width)
    (within : off + op.width ≤ r.image.size)
    (allowed : (op.accesses s).all (Access.permitted s.mem) = true) :
    ProgramStep base s (op.accesses s) (op.step s) :=
  .hmac body (r.fetch_at _ _ _ _ _ _ _ loaded pc addressable decoded positive within) allowed

private theorem width_store_permissions (m : Memory) (w : Width) (p v : Addr) (atAddr : Addr) (n : Nat) :
    (w.store m p v).canWrite atAddr n = m.canWrite atAddr n ∧
      (m.canRead atAddr n = true → (w.store m p v).canRead atAddr n = true) := by
  cases w
  · exact ⟨by simp [Width.store], canRead_write8 _ _ _ _ _⟩
  · exact ⟨by simp [Width.store], canRead_write32 _ _ _ _ _⟩
  · exact ⟨by simp [Width.store], canRead_write64 _ _ _ _ _⟩

private theorem scalar_permissions (s : CPU) (i : Instruction) (p : Addr) (n : Nat) :
    (i.step s).mem.canWrite p n = s.mem.canWrite p n ∧
      (s.mem.canRead p n = true → (i.step s).mem.canRead p n = true) := by
  cases i with | mk op width =>
  cases op <;> simp only [Instruction.step, memory_put, memory_advance, memory_write]
  case store => exact width_store_permissions _ _ _ _ _ _
  case branch => split <;> exact ⟨rfl, id⟩
  all_goals first | exact ⟨rfl, id⟩ | exact ⟨True.intro, id⟩

private theorem local_permissions (s : CPU) (op : Op) (p : Addr) (n : Nat) :
    (op.step s).mem.canWrite p n = s.mem.canWrite p n ∧
      (s.mem.canRead p n = true → (op.step s).mem.canRead p n = true) := by
  cases op with
  | scalar i => exact scalar_permissions s i p n
  | sub => exact ⟨rfl, id⟩
  | lui => exact ⟨rfl, id⟩
  | jal => exact ⟨rfl, id⟩

private theorem checked_permissions {base : Addr} {s out : CPU} {events : List Access} {ret : Bool}
    (step : checkedStep base s = some (out, events, ret)) (p : Addr) (n : Nat) :
    out.mem.canWrite p n = s.mem.canWrite p n ∧
      (s.mem.canRead p n = true → out.mem.canRead p n = true) := by
  unfold checkedStep at step
  split at step
  · contradiction
  · rename_i i decoded
    dsimp only at step
    split at step
    · have outEq : i.step s = out :=
        congrArg (fun args : CPU × List Access × Bool => args.1) (Option.some.inj step)
      rw [← outEq]
      exact scalar_permissions s i p n
    · contradiction

private theorem scalar_perm (s : CPU) (i : Instruction) (p : Addr) :
    (i.step s).mem.perm p = s.mem.perm p := by
  cases i with | mk op width =>
  cases op <;> simp only [Instruction.step, memory_put, memory_advance, memory_write]
  case store w src base imm =>
    cases w <;> simp [Width.store, Arm64.Memory.write32, Arm64.Memory.write64,
      Crypto.ARM64.Imported.perm_write8]
  all_goals first | rfl | (split <;> rfl)

private theorem local_perm (s : CPU) (op : Op) (p : Addr) :
    (op.step s).mem.perm p = s.mem.perm p := by
  cases op
  case scalar i => exact scalar_perm s i p
  all_goals rfl

private theorem writable_outside (m : Memory) (addr p : Addr) (width : Nat)
    (write : m.canWrite addr width = true) (unwritable : ((m.perm p).w && !(m.perm p).x) = false) :
    width ≤ (p - addr).toNat := by
  by_contra! inside
  have byte := (Crypto.ARM64.Imported.allPerm_true_iff m
    (fun perm => perm.w && !perm.x) addr width).mp write _ inside
  rw [Crypto.ARM64.Imported.address_reconstruct addr p, unwritable] at byte
  contradiction

private theorem width_store_outside (m : Memory) (addr p v : Addr) (w : Width)
    (outside : w.bytes ≤ (p - addr).toNat) : (w.store m addr v).cells p = m.cells p := by
  cases w with
  | byte =>
    apply Crypto.ARM64.Imported.cells_write8_outside
    intro same
    subst p
    simp [Width.bytes] at outside
  | word => exact Crypto.ARM64.Imported.write32_cells_outside _ _ _ _ outside
  | double => exact Crypto.ARM64.Imported.write64_cells_outside _ _ _ _ outside

private theorem scalar_protected (s : CPU) (i : Instruction) (p : Addr)
    (allowed : (i.observations s).all (Access.permitted s.mem) = true)
    (unwritable : ((s.mem.perm p).w && !(s.mem.perm p).x) = false) :
    (i.step s).mem.cells p = s.mem.cells p := by
  cases i with | mk op width =>
  cases op <;> simp only [Instruction.step, memory_advance, memory_put, memory_write]
  case store w src base disp =>
    simp only [Instruction.observations, Crypto.RISCV64.Op.accesses, List.all_cons, List.all_nil,
      Bool.and_true, Access.permitted, Bool.and_eq_true] at allowed
    exact width_store_outside _ _ _ _ w (writable_outside _ _ _ _ allowed.2.2 unwritable)
  case branch => split <;> rfl
  all_goals rfl

private theorem local_protected (s : CPU) (op : Op) (p : Addr)
    (allowed : (op.accesses s).all (Access.permitted s.mem) = true)
    (unwritable : ((s.mem.perm p).w && !(s.mem.perm p).x) = false) :
    (op.step s).mem.cells p = s.mem.cells p := by
  cases op
  case scalar i => exact scalar_protected s i p allowed unwritable
  all_goals rfl

private theorem checked_step_result {base : Addr} {s out : CPU} {events : List Access} {ret : Bool}
    (step : checkedStep base s = some (out, events, ret)) :
    ∃ i : Instruction, out = i.step s ∧ events = i.observations s ∧
      events.all (Access.permitted s.mem) = true := by
  unfold checkedStep at step
  split at step
  · contradiction
  · rename_i i decoded
    dsimp only at step
    split at step
    · rename_i permitted
      have prod := Option.some.inj step
      have state : i.step s = out := congrArg (fun v : CPU × List Access × Bool => v.1) prod
      have accesses : i.observations s = events :=
        congrArg (fun v : CPU × List Access × Bool => v.2.1) prod
      exact ⟨i, state.symm, accesses.symm, accesses ▸ permitted⟩
    · contradiction

attribute [local irreducible] entry key finish shaAddress checkedStep

theorem ProgramStep.permissions {base : Addr} {s out : CPU} {events : List Access}
    (step : ProgramStep base s events out) (p : Addr) (n : Nat) :
    out.mem.canWrite p n = s.mem.canWrite p n ∧
      (s.mem.canRead p n = true → out.mem.canRead p n = true) := by
  cases step with
  | @hmac r s op => exact local_permissions s op p n
  | sha step => exact checked_permissions step p n

theorem ProgramStep.perm {base : Addr} {s out : CPU} {events : List Access}
    (step : ProgramStep base s events out) (p : Addr) : out.mem.perm p = s.mem.perm p := by
  cases step with
  | @hmac r s op => exact local_perm s op p
  | sha step =>
    obtain ⟨i, eq, _⟩ := checked_step_result step
    rw [eq]
    exact scalar_perm s i p

theorem ProgramStep.allowed {base : Addr} {s out : CPU} {events : List Access}
    (step : ProgramStep base s events out) : events.all (Access.permitted s.mem) = true := by
  cases step with
  | hmac _ _ allowed => exact allowed
  | sha step => exact (checked_step_result step).elim fun _ result => result.2.2

theorem ProgramStep.protected {base : Addr} {s out : CPU} {events : List Access}
    (step : ProgramStep base s events out) (p : Addr)
    (readonly : ((s.mem.perm p).w && !(s.mem.perm p).x) = false) :
    out.mem.cells p = s.mem.cells p := by
  cases step with
  | @hmac r s op _ _ allowed => exact local_protected s op p allowed readonly
  | sha step =>
    obtain ⟨i, eq, observes, allowed⟩ := checked_step_result step
    rw [eq]
    exact scalar_protected s i p (by rw [← observes]; exact allowed) readonly

theorem ProgramExecution.perm {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (p : Addr) : out.mem.perm p = s.mem.perm p := by
  induction run with
  | nil => rfl
  | cons head _ ih => exact ih.trans (head.perm p)

theorem ProgramExecution.protected {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (p : Addr)
    (readonly : ((s.mem.perm p).w && !(s.mem.perm p).x) = false) :
    out.mem.cells p = s.mem.cells p := by
  induction run with
  | nil => rfl
  | cons head _ ih =>
    exact (ih (by rw [head.perm p]; exact readonly)).trans (head.protected p readonly)

theorem ProgramExecution.permissions {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) (p : Addr) (n : Nat) :
    out.mem.canWrite p n = s.mem.canWrite p n ∧
      (s.mem.canRead p n = true → out.mem.canRead p n = true) := by
  induction run with
  | nil => exact ⟨rfl, id⟩
  | cons head _ ih =>
    have first := head.permissions p n
    exact ⟨ih.1.trans first.1, fun readable => ih.2 (first.2 readable)⟩

end Crypto.HMACSHA256.RISCV64
