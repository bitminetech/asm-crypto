import Proofs.HMACSHA256.RISCV64Setup
import Proofs.HMACSHA256.RISCV64ShaEntry
import Proofs.RISCV64.RegionPermissions

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.ARM64.Imported (allPerm_true_iff)

theorem fetch_of_grant {r : Routine} {base : Addr} {m : Memory} {off width : Nat}
    (aligned : (routineAddress base r).toNat % 2 = 0)
    (within : off + width ≤ r.image.size) (even : off % 2 = 0)
    (grants : m.canExec (routineAddress base r) r.image.size = true) :
    (Access.fetch (routineAddress base r + BitVec.ofNat 64 off) width).permitted m = true := by
  simp only [Access.permitted, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, (allPerm_true_iff _ _ _ _).mpr ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (allPerm_true_iff _ _ _ _).mp grants _ (by omega)

theorem write_of_grant {m : Memory} {p : Addr} {size off : Nat}
    (aligned : p.toNat % 8 = 0) (within : off + 8 ≤ size) (even : off % 8 = 0)
    (grants : m.canWrite p size = true) :
    (Access.write (p + BitVec.ofNat 64 off) Width.double).permitted m = true :=
  (InRegion.permitted_write (⟨off, within, even, rfl⟩ : InRegion p size _ .double) aligned grants)

theorem read_of_grant {m : Memory} {p : Addr} {size off : Nat}
    (aligned : p.toNat % 8 = 0) (within : off + 8 ≤ size) (even : off % 8 = 0)
    (grants : m.canRead p size = true) :
    (Access.read (p + BitVec.ofNat 64 off) Width.double).permitted m = true :=
  (InRegion.permitted_read (⟨off, within, even, rfl⟩ : InRegion p size _ .double) aligned grants)

/-- A straight-line part of an actual HMAC body. The predicate inspects the
decoded instructions and their public fetch locations. Its permission
obligations are all stated against the memory at the start of the range. -/
def RangeReady (r : Routine) (base : Addr) (initial : Memory) (off : Nat)
    (s : CPU) : List Op → Prop
  | [] => True
  | op :: tail =>
    s.pc = routineAddress base r + BitVec.ofNat 64 off ∧ off < 2 ^ 64 ∧
    decodeAt r off = some op ∧ 0 < op.width ∧ off + op.width ≤ r.image.size ∧
    (op.accesses s).all (Access.permitted initial) = true ∧
    RangeReady r base initial (off + op.width) (op.step s) tail

def RoutineReadOnly (r : Routine) (base : Addr) (m : Memory) : Prop :=
  ∀ i < r.image.size,
    let perm := m.perm (routineAddress base r + BitVec.ofNat 64 i)
    (perm.w && !perm.x) = false

theorem routine_readonly_of_exec {r : Routine} {base : Addr} {m : Memory}
    (exec : m.canExec (routineAddress base r) r.image.size = true) :
    RoutineReadOnly r base m := by
  intro i hi
  have rights := (allPerm_true_iff _ _ _ _).mp exec i hi
  simp only [show (m.perm (routineAddress base r + BitVec.ofNat 64 i)).x = true from rights,
    Bool.not_true, Bool.and_false]

private theorem access_preserved {base : Addr} {s out : CPU} {event : List Access}
    (step : ProgramStep base s event out) (a : Access)
    (allowed : a.permitted s.mem = true) : a.permitted out.mem = true := by
  cases a with
  | fetch p bytes =>
    have exec : out.mem.canExec p bytes = s.mem.canExec p bytes :=
      allPerm_eq_of_perm step.perm _ _ _
    simpa only [Access.permitted, exec] using allowed
  | read p width =>
    simp only [Access.permitted, Bool.and_eq_true] at allowed ⊢
    exact ⟨allowed.1, (step.permissions p width.bytes).2 allowed.2⟩
  | write p width =>
    simpa only [Access.permitted, (step.permissions p width.bytes).1] using allowed

private theorem ready_after_permission {r : Routine} {base : Addr} {left right : Memory}
    (preserve : ∀ a : Access, a.permitted left = true → a.permitted right = true)
    (off : Nat) (s : CPU) (ops : List Op) (ok : RangeReady r base left off s ops) :
    RangeReady r base right off s ops := by
  induction ops generalizing off s with
  | nil => exact trivial
  | cons op tail ih =>
    obtain ⟨pc, address, decoded, width, within, allowed, rest⟩ := ok
    refine ⟨pc, address, decoded, width, within, List.all_eq_true.mpr ?_, ih _ _ rest⟩
    intro a seen
    exact preserve a (List.all_eq_true.mp allowed a seen)

def runOpsEvents : List Op → CPU → List (List Access)
  | [], _ => []
  | op :: tail, s => op.accesses s :: runOpsEvents tail (op.step s)

@[simp] theorem runOpsEvents_length (ops : List Op) (s : CPU) :
    (runOpsEvents ops s).length = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op tail ih => simp only [runOpsEvents, List.length_cons, ih]

set_option maxHeartbeats 1000000 in
theorem ready_range_executes (r : Routine) (base : Addr) (off : Nat) (s : CPU) (ops : List Op)
    (body : r = entry ∨ r = key ∨ r = finish) (loaded : r.Loaded (routineAddress base r) s.mem.read8)
    (readonly : RoutineReadOnly r base s.mem) (ready : RangeReady r base s.mem off s ops) :
    ProgramExecution base s (runOpsEvents ops s) (runOps ops s) := by
  induction ops generalizing off s with
  | nil => exact .nil s
  | cons op tail ih =>
    obtain ⟨pc, address, decoded, width, within, allowed, rest⟩ := ready
    have step := hmac_step_fetched base r s off op body loaded pc address decoded width within allowed
    have loadedNext : r.Loaded (routineAddress base r) (op.step s).mem.read8 := by
      intro i bound
      exact (read8_same _ (step.protected _ (readonly i bound))).trans (loaded i bound)
    have readOnlyNext : RoutineReadOnly r base (op.step s).mem := by
      intro i bound
      simp only [step.perm]
      exact readonly i bound
    have tailReady := ready_after_permission (access_preserved step) _ _ _ rest
    exact .cons step (ih _ _ loadedNext readOnlyNext tailReady)

theorem ProgramExecution.keeps_routine {base : Addr} {r : Routine} {s out : CPU}
    {events : List (List Access)} (run : ProgramExecution base s events out)
    (loaded : r.Loaded (routineAddress base r) s.mem.read8) (readonly : RoutineReadOnly r base s.mem) :
    r.Loaded (routineAddress base r) out.mem.read8 ∧ RoutineReadOnly r base out.mem := by
  refine ⟨?_, ?_⟩
  · intro i within
    exact (read8_same _ (run.protected _ (readonly i within))).trans (loaded i within)
  · intro i within
    simp only [run.perm]
    exact readonly i within

def RangeAllowed (r : Routine) (base : Addr) (off count : Nat) (s : CPU) : Prop :=
  ∃ ops, decodeRange r off count = some ops ∧ RangeReady r base s.mem off s ops

private theorem decodeRange_count (r : Routine) (off count : Nat) (ops : List Op)
    (decoded : decodeRange r off count = some ops) : ops.length = count := by
  induction count generalizing off ops with
  | zero =>
    have empty : [] = ops := Option.some.inj decoded
    rw [← empty]
    rfl
  | succ n ih =>
    cases head : decodeAt r off with
    | none => simp [decodeRange, head] at decoded
    | some op =>
      cases tail : decodeRange r (off + op.width) n with
      | none => simp [decodeRange, head, tail] at decoded
      | some rest =>
        have layout : op :: rest = ops := by simpa [decodeRange, head, tail] using decoded
        rw [← layout, List.length_cons, ih _ _ tail]

theorem run_range_observes {r : Routine} {base : Addr} {off count : Nat} {s out : CPU} {ops : List Op}
    (body : r = entry ∨ r = key ∨ r = finish)
    (run : runRange r off count s = some out)
    (loaded : r.Loaded (routineAddress base r) s.mem.read8)
    (readonly : RoutineReadOnly r base s.mem) (allowed : RangeAllowed r base off count s)
    (decoded : decodeRange r off count = some ops) :
    ProgramExecution base s (runOpsEvents ops s) out ∧ (runOpsEvents ops s).length = count := by
  obtain ⟨actual, found, ready⟩ := allowed
  have eq : actual = ops := Option.some.inj (found.symm.trans decoded)
  subst actual
  have status : runOps ops s = out := by simpa [runRange, decoded] using run
  exact ⟨status ▸ ready_range_executes r base off s ops body loaded readonly ready,
    (runOpsEvents_length ops s).trans (decodeRange_count _ _ _ _ decoded)⟩

theorem run_range_executes {r : Routine} {base : Addr} {off count : Nat} {s out : CPU}
    (body : r = entry ∨ r = key ∨ r = finish)
    (run : runRange r off count s = some out)
    (loaded : r.Loaded (routineAddress base r) s.mem.read8)
    (readonly : RoutineReadOnly r base s.mem) (allowed : RangeAllowed r base off count s) :
    ∃ events, ProgramExecution base s events out ∧ events.length = count := by
  obtain ⟨ops, decoded, ready⟩ := allowed
  have traced := run_range_observes body run loaded readonly ⟨ops, decoded, ready⟩ decoded
  exact ⟨runOpsEvents ops s, traced.1, traced.2⟩

scoped macro "hmac_range_permissions" atPC:ident execAlign:ident execGrant:ident
    readAlign:ident readGrant:ident writeAlign:ident writeGrant:ident : tactic =>
  `(tactic| (
    simp (config := {decide := true}) only [RangeReady, Op.accesses, Op.width,
      Crypto.RISCV64.Op.accesses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Op.step, Instruction.step, pc_advance, pc_put, pc_write, reg_advance, reg_put, reg_write,
      if_false, if_true, BitVec.add_assoc, BitVec.zero_add, BitVec.add_zero, ($atPC), and_true, true_and,
      ← BitVec.sub_eq_add_neg]
    repeat' apply And.intro
    all_goals
      first
      | (guard_target =~ (Access.permitted _ (Access.fetch _ _) = true)
         exact fetch_of_grant $execAlign (by decide) (by decide) $execGrant)
      | (guard_target =~ (Access.permitted _ (Access.write _ _) = true)
         exact write_of_grant $writeAlign (by decide) (by decide) $writeGrant)
      | (guard_target =~ (Access.permitted _ (Access.read _ _) = true)
         exact read_of_grant $readAlign (by decide) (by decide) $readGrant)
      | assumption
      | rfl
      | decide +kernel
  ))

end Crypto.HMACSHA256.RISCV64
