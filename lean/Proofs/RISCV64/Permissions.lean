import Proofs.RISCV64.AccessTrace
import Proofs.RISCV64.EntryMemory
import Proofs.ARM64.ImportedFetchMemory

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (allPerm_true_iff address_reconstruct cells_write8_outside
  write32_cells_outside write64_cells_outside canRead_write8 canRead_write32 canRead_write64)

/-- The mapped image may contain both executable text and read-only data. -/
def ImageReadOnly (base : Addr) (m : Memory) : Prop :=
  ∀ j < image.size, let p := m.perm (base + BitVec.ofNat 64 j); (p.w && !p.x) = false

private theorem Width.store_outside (w : Width) (m : Memory) (a p v : Addr)
    (apart : w.bytes ≤ (p-a).toNat) : (w.store m a v).cells p = m.cells p := by
  cases w with
  | byte =>
    apply cells_write8_outside
    intro same
    subst p
    simp [Width.bytes] at apart
  | word => exact write32_cells_outside _ _ _ _ apart
  | double => exact write64_cells_outside _ _ _ _ apart

private theorem Width.perm_store (w : Width) (m : Memory) (a p v : Addr) :
    (w.store m a v).perm p = m.perm p := by
  cases w <;> simp [Width.store, Arm64.Memory.write32, Arm64.Memory.write64]

private theorem Width.store_readable (w : Width) (m : Memory) (a p v : Addr) (n : Nat)
    (h : m.canRead p n = true) : (w.store m a v).canRead p n = true := by
  cases w
  · exact canRead_write8 _ _ _ _ _ h
  · exact canRead_write32 _ _ _ _ _ h
  · exact canRead_write64 _ _ _ _ _ h

private theorem Width.store_permitted (w : Width) (m : Memory) (a v : Addr) (access : Access)
    (h : access.permitted m = true) : access.permitted (w.store m a v) = true := by
  cases access with
  | fetch p n =>
    have same : (w.store m a v).canExec p n = m.canExec p n := by
      clear h
      unfold Arm64.Memory.canExec
      induction n generalizing p with
      | zero => rfl
      | succ n ih => simp only [Arm64.Memory.allPerm, w.perm_store, ih]
    simpa only [Access.permitted, same] using h
  | read p k =>
    simp only [Access.permitted, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, w.store_readable m a p v _ h.2⟩
  | write p k =>
    have same : (w.store m a v).canWrite p k.bytes = m.canWrite p k.bytes := by
      cases w <;> simp [Width.store, Arm64.Memory.canWrite, Arm64.Memory.write32, Arm64.Memory.write64]
    simpa only [Access.permitted, same] using h

private theorem Width.store_image {base a v : Addr} {w : Width} {m : Memory}
    (loaded : ImageLoaded base m) (readOnly : ImageReadOnly base m)
    (write : m.canWrite a w.bytes = true) :
    ImageLoaded base (w.store m a v) ∧ ImageReadOnly base (w.store m a v) := by
  constructor
  · apply ImageLoaded.of_cells loaded
    intro j hj
    apply w.store_outside
    by_contra h
    let p := base + BitVec.ofNat 64 j
    have small : (p-a).toNat < w.bytes := by change ¬w.bytes ≤ (p-a).toNat at h; omega
    have canWrite := (allPerm_true_iff m (fun p => p.w && !p.x) a w.bytes).mp write _ small
    rw [address_reconstruct a p] at canWrite
    have locked := readOnly j hj
    change ((m.perm p).w && !(m.perm p).x) = false at locked
    rw [locked] at canWrite
    exact Bool.false_ne_true canWrite
  · intro j hj
    simpa only [w.perm_store] using readOnly j hj

private theorem Instruction.permitted_after (i : Instruction) (s : CPU) (access : Access)
    (h : access.permitted s.mem = true) : access.permitted (i.step s).mem = true := by
  rcases i with ⟨op, size⟩
  cases op
  case store w src rs off => exact w.store_permitted s.mem _ _ access h
  case branch b x y off => simp only [Instruction.step]; split <;> exact h
  all_goals exact h

private theorem Instruction.keeps_image {base : Addr} (i : Instruction) (s : CPU)
    (loaded : ImageLoaded base s.mem) (readOnly : ImageReadOnly base s.mem)
    (allowed : (i.observations s).all (Access.permitted s.mem) = true) :
    ImageLoaded base (i.step s).mem ∧ ImageReadOnly base (i.step s).mem := by
  rcases i with ⟨op, size⟩
  cases op
  case store w src rs off =>
    simp only [Instruction.observations, Op.accesses, List.all_cons, List.all_nil,
      Bool.and_true, Access.permitted, Bool.and_eq_true] at allowed
    exact w.store_image loaded readOnly allowed.2.2
  case branch b x y off => simp only [Instruction.step]; split <;> exact ⟨loaded, readOnly⟩
  all_goals exact ⟨loaded, readOnly⟩

/-- Initial access permissions suffice for a decoded path with a protected
image. Stores preserve the image and all permissions needed by later steps. -/
theorem permittedPath_of_accesses (base : Addr) (s : CPU) (code : List Instruction)
    (loaded : ImageLoaded base s.mem) (readOnly : ImageReadOnly base s.mem)
    (allowed : (accessTrace code s).all (Access.permitted s.mem) = true) :
    PermittedPath base s code := by
  induction code generalizing s with
  | nil => exact .nil s
  | cons i tail ih =>
    simp only [accessTrace, List.all_append, Bool.and_eq_true] at allowed
    obtain ⟨loadNext, protectNext⟩ := i.keeps_image s loaded readOnly allowed.1
    refine .cons loaded allowed.1 (ih _ loadNext protectNext ?_)
    apply List.all_eq_true.mpr
    intro access occurs
    exact i.permitted_after s access (List.all_eq_true.mp allowed.2 access occurs)

theorem decodeAt_range {off : Nat} {i : Instruction}
    (decoded : decodeAt off = some i) : off % 2 = 0 ∧ off + i.bytes ≤ codeEnd := by
  unfold decodeAt decodeBytes at decoded
  by_cases start : off % 2 = 0 ∧ off + 2 ≤ codeEnd
  · refine ⟨start.1, ?_⟩
    simp [guard, start, Bind.bind, Option.bind] at decoded
    split at decoded
    · by_cases whole : off + 4 ≤ codeEnd
      · simp only [if_pos whole] at decoded
        split at decoded <;> simp_all
        subst i
        exact whole
      · simp [whole] at decoded
    · split at decoded <;> simp_all
      subst i
      exact start.2
  · simp [guard, start, Bind.bind, Option.bind] at decoded

private theorem decoded_fetch_allowed (base : Addr) (m : Memory) (pc : Addr) (i : Instruction)
    (aligned : base.toNat % 2 = 0) (executable : m.canExec base codeEnd = true)
    (decoded : decodeAt (pc-base).toNat = some i) :
    (Access.fetch pc i.bytes).permitted m = true := by
  let off := (pc-base).toNat
  obtain ⟨even, endFits⟩ := decodeAt_range decoded
  have position : pc = base + BitVec.ofNat 64 off := (address_reconstruct base pc).symm
  have reduced : off < 2^64 := (pc-base).isLt
  have alignedPC : pc.toNat % 2 = 0 := by
    rw [position, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt reduced]
    omega
  have execPC : m.canExec pc i.bytes = true := by
    apply (allPerm_true_iff m (·.x) pc i.bytes).mpr
    intro j hj
    rw [position, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (allPerm_true_iff m (·.x) base codeEnd).mp executable _ (by omega)
  simp only [Access.permitted, alignedPC, beq_self_eq_true, execPC, Bool.and_self]

def Access.isData : Access → Bool
  | .fetch .. => false
  | .read .. | .write .. => true

theorem ImageExecution.initial_permitted {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution base s code out) (initial : Memory)
    (aligned : base.toNat % 2 = 0) (executable : initial.canExec base codeEnd = true)
    (data : ((accessTrace code s).filter Access.isData).all (Access.permitted initial) = true) :
    (accessTrace code s).all (Access.permitted initial) = true := by
  induction path with
  | nil => rfl
  | @cons s out i tail decoded last rest ih =>
    simp only [accessTrace, List.filter_append, List.all_append, Bool.and_eq_true] at data ⊢
    refine ⟨?_, ih data.2⟩
    have fetch := decoded_fetch_allowed base initial s.pc i aligned executable decoded
    have isData (a : Access) (h : a ∈ i.op.accesses s) : a.isData = true := by
      cases op : i.op <;> simp_all [Op.accesses, Access.isData]
    simp only [Instruction.observations, List.all_cons, Bool.and_eq_true]
    refine ⟨fetch, List.all_eq_true.mpr ?_⟩
    intro a occur
    exact List.all_eq_true.mp data.1 a <| List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ occur, isData a occur⟩

end Crypto.RISCV64
