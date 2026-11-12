import Proofs.ARM64.ImportedWholeCall

/-!
Code-loading invariants for the instruction families in the SHA-256 image.
Permission-checked scalar stores preserve every loaded RX code byte, and the
permitted evaluator preserves CodeLoaded throughout successful word-list runs.
These are fetch-bridge helpers, not a whole-call fetched-execution certificate.
-/
namespace Crypto.ARM64.Imported

/- The bounded permission lemma follows ProofLib/Invariant.lean at the pinned
Google DeepMind revision; the address identity here uses bit-vector group laws. -/
theorem allPerm_true_iff (m : Arm64.Memory) (test : Option Arm64.Perm → Bool)
    (base : BitVec 64) (n : Nat) :
    m.allPerm test base n = true ↔ ∀ i < n, test (m.perm (base + BitVec.ofNat 64 i)) = true := by
  induction n generalizing base with
  | zero => simp [Arm64.Memory.allPerm]
  | succ n ih =>
    simp only [Arm64.Memory.allPerm, Bool.and_eq_true, ih]
    have address (i : Nat) : base + 1#64 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.ofNat_add]
      ac_rfl
    constructor
    · rintro ⟨h0, hs⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have result := hs i (by omega)
        rwa [address i] at result
    · intro h
      refine ⟨by simpa using h 0 (by omega), ?_⟩
      intro i hi
      rw [address i]
      exact h (i + 1) (by omega)

theorem writable_ne_rx {m : Arm64.Memory} {base p : BitVec 64} {n : Nat}
    (write : m.canWrite base n = true) (rx : m.perm p = some Arm64.Perm.rx)
    (i : Nat) (hi : i < n) : p ≠ base + BitVec.ofNat 64 i := by
  intro he
  have byte := (allPerm_true_iff m (fun q => q.w && !q.x) base n).mp write i hi
  rw [← he, rx] at byte
  simp [Arm64.Perm.rx] at byte

theorem writable_rx_delta {m : Arm64.Memory} {base p : BitVec 64} {n : Nat}
    (write : m.canWrite base n = true) (rx : m.perm p = some Arm64.Perm.rx) :
    n ≤ (p - base).toNat := by
  by_contra hn
  have small : (p - base).toNat < n := by omega
  exact writable_ne_rx write rx _ small (address_reconstruct base p).symm

theorem writeSized_rx_cell (m : Arm64.Memory) (sz : Arm64.MemWidth) (base p : BitVec 64) (v : BitVec 64)
    (write : m.canWrite base sz.bytes = true) (rx : m.perm p = some Arm64.Perm.rx) :
    (m.writeSized sz base v).cells p = m.cells p := by
  have dist := writable_rx_delta write rx
  cases sz with
  | B8 =>
    have neq : p ≠ base := by simpa using writable_ne_rx write rx 0 (by decide)
    exact cells_write8_outside _ _ _ _ neq
  | H16 =>
    have n0 : p ≠ base := by simpa using writable_ne_rx write rx 0 (by decide)
    have n1 : p ≠ base + 1#64 := by simpa using writable_ne_rx write rx 1 (by decide)
    simp [Arm64.Memory.writeSized, Arm64.Memory.write16, n0, n1]
  | W32 => exact write32_cells_outside _ _ _ _ dist
  | X64 => exact write64_cells_outside _ _ _ _ dist

theorem codeLoaded_writeSized {prog : Arm64.Program} {m : Arm64.Memory}
    (loaded : prog.CodeLoaded m) (sz : Arm64.MemWidth) (base : BitVec 64) (v : BitVec 64)
    (write : m.canWrite base sz.bytes = true) : prog.CodeLoaded (m.writeSized sz base v) := by
  apply codeLoaded_of_cells loaded
  intro i hi
  exact writeSized_rx_cell m sz base _ v write ((codeLoaded_iff.mp loaded).2.2 i hi).2.1

@[simp] theorem canWrite_writeSized (m : Arm64.Memory) (sz : Arm64.MemWidth)
    (base : BitVec 64) (v : BitVec 64) (p : BitVec 64) (n : Nat) :
    (m.writeSized sz base v).canWrite p n = m.canWrite p n := by
  cases sz <;> simp [Arm64.Memory.writeSized, Arm64.Memory.write16]

theorem codeLoaded_writeSized_guard {prog : Arm64.Program} {m : Arm64.Memory}
    (loaded : prog.CodeLoaded m) {sz : Arm64.MemWidth} {a : BitVec 64}
    (h : ¬(!m.canWrite a sz.bytes) = true) (v : BitVec 64) :
    prog.CodeLoaded (m.writeSized sz a v) :=
  codeLoaded_writeSized loaded sz a v (by simpa using h)

theorem codeLoaded_writePair_guard {prog : Arm64.Program} {m : Arm64.Memory}
    (loaded : prog.CodeLoaded m) {sz : Arm64.MemWidth} {a b : BitVec 64}
    (h : ¬(!(m.canWrite a sz.bytes && m.canWrite b sz.bytes)) = true) (v w : BitVec 64) :
    prog.CodeLoaded ((m.writeSized sz a v).writeSized sz b w) := by
  have writes : m.canWrite a sz.bytes = true ∧ m.canWrite b sz.bytes = true := by simpa using h
  apply codeLoaded_writeSized (codeLoaded_writeSized loaded sz a v writes.1) sz b w
  rw [canWrite_writeSized]
  exact writes.2

theorem execStr_codeLoaded {prog : Arm64.Program} (size : Arm64.MemWidth)
    (rt : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) (loaded : prog.CodeLoaded s.mem) :
    prog.CodeLoaded (Arm64.execStr size rt addr s).mem := by
  simp only [Arm64.execStr]
  repeat' split
  all_goals first
    | exact loaded
    | exact codeLoaded_writeSized_guard loaded ‹_› _

theorem execStp_codeLoaded {prog : Arm64.Program} (w : Arm64.RegWidth)
    (rt1 rt2 : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) (loaded : prog.CodeLoaded s.mem) :
    prog.CodeLoaded (Arm64.execStp w rt1 rt2 addr s).mem := by
  simp only [Arm64.execStp]
  repeat' split
  all_goals first
    | exact loaded
    | exact codeLoaded_writePair_guard loaded ‹_› _ _

theorem codeLoaded_of_mem_eq {prog : Arm64.Program} {m before : Arm64.Memory}
    (loaded : prog.CodeLoaded before) (eq : m = before) : prog.CodeLoaded m := eq ▸ loaded

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem permitted_codeLoaded {prog : Arm64.Program} (instruction : Arm64.Instr)
    (allowed : permittedInstruction instruction = true) (s : Arm64.State)
    (loaded : prog.CodeLoaded s.mem) :
    prog.CodeLoaded (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).mem := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at allowed
  case str size rt addr => exact execStr_codeLoaded size rt addr s loaded
  case stp w rt1 rt2 addr => exact execStp_codeLoaded w rt1 rt2 addr s loaded
  all_goals apply codeLoaded_of_mem_eq loaded
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execLdp,
    Arm64.execAddSubImm, Arm64.execLogicalImm, Arm64.execMoveWide, Arm64.execBitfield,
    Arm64.execLogicalShift, Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1]
  all_goals repeat' split
  all_goals rfl

def PermittedWords (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ instruction, Arm64.decode word = some instruction → permittedInstruction instruction = true

theorem PermittedWords.tail {word : BitVec 32} {rest : List (BitVec 32)}
    (permitted : PermittedWords (word :: rest)) : PermittedWords rest := by
  intro w hw instruction decoded
  exact permitted w (by simp [hw]) instruction decoded

theorem runWords_codeLoaded {prog : Arm64.Program} (words : List (BitVec 32))
    (s out : Arm64.State) (permitted : PermittedWords words)
    (loaded : prog.CodeLoaded s.mem) (executed : runWords words s = some out) :
    prog.CodeLoaded out.mem := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact loaded
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      exact ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) permitted.tail
        (permitted_codeLoaded instruction (permitted word (by simp) instruction decoded) s loaded) executed

end Crypto.ARM64.Imported
