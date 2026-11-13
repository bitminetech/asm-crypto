import Proofs.ARM64.ImportedInterleavingModel
import Proofs.ARM64.ImportedEntryInterference

/-!
Dynamic SHA-256 stack borrowing. Input/image/output remain borrowed throughout.
Stack allocation and accessibility remain reserved, while its BYTES become
exclusive only after SUB and cease being active after ADD restores SP.
Thus valid asynchronous users may change unallocated/deallocated stack bytes.
Their handling of residual secrets remains a caller/environment confidentiality
obligation; permission to reuse stack is not permission to disclose old bytes.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline

def staticBorrowScope (base : BitVec 64) (s : Arm64.State) (extent : Nat) : BorrowScope where
  shared p := (callerInput s extent).Contains p ∨ (callerImage base).Contains p
  exclusive p := (callerOutput s).Contains p

def stackActive (entry current : Arm64.State) : Prop := current.sp = entryStack entry

structure DynamicEnvironment (base : BitVec 64) (entry : Arm64.State) (extent : Nat) where
  advance : Nat → Arm64.State → Arm64.State
  event : Nat → Arm64.State → AccessEvent
  cpu : ∀ tick s, CPUProjection (advance tick s) = CPUProjection s
  staticCells : ∀ tick s, SameCellsOn (entryProtected base entry extent) s.mem (advance tick s).mem
  staticAccesses : ∀ tick s, EnvironmentAccess (staticBorrowScope base entry extent) (event tick s)
  activeStackCells : ∀ tick s, stackActive entry s →
    SameCellsOn (callerStack entry).Contains s.mem (advance tick s).mem
  activeAccesses : ∀ tick s, stackActive entry s →
    EnvironmentAccess (shaBorrowScope base entry extent) (event tick s)
  reservation : ∀ tick s, EntryStackGrants entry s.mem → EntryStackGrants entry (advance tick s).mem
  reservedLifetime : ∀ tick s p, (callerStack entry).Contains p →
    ¬(event tick s).releases p ∧ ¬(event tick s).changesProtection p

theorem static_borrow_protected (base : BitVec 64) (s : Arm64.State) (extent : Nat) (p : BitVec 64) :
    (staticBorrowScope base s extent).protected p ↔ entryProtected base s extent p := by
  simp only [BorrowScope.protected, staticBorrowScope, entryProtected]
  tauto

def DynamicEnvironment.static {base : BitVec 64} {entry : Arm64.State} {extent : Nat}
    (environment : DynamicEnvironment base entry extent) :
    BorrowEnvironment (staticBorrowScope base entry extent) (fun _ => True) where
  advance := environment.advance
  event := environment.event
  cpu := environment.cpu
  cells tick s _ p inside := environment.staticCells tick s p ((static_borrow_protected base entry extent p).mp inside)
  accesses tick s _ := environment.staticAccesses tick s

def DynamicEnvironment.active {base : BitVec 64} {entry : Arm64.State} {extent : Nat}
    (environment : DynamicEnvironment base entry extent) :
    BorrowEnvironment (shaBorrowScope base entry extent) (stackActive entry) where
  advance := environment.advance
  event := environment.event
  cpu := environment.cpu
  cells tick s active p inside := by
    rcases inside with (input | image) | output | stack
    · exact environment.staticCells tick s p (Or.inl input)
    · exact environment.staticCells tick s p (Or.inr (Or.inl image))
    · exact environment.staticCells tick s p (Or.inr (Or.inr output))
    · exact environment.activeStackCells tick s active p stack
  accesses := environment.activeAccesses

theorem stackActive_cpu_invariant (entry : Arm64.State) : EnabledCPUInvariant (stackActive entry) := by
  intro left right same active
  have sp := congrArg Arm64.State.sp same
  simp only [projection_sp] at sp
  exact sp.symm.trans active

theorem always_enabled_cpu_invariant : EnabledCPUInvariant (fun _ : Arm64.State => True) := by
  intro left right same active
  exact True.intro

end Crypto.ARM64.Imported
