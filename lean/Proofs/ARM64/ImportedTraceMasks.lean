import Proofs.ARM64.ImportedAccess

/-!
Candidate program-point relation for SHA-256 architectural trace secrecy.
Temporary registers have distinct public lifetimes. Returned is an explicit
terminal point: a caller's link register may point into the same image.
These definitions alone prove no relational instruction transfer or secrecy.
-/
namespace Crypto.ARM64.Imported

inductive TracePoint where
  | instruction (index : Fin 151)
  | returned
  deriving DecidableEq

def publicGPRAt (point : TracePoint) (r : BitVec 5) : Bool :=
  match point with
  | .returned => decide (r.toNat = 0 ∨ r.toNat = 1 ∨ r.toNat = 30)
  | .instruction index =>
      let i := index.val
      decide (r.toNat = 0 ∨ r.toNat = 1 ∨ r.toNat = 30 ∨
        (r.toNat = 5 ∧ 2 ≤ i) ∨ (r.toNat = 2 ∧ 4 ≤ i) ∨
        (r.toNat = 3 ∧ 15 ≤ i) ∨ (r.toNat = 6 ∧ 17 ≤ i) ∨
        (r.toNat = 4 ∧ 41 ≤ i) ∨
        (r.toNat = 15 ∧ 3 ≤ i ∧ i ≤ 32) ∨
        (r.toNat = 17 ∧ ((14 ≤ i ∧ i ≤ 32) ∨ (50 ≤ i ∧ i ≤ 66))) ∨
        (r.toNat = 16 ∧ ((5 ≤ i ∧ i ≤ 38) ∨ (68 ≤ i ∧ i ≤ 71) ∨
          (107 ≤ i ∧ i ≤ 122) ∨ (132 ≤ i ∧ i ≤ 135))) ∨
        (r.toNat = 8 ∧ i = 32))

def flagsPublicAt : TracePoint → Bool
  | .returned => false
  | .instruction index => decide (index.val = 18 ∨ index.val = 27 ∨ index.val = 48 ∨
      index.val = 66 ∨ index.val = 105)

def registerPublicAt (point : TracePoint) : Arm64.Reg → Bool
  | .sp | .xzr => true
  | .gpr i => (i == 31#5) || publicGPRAt point i

def PublicRegistersAgree (point : TracePoint) (left right : Arm64.State) : Prop :=
  ∀ i, publicGPRAt point i = true → left.readReg64 (.gpr i) = right.readReg64 (.gpr i)

structure PublicRelation (point : TracePoint) (left right : Arm64.State) : Prop where
  pc : left.pc = right.pc
  sp : left.sp = right.sp
  registers : PublicRegistersAgree point left right
  flags : flagsPublicAt point = true → left.pstate = right.pstate

theorem PublicRelation.read {point : TracePoint} {left right : Arm64.State}
    (related : PublicRelation point left right) (r : Arm64.Reg)
    (visible : registerPublicAt point r = true) : left.readReg64 r = right.readReg64 r := by
  cases r with
  | sp => exact related.sp
  | xzr => rfl
  | gpr i =>
    by_cases zero : i = 31#5
    · simp [Arm64.State.readReg64, zero]
    · have selected : publicGPRAt point i = true := by simpa [registerPublicAt, zero] using visible
      exact related.registers i selected

end Crypto.ARM64.Imported
