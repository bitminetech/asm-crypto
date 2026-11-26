import Proofs.RISCV64.CallCode

namespace Crypto.RISCV64

def untouchedABIRegs : List Reg := [1, 3, 4, 24, 25, 26, 27]

private def noWriteTo (regs : List Reg) (code : List Instruction) : Bool :=
  code.all fun i => regs.all fun r => i.op.destination != some r

private theorem noWrite_append {regs : List Reg} {a b : List Instruction}
    (left : noWriteTo regs a = true) (right : noWriteTo regs b = true) : noWriteTo regs (a ++ b) = true := by
  simp only [noWriteTo, List.all_append, Bool.and_eq_true] at left right ⊢
  exact ⟨left, right⟩

private theorem noWrite_repeat (regs : List Reg) (loop : Nat → List Instruction) (cycle : List Instruction)
    (zero : loop 0 = []) (succ : ∀ n, loop (n+1) = loop n ++ cycle)
    (one : noWriteTo regs cycle = true) (n : Nat) : noWriteTo regs (loop n) = true := by
  induction n with
  | zero => simp [noWriteTo, zero]
  | succ n ih => rw [succ]; exact noWrite_append ih one

private theorem untouched_block : noWriteTo untouchedABIRegs blockCode = true := by
  have loads := noWrite_repeat untouchedABIRegs loadCode loadCycle rfl (fun _ => rfl) (by decide) 16
  have expansion := noWrite_repeat untouchedABIRegs expansionCode expansionCycle rfl (fun _ => rfl) (by decide) 48
  have rounds := noWrite_repeat untouchedABIRegs roundCode roundCycle rfl (fun _ => rfl) (by decide) 64
  simp only [blockCode, List.append_assoc, noWriteTo, List.all_append, Bool.and_eq_true] at ⊢
  exact ⟨by decide, loads, expansion, by decide, rounds, by decide, by decide⟩

private theorem untouched_marker (rem : Nat) : noWriteTo untouchedABIRegs (markerCode rem) = true := by
  by_cases small : rem < 56
  · simpa only [markerCode, if_pos small, if_pos (show 0 < 56 by decide)] using
      (show noWriteTo untouchedABIRegs (markerCode 0) = true by decide)
  · simpa only [markerCode, if_neg small, if_neg (show ¬56 < 56 by decide)] using
      (show noWriteTo untouchedABIRegs (markerCode 56) = true by decide)

attribute [local irreducible] loadCode expansionCode roundCode blockLoop

set_option maxRecDepth 12000 in
private theorem untouched_call (size : Nat) : noWriteTo untouchedABIRegs (callCode size) = true := by
  have blocks (n : Nat) : noWriteTo untouchedABIRegs (blockLoop n) = true := by
    induction n with
    | zero => simp [blockLoop, noWriteTo]
    | succ n ih => rw [blockLoop]; exact noWrite_append ih untouched_block
  have tail : noWriteTo untouchedABIRegs (tailCode (size % 64)) = true :=
    noWrite_append (noWrite_repeat untouchedABIRegs tailPrefix tailCycle rfl (fun _ => rfl)
      (by decide) _) (show noWriteTo untouchedABIRegs (tailCode 0) = true by decide)
  simp only [callCode, callBeforeReturn, List.append_assoc, noWriteTo, List.all_append, Bool.and_eq_true]
  exact ⟨by decide, by decide, by decide, by decide, tail, untouched_marker _, by decide, by decide,
    blocks _, by decide, by decide, by decide, blocks _, by decide, by decide, by decide, by decide⟩

/-- Registers outside the eight spill slots which the LP64D call preserves.
The stack pointer and spilled registers are restored by the epilogue proof. -/
theorem CallPath.untouched_regs {base : Addr} {s out : CPU} {data : ByteArray}
    (path : CallPath base s out data) (r : Reg) (callee : r ∈ untouchedABIRegs) : out.reg r = s.reg r := by
  apply path.decoded.register_unchanged
  intro inst member
  have stable := List.all_eq_true.mp (untouched_call data.size) inst member
  simpa using List.all_eq_true.mp stable r callee

end Crypto.RISCV64
