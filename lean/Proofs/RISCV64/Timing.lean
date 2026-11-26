import Proofs.RISCV64.CallTrace

namespace Crypto.RISCV64

/-- The target supplies a cost law for the modeled RV64GC instruction subset.
Cost may depend on the instruction, public addresses, and control successor. -/
structure TimingProfile where
  cost : Instruction → CPU → Nat
  observedCost : Instruction → List Access → Addr → Nat
  observationLaw : ∀ i s, cost i s = observedCost i (i.observations s) (i.step s).pc

def TimingProfile.runCost (profile : TimingProfile) : List Instruction → CPU → Nat
  | [], _ => 0
  | i :: rest, s => profile.cost i s + profile.runCost rest (i.step s)

private theorem observations_length (i : Instruction) (s t : CPU) :
    (i.observations s).length = (i.observations t).length := by
  rcases i with ⟨op, bytes⟩
  cases op <;> rfl

private theorem entry_pc_of_trace {i : Instruction} {code : List Instruction} {s t : CPU}
    (trace : accessTrace (i :: code) s = accessTrace (i :: code) t) : s.pc = t.pc := by
  simp only [accessTrace, Instruction.observations, List.cons_append, List.cons.injEq,
    Access.fetch.injEq, and_true] at trace
  exact trace.1

theorem TimingProfile.cost_agrees (profile : TimingProfile) (code : List Instruction) (s t : CPU)
    (trace : accessTrace code s = accessTrace code t) (final : (run code s).pc = (run code t).pc) :
    profile.runCost code s = profile.runCost code t := by
  induction code generalizing s t with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨first, later⟩ := List.append_inj trace (observations_length i s t)
    have out : (run rest (i.step s)).pc = (run rest (i.step t)).pc := final
    have next : (i.step s).pc = (i.step t).pc := by
      cases rest with
      | nil => exact out
      | cons j tail => exact entry_pc_of_trace later
    have headCost := (profile.observationLaw i s).trans <| by
      rw [first, next, ← profile.observationLaw i t]
    simp only [TimingProfile.runCost, headCost, ih (i.step s) (i.step t) later out]

theorem call_public_cost (profile : TimingProfile) (base : Addr) (s t : CPU) (a b : ByteArray)
    (left : CallEntry base s a) (right : CallEntry base t b)
    (entry : PublicAgreement (publicRegs entryPublicRegs) s t)
    (sameSize : a.size = b.size) (samePayload : inputPayload s = inputPayload t) :
    profile.runCost (callCode a.size) s = profile.runCost (callCode b.size) t := by
  obtain ⟨trace, final⟩ := call_public_execution base s t a b left right entry sameSize samePayload
  rw [← sameSize] at trace final ⊢
  exact profile.cost_agrees _ _ _ trace final

end Crypto.RISCV64
