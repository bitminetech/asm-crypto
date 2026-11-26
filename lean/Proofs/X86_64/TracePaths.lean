import Proofs.X86_64.Observations
import Proofs.X86_64.ScalarControl

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

def linear (i : Instr) : Bool :=
  match i.op with
  | .ret | .jmp .. | .jcc .. => false
  | _ => true

private theorem linear_no_transfer {i : Instr} (h : linear i = true) (pc : Val) :
    nextAddresses pc i = [pc + BitVec.ofNat 64 i.len] := by
  cases i with
  | mk op len =>
    cases op <;> simp_all [linear,nextAddresses]

theorem linear_pc {s : Cpu} {i : Instr} (supported : ScalarLeaf i)
    (live : s.ms = none) (after : (X86.step i s).ms = none) (h : linear i = true) :
    (X86.step i s).rip = s.rip + BitVec.ofNat 64 i.len := by
  obtain ⟨form, eq⟩ := supported
  obtain ⟨op,len⟩ := i
  change op = form.op at eq
  subst op
  have regular : isReturn ⟨form.op,len⟩ = false := by
    cases form <;> first | rfl | contradiction
  have one := step_edges form len s live regular after
  rw [linear_no_transfer h] at one
  exact List.mem_singleton.mp one

private theorem addr_offset {base p : Val} {off : Nat} (pc : p = base + BitVec.ofNat 64 off)
    (bound : off < codeEnd) : (p-base).toNat = off := by
  have small : off < 2^64 := Nat.lt_trans bound (by decide)
  rw [pc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

attribute [local irreducible] fetch decodeAt X86.step image

/-- An existing successful prefix proof yields the exact observations when all
its instructions before the last are straight line. The last instruction may
transfer control. Each observed instruction still comes from the actual fetch. -/
theorem steps_observe_linear {base s out off code}
    (run : steps base code.length s = some out) (pc : s.rip = base + BitVec.ofNat 64 off)
    (decoded : decodeSeq off code.length = some code) (straight : code.dropLast.all linear = true) :
    ObservedExecution base s (observeCode code s) out := by
  induction code generalizing s off with
  | nil => simp [steps] at run; subst out; exact .nil _
  | cons i tail ih =>
    rw [List.length_cons, decodeSeq] at decoded
    obtain ⟨i',first,next⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨_,limit,next⟩ := Option.bind_eq_some_iff.mp next
    obtain ⟨rest,restBytes,next⟩ := Option.bind_eq_some_iff.mp next
    have codeEq : i'::rest = i::tail := Option.some.inj next
    injection codeEq with eq restEq
    subst i' rest
    have bound : off < codeEnd := by
      by_contra no
      simp only [guard] at limit
      simp only [no,false_and,if_false] at limit
      cases limit
    rw [List.length_cons, steps, stepInside] at run
    cases live : s.stopped
    · cases f : fetch base s with
      | none => simp [live,guard,f] at run
      | some fetched =>
        have actual := fetch_decodes f
        rw [addr_offset pc bound, first] at actual
        obtain rfl := Option.some.inj actual
        cases ret : isReturn i
        · have continued : steps base tail.length (X86.step i s) = some out := by
            simpa [live, guard, f, ret] using run
          have actualStep : stepLoaded base s = some (X86.step i s) := by simp [stepLoaded, live, guard, f]
          obtain ⟨acc,obs⟩ := scalar_accesses_defined i s (fetched_scalar f)
          have tailObserved : ObservedExecution base (X86.step i s) (observeCode tail (X86.step i s)) out := by
            cases tail with
            | nil =>
              simp [steps] at continued
              subst out
              exact .nil _
            | cons j more =>
              have straight' : linear i = true ∧ ((j::more).dropLast.all linear = true) := by
                simpa [List.dropLast_cons₂] using straight
              have nextLive : (X86.step i s).ms = none := by
                cases stopped : (X86.step i s).ms with
                | none => rfl
                | some error => simp [steps, stepInside, Cpu.stopped, guard, stopped] at continued
              have before : s.ms = none := by
                cases h : s.ms with
                | none => rfl
                | some e => simp [Cpu.stopped,h] at live
              apply ih continued _ restBytes straight'.2
              rw [linear_pc (fetched_scalar f) before nextLive straight'.1, pc, BitVec.ofNat_add, BitVec.add_assoc]
          simpa [observeCode,obs] using ObservedExecution.cons f actualStep obs tailObserved
        · simp [live,guard,f,ret] at run
    · simp [live,guard] at run

theorem steps_observe_single {base s out off i accesses}
    (run : steps base 1 s = some out) (pc : s.rip = base+BitVec.ofNat 64 off)
    (decode : decodeAt image off = some i) (before : off < codeEnd) (after : off+i.len ≤ codeEnd)
    (seen : dataAccesses i s = some accesses) :
    ObservedExecution base s [(base+BitVec.ofNat 64 off,i,accesses)] out := by
  have bytes : decodeSeq off 1 = some [i] := by simp [decodeSeq,decode,before,after,guard]
  simpa only [observeCode,pc,seen,Option.getD_some] using steps_observe_linear (code := [i]) run pc bytes rfl

end Crypto.X86_64
