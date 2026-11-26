import Models.X86SHA256Decode
import Proofs.ARM64.ImportedAccess

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

def operandAccess (s : Cpu) (nr : Val) (write : Bool) (sz : Size) : Operand → List DataAccess
  | .mem ea => [⟨write, ea.addr s nr, sz.bytes⟩]
  | _ => []

/-- Architectural data operands, evaluated at the actual pre-instruction CPU.
Read-modify-write forms report both accesses. Instruction fetches are accounted
for separately by `Execution.fetch_authorized`. -/
def dataAccesses (i : Instr) (s : Cpu) : Option (List DataAccess) :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  let src := operandAccess s nr false
  let dst := operandAccess s nr true
  let sp := s.regs.get .rsp
  match i.op with
  | .mov sz d v => some (src sz v ++ dst sz d)
  | .movx _ _ sz _ v => some (src sz v)
  | .bin k sz d v =>
    let writes := match k with | .cmp | .test => [] | _ => dst sz d
    some (src sz d ++ src sz v ++ writes)
  | .rot _ sz d _ | .shift _ sz d _ | .un _ sz d => some (src sz d ++ dst sz d)
  | .push .q (.reg ..) => some [⟨true,sp-8,8⟩]
  | .pop .q (.reg ..) | .ret => some [⟨false,sp,8⟩]
  | .lea .. | .bswap .. | .jmp (.rel _) | .jcc .. => some []
  | _ => none

theorem scalar_accesses_defined (i : Instr) (s : Cpu) (leaf : ScalarLeaf i) :
    ∃ accesses, dataAccesses i s = some accesses := by
  rcases i with ⟨op,len⟩
  obtain ⟨form,h⟩ := leaf
  change op = form.op at h
  subst op
  cases form <;> exact ⟨_, rfl⟩

/-- Execution paired with the exact ordered operand observations. -/
inductive ObservedExecution (base : Val) : Cpu → List (Val × Instr × List DataAccess) → Cpu → Prop where
  | nil (s) : ObservedExecution base s [] s
  | cons {s next out i accesses tail} (fetched : fetch base s = some i)
      (executed : stepLoaded base s = some next) (observed : dataAccesses i s = some accesses)
      (rest : ObservedExecution base next tail out) :
      ObservedExecution base s ((s.rip,i,accesses) :: tail) out

abbrev Event := Val × Instr × List DataAccess

def observeCode : List Instr → Cpu → List Event
  | [], _ => []
  | i::rest, s => (s.rip,i,(dataAccesses i s).getD []) :: observeCode rest (X86.step i s)

theorem ObservedExecution.append {base a b c x y}
    (left : ObservedExecution base a x b) (right : ObservedExecution base b y c) :
    ObservedExecution base a (x++y) c := by
  induction left with
  | nil => exact right
  | cons fetch steps obs rest ih => exact .cons fetch steps obs (ih right)

/-- The encoded address expression of a data operand. Implicit stack
operands use RSP as their base and a displacement of -8 for PUSH. -/
structure AccessForm where
  write : Bool
  ea : Ea
  bytes : Nat

private def form (write : Bool) (size : Size) : Operand → List AccessForm
  | .mem ea => [⟨write, ea, size.bytes⟩]
  | _ => []

def accessForms (i : Instr) : Option (List AccessForm) :=
  match i.op with
  | .mov sz dst src => some (form false sz src ++ form true sz dst)
  | .movx _ _ sz _ src => some (form false sz src)
  | .bin k sz dst src =>
    let writes := match k with | .cmp | .test => [] | _ => form true sz dst
    some (form false sz dst ++ form false sz src ++ writes)
  | .rot _ sz dst _ | .shift _ sz dst _ | .un _ sz dst =>
    some (form false sz dst ++ form true sz dst)
  | .push .q (.reg ..) => some [⟨true, {base := some .rsp, disp := -8}, 8⟩]
  | .pop .q (.reg ..) | .ret => some [⟨false, {base := some .rsp}, 8⟩]
  | .lea .. | .bswap .. | .jmp (.rel _) | .jcc .. => some []
  | _ => none

def AccessForm.eval (s : Cpu) (nr : Val) (a : AccessForm) : DataAccess :=
  ⟨a.write, a.ea.addr s nr, a.bytes⟩

theorem dataAccesses_forms (i : Instr) (s : Cpu) (supported : ScalarLeaf i) :
    dataAccesses i s = (accessForms i).map (List.map (AccessForm.eval s (s.rip + BitVec.ofNat 64 i.len))) := by
  obtain ⟨op,len⟩ := i
  obtain ⟨sample,eq⟩ := supported
  change op = sample.op at eq
  subst op
  have evaluate (nr : Val) (write : Bool) (sz : Size) (o : Operand) :
      (form write sz o).map (AccessForm.eval s nr) = operandAccess s nr write sz o := by
    cases o <;> rfl
  cases sample
  all_goals try cases ‹BinKind›
  all_goals try cases ‹Bool›
  all_goals simp [ScalarForm.op, dataAccesses, accessForms, List.map_append, evaluate,
    AccessForm.eval, Ea.addr, Ea.offset, BitVec.sub_eq_add_neg]

def directStack (a : AccessForm) : Prop :=
  a.ea.base = some .rsp ∧ a.ea.index = none ∧ a.ea.ripRel = false ∧ a.ea.seg = none

private instance (a : AccessForm) : Decidable (directStack a) := by
  unfold directStack
  infer_instance

end Crypto.X86_64
