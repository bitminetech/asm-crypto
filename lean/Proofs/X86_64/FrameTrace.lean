import Proofs.X86_64.TracePaths

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (DataAccess)

def frameCode (code : List Instr) : Bool :=
  code.all (fun i => ((accessForms i).getD []).all (fun a => decide (directStack a))) &&
    code.dropLast.all keepsStack

def frameEvents (sp pc : Val) : List Instr → List Event
  | [] => []
  | i::rest =>
    (pc,i,((accessForms i).getD []).map (fun a => ⟨a.write,sp+a.ea.disp,a.bytes⟩)) ::
      frameEvents sp (pc + BitVec.ofNat 64 i.len) rest

private theorem direct_access (s : Cpu) (i : Instr) (leaf : ScalarLeaf i)
    (allDirect : ((accessForms i).getD []).all (fun a => decide (directStack a)) = true) :
    (dataAccesses i s).getD [] =
      ((accessForms i).getD []).map (fun a => ⟨a.write,s.regs.get .rsp+a.ea.disp,a.bytes⟩) := by
  rw [dataAccesses_forms i s leaf]
  cases eq : accessForms i with
  | none => rfl
  | some forms =>
    simp only [Option.map_some, Option.getD_some]
    apply List.map_congr_left
    intro a member
    have h := of_decide_eq_true (List.all_eq_true.mp allDirect a (by simpa only [eq,Option.getD_some] using member))
    obtain ⟨b,idx,rip,seg⟩ := h
    simp [AccessForm.eval,Ea.addr, Ea.offset, b, idx, rip, seg]

attribute [local irreducible] X86.step

private theorem code_frame_events {base : Val} {s out : Cpu} {code}
    (actual : ObservedExecution base s (observeCode code s) out)
    (straight : code.dropLast.all linear = true) (fixed : frameCode code = true) :
    observeCode code s = frameEvents (s.regs.get .rsp) s.rip code := by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih =>
    have head := fixed
    simp only [frameCode, List.all_cons, Bool.and_eq_true] at head
    rw [observeCode] at actual
    cases actual with
    | cons fetched executed observed rest =>
      have leaf := fetched_scalar fetched
      have direct := direct_access s i leaf head.1.1
      have live : s.ms = none := by
        cases h : s.ms with
        | none => rfl
        | some e => simp [stepLoaded,Cpu.stopped,h,guard] at executed
      have shape : stepLoaded base s = some (X86.step i s) := by
        simp [stepLoaded,Cpu.stopped,live,fetched,guard]
      have next := Option.some.inj (shape.symm.trans executed)
      rw [← next] at rest
      rw [observeCode,frameEvents,direct]
      congr 1
      cases code with
      | nil => rfl
      | cons j more =>
        have stable : keepsStack i = true ∧ ((j::more).dropLast.all keepsStack = true) := by
          simpa only [List.dropLast_cons₂,List.all_cons,Bool.and_eq_true] using head.2
        have tailFixed : frameCode (j::more) = true :=
          Bool.and_eq_true_iff.mpr ⟨head.1.2, stable.2⟩
        have straight' : linear i = true ∧ ((j::more).dropLast.all linear = true) := by
          simpa only [List.dropLast_cons₂,List.all_cons,Bool.and_eq_true] using straight
        have running : (X86.step i s).ms = none := by
          cases rest with
          | cons _ executed _ _ =>
            cases h : (X86.step i s).ms with
            | none => rfl
            | some e => simp [stepLoaded,Cpu.stopped,h,guard] at executed
        rw [ih rest straight'.2 tailFixed]
        obtain ⟨form,eq⟩ := leaf
        obtain ⟨op,len⟩ := i
        change op = form.op at eq
        subst op
        have sp : (X86.step ⟨form.op,len⟩ s).regs.get .rsp = s.regs.get .rsp :=
          keep_stack _ _ _ live stable.1
        rw [sp, linear_pc ⟨form,rfl⟩ live running straight'.1]

/-- Once a decoded linear fragment is known to execute, its direct stack
observations are determined by its entry RSP and RIP. -/
theorem steps_observe_frame {base s out off code}
    (run : steps base code.length s = some out) (pc : s.rip = base + BitVec.ofNat 64 off)
    (decoded : decodeSeq off code.length = some code) (straight : code.dropLast.all linear = true)
    (fixed : frameCode code = true) :
    ObservedExecution base s (frameEvents (s.regs.get .rsp) (base + BitVec.ofNat 64 off) code) out := by
  have actual := steps_observe_linear run pc decoded straight
  rw [code_frame_events actual straight fixed, pc] at actual
  exact actual

def frameFragment (base sp : Val) (off count : Nat) : List Event :=
  frameEvents sp (base+BitVec.ofNat 64 off) ((decodeSeq off count).getD [])

def frameFragmentValid (off count : Nat) : Bool :=
  match decodeSeq off count with
  | none => false
  | some code => decide (code.length = count) && code.dropLast.all linear && frameCode code

theorem steps_observe_fragment {base s out off count}
    (run : steps base count s = some out) (pc : s.rip = base+BitVec.ofNat 64 off)
    (valid : frameFragmentValid off count = true) :
    ObservedExecution base s (frameFragment base (s.regs.get .rsp) off count) out := by
  unfold frameFragmentValid at valid
  cases decoded : decodeSeq off count with
  | none => simp [decoded] at valid
  | some code =>
    simp only [decoded, Bool.and_eq_true, decide_eq_true_eq] at valid
    unfold frameFragment
    rw [decoded, Option.getD_some]
    exact steps_observe_frame (valid.1.1.symm ▸ run) pc (valid.1.1.symm ▸ decoded) valid.1.2 valid.2

end Crypto.X86_64
