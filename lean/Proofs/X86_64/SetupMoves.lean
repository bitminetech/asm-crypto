import Proofs.X86_64.OuterControl
import Proofs.X86_64.TracePaths
import Proofs.ARM64.ImportedHashInitFrame

namespace Crypto.X86_64
open X86

/-- The qword moves and address computations in SHA-256's frame setup. -/
inductive FrameMove where
  | load (dst src : GPR) (disp : Val)
  | store (disp : Nat) (src : GPR)
  | constant (disp : Nat) (value : Val)
  | lea (dst src : GPR) (disp : Val)
  | relative (dst : GPR) (disp : Val)

def FrameMove.op : FrameMove → Op
  | .load dst src disp => .mov .q (.reg dst) (.mem {base := some src, disp})
  | .store d src => .mov .q (.mem {base := some .rsp, disp := BitVec.ofNat 64 d}) (.reg src)
  | .constant d v => .mov .q (.mem {base := some .rsp, disp := BitVec.ofNat 64 d}) (.imm v)
  | .lea dst src disp => .lea .q dst {base := some src, disp}
  | .relative dst disp => .lea .q dst {ripRel := true, disp}

def FrameMove.eval (m : FrameMove) (len : Nat) (s : Cpu) : Cpu :=
  let next := s.rip + BitVec.ofNat 64 len
  match m with
  | .load dst src disp => {s with rip := next, regs := s.regs.set dst (s.mem.readSize .q (s.regs.get src+disp))}
  | .store d src => {s with rip := next, mem := s.mem.writeSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) (s.regs.get src)}
  | .constant d v => {s with rip := next, mem := s.mem.writeSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) v}
  | .lea dst src disp => {s with rip := next, regs := s.regs.set dst (s.regs.get src+disp)}
  | .relative dst disp => {s with rip := next, regs := s.regs.set dst (next+disp)}

private theorem move_step (m : FrameMove) (len : Nat) (s : Cpu) (live : s.ms = none) :
    X86.step ⟨m.op,len⟩ s = m.eval len s := by
  cases m <;> simp [FrameMove.op, FrameMove.eval, X86.step, Cpu.stopped, live, wellFormed2,
    Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.getReg, Cpu.setReg, Cpu.readMem,
    Cpu.writeMem, Cpu.setRip, Value.writeView, Ea.addr, Ea.offset]

abbrev FrameCode := List (FrameMove × Nat)

def moveInstructions (code : FrameCode) : List Instr := code.map fun (m,n) => ⟨m.op,n⟩

def moveRun (code : FrameCode) (s : Cpu) := code.foldl (fun st p => p.1.eval p.2 st) s

def moveEvents : FrameCode → Cpu → List Event
  | [], _ => []
  | (move,len)::rest, s =>
    let accesses := match move with
      | .load _ src disp => [⟨false,s.regs.get src+disp,8⟩]
      | .store disp _ | .constant disp _ => [⟨true,s.regs.get .rsp+BitVec.ofNat 64 disp,8⟩]
      | .lea .. | .relative .. => []
    (s.rip,⟨move.op,len⟩,accesses) :: moveEvents rest (move.eval len s)

private theorem move_events (code : FrameCode) (s : Cpu) (live : s.ms = none) :
    observeCode (moveInstructions code) s = moveEvents code s := by
  induction code generalizing s with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨m,len⟩ := head
    have next : (m.eval len s).ms = none := by cases m <;> exact live
    have codeEq : moveInstructions ((m,len)::rest) = ⟨m.op,len⟩ :: moveInstructions rest := rfl
    simp only [codeEq, observeCode, moveEvents, move_step _ _ _ live, ih _ next]
    cases m <;> simp [FrameMove.op,dataAccesses,operandAccess,Ea.addr,Ea.offset,Size.bytes]

theorem moves_observed {base s out off} (code : FrameCode) (live : s.ms = none)
    (run : steps base code.length s = some out) (pc : s.rip = base + BitVec.ofNat 64 off)
    (decoded : decodeSeq off code.length = some (moveInstructions code))
    (straight : (moveInstructions code).dropLast.all linear = true) :
    ObservedExecution base s (moveEvents code s) out := by
  have actual := steps_observe_linear (code := moveInstructions code)
    (by simpa [moveInstructions] using run) pc (by simpa [moveInstructions] using decoded) straight
  rwa [move_events _ _ live] at actual

def FrameMove.wellPlaced (m : FrameMove) (bound : Nat) : Prop :=
  match m with
  | .load dst .. | .lea dst .. | .relative dst .. => dst ≠ .rsp
  | .store d .. | .constant d .. => d + 8 ≤ bound

instance (m : FrameMove) (bound : Nat) : Decidable (m.wellPlaced bound) := by
  cases m <;> unfold FrameMove.wellPlaced <;> infer_instance

private theorem move_frame (m : FrameMove) (n : Nat) (s : Cpu) (bound : Nat) (limit : m.wellPlaced bound) :
    let out := m.eval n s
    out.rip = s.rip+BitVec.ofNat 64 n ∧ out.ms = s.ms ∧ out.regs.get .rsp = s.regs.get .rsp ∧
      ∀ p, bound ≤ (p-s.regs.get .rsp).toNat → out.mem.read p = s.mem.read p := by
  cases m <;> first
    | exact ⟨rfl,rfl,Regs.get_set_ne _ _ _ _ limit,fun _ _ => rfl⟩
    | exact ⟨rfl,rfl,rfl,fun p hp => counter_frame _ _ _ _
        (Crypto.ARM64.Imported.region_store_delta _ _ _ bound 8 limit hp)⟩

/-- Every fetch in a sequence of frame moves uses bytes in the live memory,
including fetches after stores. The bound covers all its stack writes. -/
theorem moves_loaded (base : Val) (code : FrameCode) (off bound : Nat) (s : Cpu)
    (live : s.ms = none) (pc : s.rip = base+BitVec.ofNat 64 off) (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → bound ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (wf : ∀ p ∈ code, p.1.wellPlaced bound)
    (decode : decodeSeq off code.length = some (moveInstructions code)) :
    steps base code.length s = some (moveRun code s) := by
  induction code generalizing off s with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m,n⟩ := hd
    simp only [List.length_cons, decodeSeq] at decode
    cases h : decodeAt image off with
    | none => simp [h] at decode
    | some i =>
      by_cases extent : off < codeEnd ∧ off+i.len ≤ codeEnd
      · cases more : decodeSeq (off+i.len) tl.length with
        | none => simp [h, guard, extent, more] at decode
        | some rest =>
          simp [h, guard, extent, more, moveInstructions] at decode
          obtain ⟨rfl, restEq⟩ := decode
          have first := one_at base s off _ live loaded pc h extent.1 extent.2 (by cases m <;> rfl)
          rw [move_step _ _ _ live] at first
          obtain ⟨rip, ok, rsp, frame⟩ := move_frame m n s bound (wf (m,n) (by simp))
          have tail := ih (off+n) (m.eval n s) (ok.trans live)
            (rip.trans (by rw [pc, BitVec.ofNat_add, BitVec.add_assoc]))
            (fun j hj => (frame _ (sep j hj)).trans (loaded j hj))
            (by simpa only [rsp] using sep) (fun p hp => wf p (by simp [hp])) (more.trans (congrArg some restEq))
          simpa [Nat.add_comm 1 tl.length, moveRun] using steps_append first tail
      · simp [h, guard, extent] at decode

end Crypto.X86_64
