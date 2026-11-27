import Proofs.HMACSHA256.ARM64Ranges
import Proofs.ARM64.ImportedTraceRelation

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private def fixedFlow (i : Arm64.Instr) : Bool :=
  match i with
  | .b _ | .bl _ => true
  | .dataProc3 _ _ dst .. => decide (dst ≠ .sp)
  | _ => sequentialInstruction i && stackPreservingInstruction i

private def registerDependencies (i : Arm64.Instr) : Arm64.Reg → Option (List Arm64.Reg)
  | .sp => some [.sp]
  | .xzr => some []
  | .gpr r =>
    match i with
    | .bl _ => some (if r = 30#5 then [] else [.gpr r])
    | .dataProc3 _ _ dst rn rm ra => some (if dst = .gpr r then [rn, rm, ra] else [.gpr r])
    | _ => resultSources i r

private def instructionDependencies (i : Arm64.Instr) (after : List Arm64.Reg) : Option (List Arm64.Reg) := do
  if fixedFlow i && hmacLocal i then
    let registers ← after.mapM (registerDependencies i)
    return accessRegisters i ++ registers.flatten
  else none

/-- Public register values sufficient for the observations of a fixed decoded
fragment and the selected register values at its exit. Loaded values are
unknown unless they are outside the selected dependency closure. -/
def straightDependencies : List Arm64.Instr → List Arm64.Reg → Option (List Arm64.Reg)
  | [], after => some after
  | i :: rest, after => do
    let live ← straightDependencies rest after
    instructionDependencies i live

private theorem agree_subset {a b : List Arm64.Reg} {s t : Arm64.State}
    (agree : RegistersAgree b s t) (subset : ∀ r ∈ a, r ∈ b) : RegistersAgree a s t :=
  fun r hit => agree r (subset r hit)

private theorem dependencies_member {i : Arm64.Instr} {out : List Arm64.Reg}
    {deps : List (List Arm64.Reg)} (walk : out.mapM (registerDependencies i) = some deps)
    {r : Arm64.Reg} (hit : r ∈ out) :
    ∃ sources ∈ deps, registerDependencies i r = some sources := by
  induction out generalizing deps with
  | nil => simp at hit
  | cons x xs ih =>
    simp only [List.mapM_cons] at walk
    cases first : registerDependencies i x with
    | none => simp [first] at walk
    | some before =>
      cases tail : xs.mapM (registerDependencies i) with
      | none => simp [first, tail] at walk
      | some remaining =>
        rw [first, tail] at walk
        change some (before :: remaining) = some deps at walk
        cases walk
        rcases List.mem_cons.mp hit with rfl | later
        · exact ⟨before, List.mem_cons_self, first⟩
        · obtain ⟨sources, member, eq⟩ := ih tail later
          exact ⟨sources, List.mem_cons_of_mem _ member, eq⟩

private theorem fixed_control (i : Arm64.Instr) (s t : Arm64.State)
    (fixed : fixedFlow i = true) (pc : s.pc = t.pc) (sp : s.sp = t.sp)
    (runs : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running)
    (runt : (Arm64.execInstWithSvc Arm64.noSyscalls i t).status = .Running) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).pc = (Arm64.execInstWithSvc Arm64.noSyscalls i t).pc ∧
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).sp = s.sp ∧
    (Arm64.execInstWithSvc Arm64.noSyscalls i t).sp = t.sp := by
  cases i
  case b offset => exact ⟨congrArg (· + offset) pc, rfl, rfl⟩
  case bl offset => exact ⟨congrArg (· + offset) pc, rfl, rfl⟩
  case dataProc3 w op dst rn rm ra =>
    have away : dst ≠ .sp := of_decide_eq_true fixed
    cases w <;> simp [Arm64.execInstWithSvc, Arm64.execDataProc3, Arm64.State.writeReg,
      Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.State.setPC, away, pc]
  all_goals
    simp only [fixedFlow, Bool.and_eq_true] at fixed
    exact ⟨(sequential_pc _ fixed.1 s runs).trans
      ((congrArg (· + 4#64) pc).trans (sequential_pc _ fixed.1 t runt).symm),
      stack_preserving_sp _ s fixed.2, stack_preserving_sp _ t fixed.2⟩

set_option linter.unusedVariables false in
private theorem register_agrees_after (i : Arm64.Instr) (r : Arm64.Reg) (sources : List Arm64.Reg)
    (s t : Arm64.State) (pc : s.pc = t.pc)
    (nextSP : (Arm64.execInstWithSvc Arm64.noSyscalls i s).sp =
      (Arm64.execInstWithSvc Arm64.noSyscalls i t).sp)
    (deps : registerDependencies i r = some sources) (agree : RegistersAgree sources s t) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).readReg64 r =
      (Arm64.execInstWithSvc Arm64.noSyscalls i t).readReg64 r := by
  cases r with
  | sp => exact nextSP
  | xzr => rfl
  | gpr r =>
    by_cases zero : r = 31#5
    · subst r; rfl
    cases i
    case neg.bl offset =>
      by_cases isLink : r = 30#5
      · subst r
        simp only [Arm64.execInstWithSvc, trace_read_reg_set_pc, Arm64.Reg.lr,
          trace_read_write_reg64 _ _ _ _ (by decide : 30#5 ≠ 31#5), if_true, pc]
      · simp only [registerDependencies, if_neg isLink, Option.some.injEq] at deps
        subst sources
        have same := agree (.gpr r) (by simp)
        have away : (Arm64.Reg.gpr 30#5) ≠ .gpr r := fun h => isLink (Arm64.Reg.gpr.inj h).symm
        simpa only [Arm64.execInstWithSvc, trace_read_reg_set_pc, Arm64.Reg.lr,
          trace_read_write_reg64 _ _ _ _ zero, if_neg away] using same
    case neg.dataProc3 w op dst rn rm ra =>
      by_cases changes : dst = .gpr r
      · simp only [registerDependencies, if_pos changes, Option.some.injEq] at deps
        subst sources
        have n := agree rn (by simp)
        have m := agree rm (by simp)
        have a := agree ra (by simp)
        simp only [Arm64.execInstWithSvc, Arm64.execDataProc3, trace_read_reg_advance,
          trace_read_write_reg _ _ _ _ _ zero, if_pos changes, Arm64.State.readReg32, n, m, a]
      · simp only [registerDependencies, if_neg changes, Option.some.injEq] at deps
        subst sources
        have same := agree (.gpr r) (by simp)
        simpa only [Arm64.execInstWithSvc, Arm64.execDataProc3, trace_read_reg_advance,
          trace_read_write_reg _ _ _ _ _ zero, if_neg changes] using same
    all_goals
      apply result_sources_sound _ r s t pc
      simp only [registerDependencies] at deps
      unfold ResultInputsAgree
      rw [deps]
      exact agree

private theorem fixed_steps_running_before (code : List Arm64.Instr) (need live : List Arm64.Reg)
    (check : straightDependencies code live = some need) (s : Arm64.State)
    (running : (runDecoded code s).status = .Running) : s.status = .Running := by
  induction code generalizing s need with
  | nil => exact running
  | cons i tail ih =>
    change (straightDependencies tail live >>= instructionDependencies i) = some need at check
    cases found : straightDependencies tail live with
    | none => simp [found] at check
    | some mid =>
      rw [found] at check
      change instructionDependencies i mid = some need at check
      unfold instructionDependencies at check
      split at check
      next both =>
        simp only [Bool.and_eq_true] at both
        exact local_running_before i s both.2
          (ih mid found (Arm64.execInstWithSvc Arm64.noSyscalls i s) running)
      next => simp at check

set_option maxHeartbeats 3400000 in
private theorem decoded_straight_agree (code : List Arm64.Instr) (need live : List Arm64.Reg)
    (check : straightDependencies code live = some need) (s t : Arm64.State)
    (pc : s.pc = t.pc) (sp : s.sp = t.sp) (inputs : RegistersAgree need s t)
    (runs : (runDecoded code s).status = .Running) (runt : (runDecoded code t).status = .Running) :
    decodedEvents code s = decodedEvents code t ∧
    RegistersAgree live (runDecoded code s) (runDecoded code t) := by
  induction code generalizing s t need with
  | nil =>
    have eq : live = need := Option.some.inj check
    subst need
    exact ⟨rfl, inputs⟩
  | cons i tail ih =>
    change (straightDependencies tail live >>= instructionDependencies i) = some need at check
    cases found : straightDependencies tail live with
    | none => simp [found] at check
    | some mid =>
      rw [found] at check
      change instructionDependencies i mid = some need at check
      unfold instructionDependencies at check
      split at check
      next enabled =>
        simp only [Bool.and_eq_true] at enabled
        have fixed := enabled.1
        cases src : mid.mapM (registerDependencies i) with
        | none => simp [src] at check
        | some deps =>
          rw [src] at check
          change some (accessRegisters i ++ deps.flatten) = some need at check
          cases check
          let s' := Arm64.execInstWithSvc Arm64.noSyscalls i s
          let t' := Arm64.execInstWithSvc Arm64.noSyscalls i t
          obtain ⟨pc', a, b⟩ := fixed_control i s t fixed pc sp
            (fixed_steps_running_before tail mid live found s' runs)
            (fixed_steps_running_before tail mid live found t' runt)
          have sp' := a.trans (sp.trans b.symm)
          have regs : RegistersAgree mid s' t' := by
            intro r hit
            obtain ⟨sources, present, dependency⟩ := dependencies_member src hit
            exact register_agrees_after i r sources s t pc sp' dependency
              (agree_subset inputs (fun x hx => List.mem_append_right _ (List.mem_flatten.mpr ⟨sources, present, hx⟩)))
          have addresses : RegistersAgree (accessRegisters i) s t :=
            agree_subset inputs (fun _ h => List.mem_append_left _ h)
          have here : instructionObservation i s = instructionObservation i t := by
            simp only [instructionObservation, InstructionObservation.mk.injEq]
            exact ⟨pc, pc', sp, sp', dataAccesses_eq_of_registers i s t addresses⟩
          obtain ⟨rest, afterwards⟩ := ih mid found s' t' pc' sp' regs runs runt
          exact ⟨congrArg₂ List.cons here rest, afterwards⟩
      next => simp at check

theorem range_straight_agree {routine : Routine} {offset count : Nat}
    {s t outS outT : Arm64.State} {need live : List Arm64.Reg}
    (check : ((decodeRange routine offset count).bind (straightDependencies · live)) = some need)
    (left : runRange routine offset count s = some outS)
    (right : runRange routine offset count t = some outT)
    (runs : outS.status = .Running) (runt : outT.status = .Running)
    (pc : s.pc = t.pc) (sp : s.sp = t.sp) (inputs : RegistersAgree need s t) :
    rangeEvents routine offset count s = rangeEvents routine offset count t ∧ RegistersAgree live outS outT := by
  cases code : decodeRange routine offset count with
  | none => simp [code] at check
  | some instructions =>
    rw [code] at check
    change straightDependencies instructions live = some need at check
    have a : runDecoded instructions s = outS := by
      simpa only [runRange, code, Option.map_some, Option.some.injEq] using left
    have b : runDecoded instructions t = outT := by
      simpa only [runRange, code, Option.map_some, Option.some.injEq] using right
    simpa only [rangeEvents, code, Option.getD_some, a, b] using
      decoded_straight_agree instructions need live check s t pc sp inputs (a ▸ runs) (b ▸ runt)

private def registerIncluded (r : Arm64.Reg) : List Arm64.Reg → Bool
  | [] => false
  | head :: tail => decide (r = head) || registerIncluded r tail

private theorem register_included {r : Arm64.Reg} {registers : List Arm64.Reg} :
    registerIncluded r registers = true ↔ r ∈ registers := by
  induction registers with
  | nil => simp [registerIncluded]
  | cons head tail ih => simp only [registerIncluded, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]

def rangeDependenciesWithin (routine : Routine) (offset count : Nat) (before after : List Arm64.Reg) : Bool :=
  (((decodeRange routine offset count).bind (straightDependencies · after)).map
    (·.all (fun r => registerIncluded r before))).getD false

theorem range_agree_on {routine : Routine} {offset count : Nat}
    {s t outS outT : Arm64.State} {before after : List Arm64.Reg}
    (check : rangeDependenciesWithin routine offset count before after = true)
    (left : runRange routine offset count s = some outS)
    (right : runRange routine offset count t = some outT)
    (runs : outS.status = .Running) (runt : outT.status = .Running)
    (pc : s.pc = t.pc) (sp : s.sp = t.sp) (inputs : RegistersAgree before s t) :
    rangeEvents routine offset count s = rangeEvents routine offset count t ∧ RegistersAgree after outS outT := by
  unfold rangeDependenciesWithin at check
  cases closure : (decodeRange routine offset count).bind (straightDependencies · after) with
  | none => simp [closure] at check
  | some need =>
    simp only [closure, Option.map_some, Option.getD_some, List.all_eq_true, register_included] at check
    exact range_straight_agree closure left right runs runt pc sp (agree_subset inputs check)

end Crypto.HMACSHA256.ARM64
