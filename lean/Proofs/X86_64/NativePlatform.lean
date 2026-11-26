import Proofs.X86_64.NativeScheduled

namespace Crypto.X86_64
open X86 Crypto.Baseline

inductive TargetOS
  | linux | macos | windows

/-- Primitive correspondence for the selected operating system and loaded
artifact. It includes context restoration across a scheduler boundary and
framing of state outside the scalar ISA model. The deployment must establish
these laws for its loader, exception policy, unwind registration and CPU. -/
structure PlatformModel (Hardware Opaque : Type) {scope : BorrowScope}
    (base : Val) (env : Environment scope) where
  target : TargetOS
  project : Hardware → Cpu
  abi : Hardware → Opaque
  resume : Nat → Hardware → Hardware → Prop
  execute : Hardware → Event → Hardware → Prop
  resume_agrees : ∀ tick before after, resume tick before after →
    project after = {project before with mem := env.memory tick (project before)} ∧
      abi after = abi before
  resume_exists : ∀ tick before, ∃ after, resume tick before after
  step_agrees : ∀ before after e, execute before e after →
    e.1 = (project before).rip ∧
    fetch base (project before) = some e.2.1 ∧
    dataAccesses e.2.1 (project before) = some e.2.2 ∧
    stepLoaded base (project before) = some (project after) ∧ abi after = abi before
  step_exists : ∀ before i access after, fetch base (project before) = some i →
    dataAccesses i (project before) = some access →
    stepLoaded base (project before) = some after →
    CallAccess scope (ReportedAccess (project before).rip i access) →
    ∃ result, execute before ((project before).rip,i,access) result

inductive NativeExecution {Hardware Opaque : Type} {scope : BorrowScope} {base : Val}
    {env : Environment scope} (platform : PlatformModel Hardware Opaque base env) :
    Nat → Hardware → List Event → Hardware → Prop where
  | nil (tick before) : NativeExecution platform tick before [] before
  | cons {tick before resumed next out event rest}
      (resume : platform.resume tick before resumed)
      (instruction : platform.execute resumed event next)
      (tail : NativeExecution platform (tick+1) next rest out) :
      NativeExecution platform tick before (event::rest) out

/-- Realize the already proved scheduled execution under primitive target
correspondence. Opaque current-thread ABI state is preserved through all
resumptions and retired instructions. -/
theorem ScheduledExecution.realize {Hardware Opaque : Type} {scope base} {env : Environment scope}
    (platform : PlatformModel Hardware Opaque base env)
    {tick logical trace out} (run : ScheduledExecution base env tick logical trace out)
    (hardware : Hardware) (start : platform.project hardware = logical)
    (allowed : ∀ e ∈ trace, CallAccess scope (ReportedAccess e.1 e.2.1 e.2.2)) :
    ∃ final, NativeExecution platform tick hardware trace final ∧
      platform.project final = out ∧ platform.abi final = platform.abi hardware := by
  induction run generalizing hardware with
  | nil => exact ⟨hardware,.nil _ _,start,rfl⟩
  | @cons tick s next out i access tail fetched executed observed frame race rest ih =>
    obtain ⟨resumed, resumedRun⟩ := platform.resume_exists tick hardware
    obtain ⟨projection,opaqueFrame⟩ := platform.resume_agrees tick hardware resumed resumedRun
    rw [start] at projection
    obtain ⟨advanced, action⟩ := platform.step_exists resumed i access next
      (by rw [projection]; exact fetched) (by rw [projection]; exact observed)
      (by rw [projection]; exact executed) (by rw [projection]; exact allowed _ List.mem_cons_self)
    have actual := platform.step_agrees _ _ _ action
    have same : platform.project advanced = next :=
      Option.some.inj (actual.2.2.2.1.symm.trans (by rw [projection]; exact executed))
    obtain ⟨final,tailRun,endState,preserve⟩ := ih advanced same (fun e h => allowed e (List.mem_cons_of_mem _ h))
    have pc : (platform.project resumed).rip = s.rip := by rw [projection]
    rw [pc] at action
    exact ⟨final,.cons resumedRun action tailRun,endState,preserve.trans (actual.2.2.2.2.trans opaqueFrame)⟩

theorem sha256_native_platform {Hardware Opaque : Type} {base s message extent authority}
    (entry : PermissionEntry base s message extent authority)
    (env : Environment (callBorrow base s extent)) (platform : PlatformModel Hardware Opaque base env)
    (hardware : Hardware) (start : platform.project hardware = s) :
    ∃ out physical, ScheduledResult base s out message extent authority env (callEvents base s message) ∧
      NativeExecution platform 0 hardware (callEvents base s message) physical ∧
      platform.project physical = out ∧ platform.abi physical = platform.abi hardware := by
  obtain ⟨out,call⟩ := sha256_scheduled entry env
  obtain ⟨physical,run,project,abi⟩ := call.execution.realize platform hardware start call.owned
  exact ⟨out,physical,call,run,project,abi⟩

end Crypto.X86_64
