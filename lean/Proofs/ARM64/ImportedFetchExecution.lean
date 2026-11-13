import Proofs.ARM64.ImportedFetchMemory

/-!
Running-state and PC rules for the instruction families used by SHA-256.
A fault cannot recover to Running; successful sequential instructions advance
PC by four bytes. A separately supplied StaticPath plus the recorded-word
result lifts to actual imported Steps through loaded memory.
-/
namespace Crypto.ARM64.Imported

@[simp] theorem status_set_pc (s : Arm64.State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by cases s; rfl
@[simp] theorem status_set_pstate (s : Arm64.State) (p : Arm64.PState) : (s.setPState p).status = s.status := by cases s; rfl
@[simp] theorem status_set_status (s : Arm64.State) (status : Arm64.ExecStatus) : (s.setStatus status).status = status := by cases s; rfl
@[simp] theorem status_write_reg64 (s : Arm64.State) (r : Arm64.Reg) (v : BitVec 64) :
    (s.writeReg64 r v).status = s.status := by cases s; cases r <;> rfl
@[simp] theorem status_write_reg (s : Arm64.State) (w : Arm64.RegWidth) (r : Arm64.Reg) (v : BitVec 64) :
    (s.writeReg w r v).status = s.status := by cases w <;> simp [Arm64.State.writeReg]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem permitted_running_before (instruction : Arm64.Instr)
    (allowed : permittedInstruction instruction = true) (s : Arm64.State)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running) :
    s.status = .Running := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at allowed
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr,
    Arm64.execLdp, Arm64.execStp, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1] at running
  all_goals repeat' split at running
  all_goals try simp only [status_advance, status_set_pc, status_set_mem, status_set_pstate,
    status_set_status, status_write_reg64, status_write_reg] at running
  all_goals first | exact running | cases running

@[simp] theorem pc_write_reg64 (s : Arm64.State) (r : Arm64.Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pc = s.pc := by cases s; cases r <;> rfl
@[simp] theorem pc_write_reg (s : Arm64.State) (w : Arm64.RegWidth) (r : Arm64.Reg) (v : BitVec 64) :
    (s.writeReg w r v).pc = s.pc := by cases w <;> simp [Arm64.State.writeReg]
@[simp] theorem pc_set_status (s : Arm64.State) (status : Arm64.ExecStatus) :
    (s.setStatus status).pc = s.pc := by cases s; rfl

def sequentialInstruction : Arm64.Instr → Bool
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield ..
  | .extr .. | .logicalShift .. | .addSubShift .. | .addSubExt ..
  | .dataProc1 .. | .ldr .. | .str .. | .ldp .. | .stp .. => true
  | _ => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem sequential_pc (instruction : Arm64.Instr)
    (sequential : sequentialInstruction instruction = true) (s : Arm64.State)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc = s.pc + 4#64 := by
  cases instruction <;> simp only [sequentialInstruction, Bool.false_eq_true] at sequential
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr,
    Arm64.execLdp, Arm64.execStp, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1] at running ⊢
  all_goals repeat' split at running
  all_goals try simp only [status_advance, status_set_mem, status_set_pstate,
    status_set_status, status_write_reg64, status_write_reg] at running
  all_goals first | contradiction | skip
  all_goals simp_all

theorem sequential_permitted (instruction : Arm64.Instr)
    (sequential : sequentialInstruction instruction = true) : permittedInstruction instruction = true := by
  cases instruction <;> simp_all [sequentialInstruction, permittedInstruction]

theorem runWords_running_before (words : List (BitVec 32)) (s out : Arm64.State)
    (permitted : PermittedWords words) (executed : runWords words s = some out)
    (running : out.status = .Running) : s.status = .Running := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact running
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have next := ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) permitted.tail executed
      exact permitted_running_before instruction (permitted word (by simp) instruction decoded) s next

def StaticPath (base : BitVec 64) : List (BitVec 32) → Arm64.State → Prop
  | [], _ => True
  | word :: rest, s => match Arm64.decode word with
    | none => False
    | some instruction => (program base).fetch s.pc = some instruction ∧
        StaticPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

theorem staticPath_steps (base : BitVec 64) (words : List (BitVec 32)) (s out : Arm64.State)
    (permitted : PermittedWords words) (loaded : (program base).CodeLoaded s.mem)
    (executed : runWords words s = some out) (path : StaticPath base words s)
    (running : out.status = .Running) : Arm64.Steps (program base) s out := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact Arm64.Steps.refl _
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have allowed := permitted word (by simp) instruction decoded
      have nextRunning := runWords_running_before rest _ out permitted.tail executed running
      have beforeRunning := permitted_running_before instruction allowed s nextRunning
      have parts : (program base).fetch s.pc = some instruction ∧
          StaticPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [StaticPath, decoded] using path
      exact Arm64.Steps.step (recorded_step loaded parts.1 beforeRunning allowed)
        (ih _ permitted.tail (permitted_codeLoaded instruction allowed s loaded) executed parts.2)

end Crypto.ARM64.Imported
