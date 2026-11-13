import Proofs.ARM64.ImportedStackBound
import Proofs.ARM64.ImportedTraceMasks
import Proofs.ARM64.ImportedLabeledCode

/-!
Semantic paired-instruction observations for the concrete SHA-256 vocabulary.
Effective addresses use only declared address registers; branch observations
use only the tested public register or flags. Successful load/store guards are
derived elsewhere from the complete call, rather than added to caller entry.
A closed certificate checks that the candidate point masks include every
observation source for all151 image instructions. Semantic operand-dependency
rules and closed certificates establish next-mask preservation for every
post-header CFG edge, including the final return. Header load agreement,
complete paired trace equality, disclosure policy, physical timing and the
independently pinned architecture baseline remain separate obligations.
-/

namespace Crypto.ARM64.Imported

def RegistersAgree (registers : List Arm64.Reg) (left right : Arm64.State) : Prop :=
  ∀ reg ∈ registers, left.readReg64 reg = right.readReg64 reg

def addressRegisters : Arm64.AddrMode → List Arm64.Reg
  | .Offset base _ | .UnscaledOffset base _ | .PreIndex base _ | .PostIndex base _ => [base]
  | .RegOffset base index _ _ => [base, index]

theorem address_registers_agree (addr : Arm64.AddrMode) (left right : Arm64.State)
    (agree : RegistersAgree (addressRegisters addr) left right) :
    Arm64.evalAddrMode left addr = Arm64.evalAddrMode right addr := by
  cases addr with
  | Offset base off => simp only [Arm64.evalAddrMode]; rw [agree base (by simp [addressRegisters])]
  | UnscaledOffset base off => simp only [Arm64.evalAddrMode]; rw [agree base (by simp [addressRegisters])]
  | PreIndex base off => simp only [Arm64.evalAddrMode]; rw [agree base (by simp [addressRegisters])]
  | PostIndex base off => simp only [Arm64.evalAddrMode]; rw [agree base (by simp [addressRegisters])]
  | RegOffset base index ext amount =>
    simp only [Arm64.evalAddrMode]
    rw [agree base (by simp [addressRegisters]), agree index (by simp [addressRegisters])]

def accessRegisters : Arm64.Instr → List Arm64.Reg
  | .ldr _ _ _ _ addr | .str _ _ addr | .ldp _ _ _ _ addr | .stp _ _ _ addr => addressRegisters addr
  | _ => []

theorem dataAccesses_eq_of_registers (instruction : Arm64.Instr) (left right : Arm64.State)
    (agree : RegistersAgree (accessRegisters instruction) left right) :
    dataAccesses instruction left = dataAccesses instruction right := by
  cases instruction <;> try rfl
  all_goals simp only [accessRegisters] at agree
  all_goals simp only [dataAccesses, address_registers_agree _ left right agree]

def noWritebackAddress : Arm64.AddrMode → Bool
  | .Offset .. | .UnscaledOffset .. | .RegOffset .. => true
  | _ => false

def memoryObservationForm : Arm64.Instr → Bool
  | .ldr _ _ _ rt addr => decide (rt ≠ .sp) && noWritebackAddress addr
  | .str _ _ addr => noWritebackAddress addr
  | .ldp _ _ rt rt2 addr => decide (rt ≠ .sp) && decide (rt2 ≠ .sp) && noWritebackAddress addr
  | .stp _ _ _ addr => noWritebackAddress addr
  | _ => false

theorem memory_observation_stack_preserving (instruction : Arm64.Instr)
    (form : memoryObservationForm instruction = true) : stackPreservingInstruction instruction = true := by
  cases instruction <;> simp only [memoryObservationForm, stackPreservingInstruction,
    Bool.false_eq_true] at form ⊢
  all_goals simpa only [noWritebackAddress, stackNoWriteback] using form

theorem memory_observation_sp (instruction : Arm64.Instr) (s : Arm64.State)
    (form : memoryObservationForm instruction = true) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).sp = s.sp :=
  stack_preserving_sp instruction s (memory_observation_stack_preserving instruction form)

theorem memory_observation_sequential (instruction : Arm64.Instr)
    (form : memoryObservationForm instruction = true) : sequentialInstruction instruction = true := by
  cases instruction <;> simp_all [memoryObservationForm, sequentialInstruction]

theorem memory_observation_eq (instruction : Arm64.Instr) (left right : Arm64.State)
    (form : memoryObservationForm instruction = true)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (addresses : RegistersAgree (accessRegisters instruction) left right)
    (leftRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running)
    (rightRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running) :
    instructionObservation instruction left = instructionObservation instruction right := by
  have nextPC := (sequential_pc instruction (memory_observation_sequential instruction form) left leftRunning).trans
    ((congrArg (fun x : BitVec 64 => x + 4#64) pc).trans
      (sequential_pc instruction (memory_observation_sequential instruction form) right rightRunning).symm)
  have nextSP := (memory_observation_sp instruction left form).trans
    (sp.trans (memory_observation_sp instruction right form).symm)
  simp only [instructionObservation, InstructionObservation.mk.injEq]
  exact ⟨pc, nextPC, sp, nextSP, dataAccesses_eq_of_registers instruction left right addresses⟩

def controlObservationForm : Arm64.Instr → Bool
  | .b .. | .bCond .. | .cbz .. | .ret .. => true
  | _ => false

def ControlAgree (instruction : Arm64.Instr) (left right : Arm64.State) : Prop :=
  match instruction with
  | .bCond .. => left.pstate = right.pstate
  | .cbz _ _ reg _ | .ret reg => left.readReg64 reg = right.readReg64 reg
  | _ => True

theorem trace_read_reg_width (left right : Arm64.State) (w : Arm64.Width) (reg : Arm64.Reg)
    (equal : left.readReg64 reg = right.readReg64 reg) : left.readReg w reg = right.readReg w reg := by
  cases w <;> simp [Arm64.State.readReg, Arm64.State.readReg32, equal]

set_option maxRecDepth 16384 in
theorem control_observation_eq (instruction : Arm64.Instr) (left right : Arm64.State)
    (form : controlObservationForm instruction = true)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (agree : ControlAgree instruction left right) :
    instructionObservation instruction left = instructionObservation instruction right := by
  cases instruction <;> simp only [controlObservationForm, Bool.false_eq_true] at form
  case b offset =>
    simp [instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.State.setPC, pc, sp]
  case bCond condition offset =>
    change left.pstate = right.pstate at agree
    by_cases taken : Arm64.ConditionHolds condition right.pstate = true
    all_goals simp [instructionObservation, dataAccesses, Arm64.execInstWithSvc,
      Arm64.State.setPC, Arm64.State.advancePC, agree, pc, sp, taken]
  case ret reg =>
    change left.readReg64 reg = right.readReg64 reg at agree
    simp [instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.State.setPC, agree, pc, sp]
  case cbz w nonzero reg offset =>
    change left.readReg64 reg = right.readReg64 reg at agree
    have value := trace_read_reg_width left right w reg agree
    cases nonzero <;> by_cases zero : right.readReg w reg = 0#64
    all_goals simp [instructionObservation, dataAccesses, Arm64.execInstWithSvc,
      Arm64.State.setPC, Arm64.State.advancePC, value, pc, sp, zero]


theorem sequential_observation_eq (instruction : Arm64.Instr) (left right : Arm64.State)
    (sequential : sequentialInstruction instruction = true)
    (preservesSP : stackPreservingInstruction instruction = true)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (addresses : RegistersAgree (accessRegisters instruction) left right)
    (leftRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running)
    (rightRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running) :
    instructionObservation instruction left = instructionObservation instruction right := by
  have nextPC := (sequential_pc instruction sequential left leftRunning).trans
    ((congrArg (fun x : BitVec 64 => x + 4#64) pc).trans
      (sequential_pc instruction sequential right rightRunning).symm)
  have nextSP := (stack_preserving_sp instruction left preservesSP).trans
    (sp.trans (stack_preserving_sp instruction right preservesSP).symm)
  simp only [instructionObservation, InstructionObservation.mk.injEq]
  exact ⟨pc, nextPC, sp, nextSP, dataAccesses_eq_of_registers instruction left right addresses⟩

theorem sp_immediate_observation_eq (op : Arm64.AddSubOp) (imm : BitVec 12) (shift : Bool)
    (left right : Arm64.State) (pc : left.pc = right.pc) (sp : left.sp = right.sp) :
    instructionObservation (.addSubImm .W64 op .sp .sp imm shift) left =
      instructionObservation (.addSubImm .W64 op .sp .sp imm shift) right := by
  cases op <;>
    simp [instructionObservation, dataAccesses, Arm64.execInstWithSvc, Arm64.execAddSubImm,
      Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.readReg64,
      Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC,
      Arm64.State.setPState, pc, sp]

def ordinaryObservationForm (instruction : Arm64.Instr) : Bool :=
  controlObservationForm instruction || (sequentialInstruction instruction && stackPreservingInstruction instruction)

/-- Sound semantic observation rule. Its premises identify the actual source
register agreements; equal code words alone do not establish these facts. -/
theorem ordinary_observation_eq (instruction : Arm64.Instr) (left right : Arm64.State)
    (form : ordinaryObservationForm instruction = true)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (addresses : RegistersAgree (accessRegisters instruction) left right)
    (control : ControlAgree instruction left right)
    (leftRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running)
    (rightRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running) :
    instructionObservation instruction left = instructionObservation instruction right := by
  have branches : controlObservationForm instruction = true ∨
      (sequentialInstruction instruction = true ∧ stackPreservingInstruction instruction = true) := by
    simpa [ordinaryObservationForm] using form
  cases branches with
  | inl branch => exact control_observation_eq instruction left right branch pc sp control
  | inr parts =>
    exact sequential_observation_eq instruction left right parts.1 parts.2 pc sp addresses leftRunning rightRunning

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_observation_forms : ∀ i : Fin 151, i.val = 0 ∨ i.val = 149 ∨
    ((Arm64.decode imageWords[i.val]!).map ordinaryObservationForm).getD false = true := by
  decide +kernel

theorem image_allocation_decode :
    Arm64.decode imageWords[0]! = some (.addSubImm .W64 .SUB .sp .sp 416#12 false) := by decide +kernel

theorem image_restoration_decode :
    Arm64.decode imageWords[149]! = some (.addSubImm .W64 .ADD .sp .sp 416#12 false) := by decide +kernel


def controlInputsPublic (point : TracePoint) : Arm64.Instr → Bool
  | .bCond .. => flagsPublicAt point
  | .cbz _ _ reg _ | .ret reg => registerPublicAt point reg
  | _ => true

def observationInputsPublic (point : TracePoint) (instruction : Arm64.Instr) : Bool :=
  (accessRegisters instruction).all (registerPublicAt point) && controlInputsPublic point instruction

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_public_observation_inputs : ∀ i : Fin 151,
    ((Arm64.decode imageWords[i.val]!).map
      (observationInputsPublic (.instruction i))).getD false = true := by
  decide +kernel

theorem public_relation_access_registers (point : TracePoint) (instruction : Arm64.Instr)
    (left right : Arm64.State) (related : PublicRelation point left right)
    (isPublic : (accessRegisters instruction).all (registerPublicAt point) = true) :
    RegistersAgree (accessRegisters instruction) left right := by
  intro reg member
  exact related.read reg (List.all_eq_true.mp isPublic reg member)

theorem public_relation_control (point : TracePoint) (instruction : Arm64.Instr)
    (left right : Arm64.State) (related : PublicRelation point left right)
    (isPublic : controlInputsPublic point instruction = true) : ControlAgree instruction left right := by
  cases instruction <;> simp only [controlInputsPublic, ControlAgree] at isPublic ⊢
  all_goals first
    | exact True.intro
    | exact related.flags isPublic
    | exact related.read _ isPublic

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- Per-instruction paired observation theorem for every word of this SHA image.
The point is a supplied program label; proving its agreement with actual PCs
and preservation of the next label's relation remain separate obligations. -/
theorem image_public_observation_eq (i : Fin 151) (instruction : Arm64.Instr)
    (left right : Arm64.State)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction)
    (related : PublicRelation (.instruction i) left right)
    (leftRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running)
    (rightRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running) :
    instructionObservation instruction left = instructionObservation instruction right := by
  have isPublic : (accessRegisters instruction).all (registerPublicAt (.instruction i)) = true ∧
      controlInputsPublic (.instruction i) instruction = true := by
    have check := image_public_observation_inputs i
    simpa only [decoded, Option.map_some, Option.getD_some, observationInputsPublic, Bool.and_eq_true] using check
  have addresses := public_relation_access_registers (.instruction i) instruction left right related isPublic.1
  have control := public_relation_control (.instruction i) instruction left right related isPublic.2
  rcases image_observation_forms i with allocation | restoration | ordinary
  · have wordEq : imageWords[i.val]! = imageWords[0]! := by rw [allocation]
    have instructionEq : instruction = .addSubImm .W64 .SUB .sp .sp 416#12 false :=
      Option.some.inj (decoded.symm.trans (wordEq ▸ image_allocation_decode))
    subst instruction
    exact sp_immediate_observation_eq .SUB 416#12 false left right related.pc related.sp
  · have wordEq : imageWords[i.val]! = imageWords[149]! := by rw [restoration]
    have instructionEq : instruction = .addSubImm .W64 .ADD .sp .sp 416#12 false :=
      Option.some.inj (decoded.symm.trans (wordEq ▸ image_restoration_decode))
    subst instruction
    exact sp_immediate_observation_eq .ADD 416#12 false left right related.pc related.sp
  · have form : ordinaryObservationForm instruction = true := by
      simpa only [decoded, Option.map_some, Option.getD_some] using ordinary
    exact ordinary_observation_eq instruction left right form related.pc related.sp addresses control leftRunning rightRunning


theorem trace_read_write_reg64 (s : Arm64.State) (dst : Arm64.Reg) (value : BitVec 64)
    (reg : BitVec 5) (nonzero : reg ≠ 31#5) :
    (s.writeReg64 dst value).readReg64 (.gpr reg) =
      if dst = .gpr reg then value else s.readReg64 (.gpr reg) := by
  cases dst with
  | sp => simp [Arm64.State.writeReg64, Arm64.State.readReg64]
  | xzr => simp [Arm64.State.writeReg64, Arm64.State.readReg64]
  | gpr index =>
    by_cases same : index = reg
    · subst index
      simp [Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.read, Arm64.RegFile.write, nonzero]
    · by_cases zero : index = 31#5
      all_goals simp [Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.read,
        Arm64.RegFile.write, zero, same, Ne.symm same, nonzero, Ne.symm nonzero]

theorem trace_read_write_reg (s : Arm64.State) (w : Arm64.Width) (dst : Arm64.Reg) (value : BitVec 64)
    (reg : BitVec 5) (nonzero : reg ≠ 31#5) :
    (s.writeReg w dst value).readReg64 (.gpr reg) =
      if dst = .gpr reg then (match w with | .W32 => (value.truncate 32).zeroExtend 64 | .W64 => value)
      else s.readReg64 (.gpr reg) := by
  exact trace_read_write_reg64 s dst _ reg nonzero

@[simp] theorem trace_read_reg_set_mem (s : Arm64.State) (mem : Arm64.Memory) (reg : Arm64.Reg) :
    (s.setMem mem).readReg64 reg = s.readReg64 reg := by cases s; cases reg <;> rfl
@[simp] theorem trace_read_reg_set_status (s : Arm64.State) (status : Arm64.ExecStatus) (reg : Arm64.Reg) :
    (s.setStatus status).readReg64 reg = s.readReg64 reg := by cases s; cases reg <;> rfl
@[simp] theorem trace_read_reg_set_pstate (s : Arm64.State) (flags : Arm64.PState) (reg : Arm64.Reg) :
    (s.setPState flags).readReg64 reg = s.readReg64 reg := by cases s; cases reg <;> rfl
@[simp] theorem trace_read_reg_set_pc (s : Arm64.State) (pc : BitVec 64) (reg : Arm64.Reg) :
    (s.setPC pc).readReg64 reg = s.readReg64 reg := by cases s; cases reg <;> rfl
@[simp] theorem trace_read_reg_advance (s : Arm64.State) (reg : Arm64.Reg) :
    s.advancePC.readReg64 reg = s.readReg64 reg := by cases s; cases reg <;> rfl


@[simp] theorem trace_read_optional_flags (s : Arm64.State) (flags : Option Arm64.PState) (reg : Arm64.Reg) :
    (match flags with | some ps => s.setPState ps | none => s).readReg64 reg = s.readReg64 reg := by
  cases flags <;> rfl

@[simp] theorem trace_logical_ignore_old (w : Arm64.Width) (op : Arm64.LogicalOp)
    (x y : BitVec 64) (ps : Arm64.PState) :
    Arm64.evalLogical w op x y ps = Arm64.evalLogical w op x y Arm64.PState.zero := by rfl

@[simp] theorem trace_ubfm_ignore_old (w : Arm64.Width) (dst src : BitVec 64) (r m : Nat) :
    Arm64.evalBitfield w .UBFM dst src r m = Arm64.evalBitfield w .UBFM 0#64 src r m := by
  cases w <;> rfl

@[simp] theorem trace_sbfm_ignore_old (w : Arm64.Width) (dst src : BitVec 64) (r m : Nat) :
    Arm64.evalBitfield w .SBFM dst src r m = Arm64.evalBitfield w .SBFM 0#64 src r m := by
  cases w <;> rfl

/-- Sources of a queried GPR result. A load into that GPR is unknown; source
agreements are never a digest or execution conclusion. Unchanged GPRs depend
only on their own initial value. This covers the SHA instruction vocabulary. -/
def resultSources (instruction : Arm64.Instr) (reg : BitVec 5) : Option (List Arm64.Reg) :=
  if reg == 31#5 then some [] else
  let unchanged := some [.gpr reg]
  match instruction with
  | .adr _ dst _ => if dst = .gpr reg then some [] else unchanged
  | .addSubImm _ _ dst rn _ _ | .logicalImm _ _ dst rn _ | .dataProc1 _ _ dst rn =>
      if dst = .gpr reg then some [rn] else unchanged
  | .addSubShift _ _ dst rn rm _ _ | .addSubExt _ _ dst rn rm _ _
  | .logicalShift _ _ dst rn rm _ _ | .extr _ dst rn rm _ =>
      if dst = .gpr reg then some [rn, rm] else unchanged
  | .moveWide _ op dst _ _ =>
      if dst = .gpr reg then some (if op = .MOVK then [dst] else []) else unchanged
  | .bitfield _ op dst rn _ _ =>
      if dst = .gpr reg then some (if op = .BFM then [rn, dst] else [rn]) else unchanged
  | .ldr _ _ _ dst addr =>
      if stackNoWriteback addr then (if dst = .gpr reg then none else unchanged) else none
  | .ldp _ _ dst dst2 addr =>
      if stackNoWriteback addr then (if dst = .gpr reg ∨ dst2 = .gpr reg then none else unchanged) else none
  | .str _ _ addr | .stp _ _ _ addr => if stackNoWriteback addr then unchanged else none
  | .b .. | .bCond .. | .cbz .. | .ret .. => unchanged
  | _ => none

def ResultInputsAgree (instruction : Arm64.Instr) (reg : BitVec 5) (left right : Arm64.State) : Prop :=
  match resultSources instruction reg with
  | none => False
  | some sources => RegistersAgree sources left right

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem result_sources_sound (instruction : Arm64.Instr) (reg : BitVec 5) (left right : Arm64.State)
    (pc : left.pc = right.pc) (agree : ResultInputsAgree instruction reg left right) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).readReg64 (.gpr reg) =
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).readReg64 (.gpr reg) := by
  by_cases zero : reg = 31#5
  · simp [zero, Arm64.State.readReg64]
  have z : (reg == 31#5) = false := by simp [zero]
  cases instruction <;> simp only [ResultInputsAgree, resultSources, z] at agree
  all_goals try cases ‹Arm64.AddrMode›
  all_goals simp only [stackNoWriteback, Bool.false_eq_true] at agree
  all_goals try split_ifs at agree
  all_goals try simp_all [RegistersAgree]
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift, Arm64.execAddSubShift,
    Arm64.execAddSubExt, Arm64.execDataProc1, Arm64.execLdr, Arm64.execStr, Arm64.execLdp, Arm64.execStp,
    Arm64.evalAddrMode]
  all_goals try simp_all [RegistersAgree, trace_read_write_reg, trace_read_write_reg64,
    Arm64.State.readReg, Arm64.State.readReg32]
  all_goals repeat' split
  all_goals try subst_vars
  all_goals try simp_all [RegistersAgree, trace_read_write_reg, trace_read_write_reg64,
    Arm64.State.readReg, Arm64.State.readReg32]

  all_goals cases ‹Arm64.BitfieldOp› <;> simp_all


/-- Only these two CMP forms generate flags selected by the SHA point masks. -/
def flagSources : Arm64.Instr → Option (List Arm64.Reg)
  | .addSubImm _ .SUBS _ rn _ _ => some [rn]
  | .addSubShift _ .SUBS _ rn rm _ _ => some [rn, rm]
  | _ => none

def FlagInputsAgree (instruction : Arm64.Instr) (left right : Arm64.State) : Prop :=
  match flagSources instruction with
  | none => False
  | some sources => RegistersAgree sources left right

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem flag_sources_sound (instruction : Arm64.Instr) (left right : Arm64.State)
    (agree : FlagInputsAgree instruction left right) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).pstate =
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).pstate := by
  cases instruction <;> simp only [FlagInputsAgree, flagSources] at agree
  all_goals cases ‹Arm64.AddSubOp›
  all_goals simp only [flagSources] at agree
  all_goals simp_all [RegistersAgree]
  all_goals cases ‹Arm64.RegWidth›
  all_goals simp_all [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execAddSubShift,
    Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.readReg32,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.setPState, Arm64.State.advancePC]


def resultInputsPublic (point : TracePoint) (instruction : Arm64.Instr) (reg : BitVec 5) : Bool :=
  ((resultSources instruction reg).map (fun sources => sources.all (registerPublicAt point))).getD false

def flagInputsPublic (point : TracePoint) (instruction : Arm64.Instr) : Bool :=
  ((flagSources instruction).map (fun sources => sources.all (registerPublicAt point))).getD false

def transferInputsPublic (before after : TracePoint) (instruction : Arm64.Instr) : Bool :=
  (List.finRange 32).all (fun reg =>
    if publicGPRAt after (BitVec.ofNat 5 reg.val) then resultInputsPublic before instruction (BitVec.ofNat 5 reg.val) else true) &&
  (if flagsPublicAt after then flagInputsPublic before instruction else true)

theorem public_result_inputs_agree (point : TracePoint) (instruction : Arm64.Instr) (reg : BitVec 5)
    (left right : Arm64.State) (related : PublicRelation point left right)
    (isPublic : resultInputsPublic point instruction reg = true) : ResultInputsAgree instruction reg left right := by
  cases sources : resultSources instruction reg with
  | none => simp [resultInputsPublic, sources] at isPublic
  | some registers =>
    have all : registers.all (registerPublicAt point) = true := by simpa [resultInputsPublic, sources] using isPublic
    change match resultSources instruction reg with | none => False | some xs => RegistersAgree xs left right
    rw [sources]
    intro r member
    exact related.read r (List.all_eq_true.mp all r member)

theorem public_flag_inputs_agree (point : TracePoint) (instruction : Arm64.Instr)
    (left right : Arm64.State) (related : PublicRelation point left right)
    (isPublic : flagInputsPublic point instruction = true) : FlagInputsAgree instruction left right := by
  cases sources : flagSources instruction with
  | none => simp [flagInputsPublic, sources] at isPublic
  | some registers =>
    have all : registers.all (registerPublicAt point) = true := by simpa [flagInputsPublic, sources] using isPublic
    change match flagSources instruction with | none => False | some xs => RegistersAgree xs left right
    rw [sources]
    intro r member
    exact related.read r (List.all_eq_true.mp all r member)

theorem transfer_inputs_register (before after : TracePoint) (instruction : Arm64.Instr)
    (checked : transferInputsPublic before after instruction = true)
    (reg : BitVec 5) (selected : publicGPRAt after reg = true) : resultInputsPublic before instruction reg = true := by
  have all : (List.finRange 32).all (fun r =>
      if publicGPRAt after (BitVec.ofNat 5 r.val) then resultInputsPublic before instruction (BitVec.ofNat 5 r.val) else true) = true :=
    by
      have parts := checked
      simp only [transferInputsPublic, Bool.and_eq_true] at parts
      exact parts.1
  let index : Fin 32 := ⟨reg.toNat, reg.isLt⟩
  have found := List.all_eq_true.mp all index (by simp)
  have same : BitVec.ofNat 5 index.val = reg := by simp [index]
  rw [same, selected] at found
  exact found

theorem transfer_inputs_flags (before after : TracePoint) (instruction : Arm64.Instr)
    (checked : transferInputsPublic before after instruction = true)
    (selected : flagsPublicAt after = true) : flagInputsPublic before instruction = true := by
  have parts := checked
  simp only [transferInputsPublic, Bool.and_eq_true] at parts
  simpa only [selected, ↓reduceIte] using parts.2

def tracePointIndex : TracePoint → IndexPoint
  | .instruction i => .instruction i.val
  | .returned => .returned

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem image_transfer_inputs : ∀ i : Fin 151, 4 ≤ i.val →
    (successorIndices i.val).all (fun next =>
      if h : next < 151 then
        ((Arm64.decode imageWords[i.val]!).map
          (transferInputsPublic (.instruction i) (.instruction ⟨next, h⟩))).getD false
      else false) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_return_transfer_inputs :
    ((Arm64.decode imageWords[150]!).map
      (transferInputsPublic (.instruction ⟨150, by decide⟩) .returned)).getD false = true := by
  decide +kernel

theorem image_edge_transfer_inputs (i : Fin 151) (next : TracePoint) (instruction : Arm64.Instr)
    (afterHeader : 4 ≤ i.val) (edge : labeledSuccessor i.val (tracePointIndex next) = true)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction) :
    transferInputsPublic (.instruction i) next instruction = true := by
  cases next with
  | instruction j =>
    have member := labeledSuccessor_mem i.val j.val edge
    have checked := List.all_eq_true.mp (image_transfer_inputs i afterHeader) j.val member
    have same : (⟨j.val, j.isLt⟩ : Fin 151) = j := rfl
    simpa only [j.isLt, ↓reduceDIte, same, decoded, Option.map_some, Option.getD_some] using checked
  | returned =>
    have index : i.val = 150 := by simpa only [tracePointIndex, labeledSuccessor, decide_eq_true_eq] using edge
    have same : i = (⟨150, by decide⟩ : Fin 151) := Fin.ext index
    subst i
    simpa only [decoded, Option.map_some, Option.getD_some] using image_return_transfer_inputs

/-- The syntactic source certificate is kernel computed from each CFG edge.
No next-register agreement or trace equality is assumed by this rule. -/
theorem image_public_relation_transfer (i : Fin 151) (next : TracePoint) (instruction : Arm64.Instr)
    (left right : Arm64.State) (afterHeader : 4 ≤ i.val)
    (edge : labeledSuccessor i.val (tracePointIndex next) = true)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction)
    (related : PublicRelation (.instruction i) left right)
    (leftRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction left).status = .Running)
    (rightRunning : (Arm64.execInstWithSvc Arm64.noSyscalls instruction right).status = .Running) :
    PublicRelation next (Arm64.execInstWithSvc Arm64.noSyscalls instruction left)
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction right) := by
  have observed := image_public_observation_eq i instruction left right decoded related leftRunning rightRunning
  have checked := image_edge_transfer_inputs i next instruction afterHeader edge decoded
  refine ⟨congrArg InstructionObservation.nextPC observed, congrArg InstructionObservation.nextSP observed, ?_, ?_⟩
  · intro reg selected
    exact result_sources_sound instruction reg left right related.pc
      (public_result_inputs_agree (.instruction i) instruction reg left right related
        (transfer_inputs_register (.instruction i) next instruction checked reg selected))
  · intro selected
    exact flag_sources_sound instruction left right
      (public_flag_inputs_agree (.instruction i) instruction left right related
        (transfer_inputs_flags (.instruction i) next instruction checked selected))

end Crypto.ARM64.Imported
