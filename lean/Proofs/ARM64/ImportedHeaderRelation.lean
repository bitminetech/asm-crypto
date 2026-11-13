import Proofs.ARM64.ImportedHeader
import Proofs.ARM64.ImportedTraceMasks

/-!
Paired execution of exactly the first four recorded SHA-256 words. Equal
public PC/SP/input/output/link-register context and truthful equal offset/count
metadata yield the same actual observation list and the public register mask
at instruction4. Payload bytes, old stack/output contents and other registers
may differ; the actual header-read guards remain explicit on each execution.
This is a native word/observation relation, not a whole-call trace or physical
timing certificate.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def headerInstructions : List Arm64.Instr := [
  .addSubImm .W64 .SUB .sp .sp 416#12 false,
  .ldr .W64 .X64 false .x5 (.Offset .x0 8#64),
  .ldr .W64 .X64 false .x15 (.Offset .x0 16#64),
  .addSubShift .W64 .ADD .x2 .x0 .x5 .LSL 0]

theorem header_trace_decoded : headerCode.mapM Arm64.decode = some headerInstructions := by decide +kernel

def runDecodedObserved : List Arm64.Instr → Arm64.State → Arm64.State × List InstructionObservation
  | [], s => (s, [])
  | instruction :: rest, s =>
    let (out, observations) := runDecodedObserved rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)
    (out, instructionObservation instruction s :: observations)

theorem runWordsObserved_decode (words : List (BitVec 32)) (s : Arm64.State) :
    runWordsObserved words s = (words.mapM Arm64.decode).map (fun decoded => runDecodedObserved decoded s) := by
  induction words generalizing s with
  | nil => rfl
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded, List.mapM_cons]
    | some instruction =>
      simp only [runWordsObserved, decoded, List.mapM_cons, Bind.bind, Option.bind]
      rw [ih]
      cases rest.mapM Arm64.decode <;> simp [runDecodedObserved]

def headerObservations (s : Arm64.State) : List InstructionObservation := [
  ⟨s.pc, s.pc + 4#64, s.sp, s.sp - 416#64, []⟩,
  ⟨s.pc + 4#64, s.pc + 8#64, s.sp - 416#64, s.sp - 416#64,
    [⟨false, s.readReg64 .x0 + 8#64, 8⟩]⟩,
  ⟨s.pc + 8#64, s.pc + 12#64, s.sp - 416#64, s.sp - 416#64,
    [⟨false, s.readReg64 .x0 + 16#64, 8⟩]⟩,
  ⟨s.pc + 12#64, s.pc + 16#64, s.sp - 416#64, s.sp - 416#64, []⟩]

theorem header_observation_values (s : Arm64.State)
    (offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true)
    (countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true) :
    (runWordsObserved headerCode s).map Prod.snd = some (headerObservations s) := by
  rw [runWordsObserved_decode, header_trace_decoded]
  simp (config := { decide := true }) [runDecodedObserved, headerInstructions,
    instructionObservation, dataAccesses, headerObservations, Arm64.execInstWithSvc,
    Arm64.execAddSubImm, Arm64.execLdr, Arm64.execAddSubShift, Arm64.evalAddSub,
    Arm64.shiftVal, Arm64.shift64, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.evalAddrMode, Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    BitVec.truncate_eq_setWidth, subtract416, addWithCarry64_add, offsetRead, countRead, BitVec.add_assoc]

theorem header_observations_eq (left right : Arm64.State)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (input : left.readReg64 .x0 = right.readReg64 .x0) :
    headerObservations left = headerObservations right := by
  unfold headerObservations
  rw [pc, sp, input]

theorem observed_trace_projection (words : List (BitVec 32)) (s out : Arm64.State)
    (observations expected : List InstructionObservation)
    (executed : runWordsObserved words s = some (out, observations))
    (projected : (runWordsObserved words s).map Prod.snd = some expected) : observations = expected := by
  have actual := congrArg (Option.map Prod.snd) executed
  have trace : (runWordsObserved words s).map Prod.snd = some observations := by
    simpa only [Option.map_some] using actual
  exact Option.some.inj (trace.symm.trans projected)

theorem header_public_registers : ∀ r : BitVec 5,
    publicGPRAt (.instruction ⟨4, by decide⟩) r = true →
    r = 0#5 ∨ r = 1#5 ∨ r = 2#5 ∨ r = 5#5 ∨ r = 15#5 ∨ r = 30#5 := by decide +kernel

theorem paired_header (left right : Arm64.State)
    (pc : left.pc = right.pc) (sp : left.sp = right.sp)
    (input : left.readReg64 .x0 = right.readReg64 .x0)
    (output : left.readReg64 .x1 = right.readReg64 .x1)
    (link : left.readReg64 .x30 = right.readReg64 .x30)
    (offset : left.mem.read64 (left.readReg64 .x0 + 8#64) = right.mem.read64 (right.readReg64 .x0 + 8#64))
    (count : left.mem.read64 (left.readReg64 .x0 + 16#64) = right.mem.read64 (right.readReg64 .x0 + 16#64))
    (leftOffsetRead : left.mem.canRead (left.readReg64 .x0 + 8#64) 8 = true)
    (leftCountRead : left.mem.canRead (left.readReg64 .x0 + 16#64) 8 = true)
    (rightOffsetRead : right.mem.canRead (right.readReg64 .x0 + 8#64) 8 = true)
    (rightCountRead : right.mem.canRead (right.readReg64 .x0 + 16#64) 8 = true) :
    ∃ leftOut rightOut observations,
      runWords headerCode left = some leftOut ∧ runWords headerCode right = some rightOut ∧
      runWordsObserved headerCode left = some (leftOut, observations) ∧
      runWordsObserved headerCode right = some (rightOut, observations) ∧
      PublicRelation (.instruction ⟨4, by decide⟩) leftOut rightOut := by
  obtain ⟨leftOut, leftExecuted, leftPost⟩ := exists_of_map_some _ _ _ (decode_header left leftOffsetRead leftCountRead)
  obtain ⟨rightOut, rightExecuted, rightPost⟩ := exists_of_map_some _ _ _ (decode_header right rightOffsetRead rightCountRead)
  simp only [Prod.mk.injEq] at leftPost rightPost
  obtain ⟨_, _, leftSP, leftPC, leftNV, left0, left1, left2, left5, left15⟩ := leftPost
  obtain ⟨_, _, rightSP, rightPC, rightNV, right0, right1, right2, right5, right15⟩ := rightPost
  obtain ⟨leftTrace, leftObserved⟩ := runWords_observed headerCode left leftOut leftExecuted
  obtain ⟨rightTrace, rightObserved⟩ := runWords_observed headerCode right rightOut rightExecuted
  have leftTraceEq := observed_trace_projection headerCode left leftOut leftTrace (headerObservations left)
    leftObserved (header_observation_values left leftOffsetRead leftCountRead)
  have rightTraceEq := observed_trace_projection headerCode right rightOut rightTrace (headerObservations right)
    rightObserved (header_observation_values right rightOffsetRead rightCountRead)
  have traceEq : leftTrace = rightTrace := leftTraceEq.trans ((header_observations_eq left right pc sp input).trans rightTraceEq.symm)
  rw [← traceEq] at rightObserved
  have left30 := congrFun leftNV ⟨12, by decide⟩
  have right30 := congrFun rightNV ⟨12, by decide⟩
  change leftOut.readReg64 .x30 = left.readReg64 .x30 at left30
  change rightOut.readReg64 .x30 = right.readReg64 .x30 at right30
  refine ⟨leftOut, rightOut, leftTrace, leftExecuted, rightExecuted, leftObserved, rightObserved, ?_⟩
  constructor
  · exact leftPC.trans ((congrArg (· + 16#64) pc).trans rightPC.symm)
  · exact leftSP.trans ((congrArg (· - 416#64) sp).trans rightSP.symm)
  · intro r selected
    rcases header_public_registers r selected with reg | reg | reg | reg | reg | reg <;> subst r
    · exact left0.trans (input.trans right0.symm)
    · exact left1.trans (output.trans right1.symm)
    · exact left2.trans ((congrArg₂ (· + ·) input offset).trans right2.symm)
    · exact left5.trans (offset.trans right5.symm)
    · exact left15.trans (count.trans right15.symm)
    · exact left30.trans (link.trans right30.symm)
  · intro impossible
    exact Bool.noConfusion impossible

end Crypto.ARM64.Imported
