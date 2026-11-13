import Proofs.ARM64.ImportedPairedTrace
import Proofs.ARM64.ImportedHeaderRelation
import Proofs.ARM64.ImportedSafeCall

/-!
Architectural control/address trace noninterference for the complete native
SHA-256 call. Public runtime inputs are pointers, stack/link context, offset
and byte count. Payload bytes, prior stack/output and unrelated registers may
differ. The native instructions and their actual observations are compared;
neither equal traces nor public next-state registers are caller assumptions.
This is not a claim about every physical timing or other side channel.
-/
namespace Crypto.ARM64.Imported

structure SamePublicCall (left right : Arm64.State) : Prop where
  input : left.readReg64 .x0 = right.readReg64 .x0
  output : left.readReg64 .x1 = right.readReg64 .x1
  stack : left.sp = right.sp
  link : left.readReg64 .x30 = right.readReg64 .x30
  offset : left.mem.read64 (left.readReg64 .x0 + 8#64) = right.mem.read64 (right.readReg64 .x0 + 8#64)

theorem observed_call_running (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 data.size)) s = some (out, observations)) :
    out.status = .Running := by
  have actual := fetch_observed_raw_execution _ s out observations observed
  obtain ⟨known, native, _, _, _, _, _, running, _⟩ := whole_call_sha256 base s data entry
  have same : known = out := Option.some.inj (native.symm.trans actual)
  simpa only [same] using running

/-- Internal native execution composition rule. Its path/execution premises
are proved from caller conditions by public call theorems; auxiliary permission
views can use the same rule without assuming identical permission metadata. -/
theorem native_paired_call (count : BitVec 64) (base : BitVec 64) (left right : Arm64.State)
    (leftOut rightOut : Arm64.State) (leftObs rightObs : List InstructionObservation)
    (leftPC : left.pc = base) (rightPC : right.pc = base)
    (publicInputs : SamePublicCall left right)
    (countValues : left.mem.read64 (left.readReg64 .x0 + 16#64) =
      right.mem.read64 (right.readReg64 .x0 + 16#64))
    (leftOffsetRead : left.mem.canRead (left.readReg64 .x0 + 8#64) 8 = true)
    (leftCountRead : left.mem.canRead (left.readReg64 .x0 + 16#64) 8 = true)
    (rightOffsetRead : right.mem.canRead (right.readReg64 .x0 + 8#64) 8 = true)
    (rightCountRead : right.mem.canRead (right.readReg64 .x0 + 16#64) 8 = true)
    (leftPath : StaticPath base (wholeCallCode count) left)
    (rightPath : StaticPath base (wholeCallCode count) right)
    (leftObserved : runWordsObserved (wholeCallCode count) left = some (leftOut, leftObs))
    (rightObserved : runWordsObserved (wholeCallCode count) right = some (rightOut, rightObs))
    (leftRunning : leftOut.status = .Running) (rightRunning : rightOut.status = .Running) :
    leftObs = rightObs ∧ PublicRelation .returned leftOut rightOut := by
  let suffix := ((wholeCallIndices count).drop 4).map fun i => imageWords[i]!
  have leftExec := fetch_observed_raw_execution _ left leftOut leftObs leftObserved
  have rightExec := fetch_observed_raw_execution _ right rightOut rightObs rightObserved
  obtain ⟨headerLeft, headerRight, headerObs, leftHeader, rightHeader,
      leftHeaderObserved, rightHeaderObserved, relatedHeader⟩ :=
    paired_header left right (leftPC.trans rightPC.symm) publicInputs.stack publicInputs.input
      publicInputs.output publicInputs.link publicInputs.offset countValues
      leftOffsetRead leftCountRead rightOffsetRead rightCountRead
  have shape : wholeCallCode count = headerCode ++ suffix := wholeCallCode_header_suffix count
  have leftExpanded := runWords_code_cast (wholeCallCode count) (headerCode ++ suffix) left leftOut shape leftExec
  have rightExpanded := runWords_code_cast (wholeCallCode count) (headerCode ++ suffix) right rightOut shape rightExec
  have leftSuffix := runWords_suffix_of_prefix headerCode suffix left headerLeft leftOut leftHeader leftExpanded
  have rightSuffix := runWords_suffix_of_prefix headerCode suffix right headerRight rightOut rightHeader rightExpanded
  obtain ⟨leftTail, leftTailObserved⟩ := runWords_observed suffix headerLeft leftOut leftSuffix
  obtain ⟨rightTail, rightTailObserved⟩ := runWords_observed suffix headerRight rightOut rightSuffix
  have leftLabels := whole_call_labelPCPath base left leftOut count leftPC leftExec leftPath leftRunning
  have rightLabels := whole_call_labelPCPath base right rightOut count rightPC rightExec rightPath rightRunning
  have leftSuffixPath := wholeCallIndices_suffix_labelPCPath base count left headerLeft leftHeader leftLabels
  have rightSuffixPath := wholeCallIndices_suffix_labelPCPath base count right headerRight rightHeader rightLabels
  obtain ⟨sameTail, returned⟩ := paired_public_suffix count base headerLeft headerRight leftOut rightOut
    leftTail rightTail leftSuffixPath rightSuffixPath leftTailObserved rightTailObserved leftRunning rightRunning relatedHeader
  have leftCombined := runWordsObserved_append_success headerCode suffix left headerLeft leftOut headerObs leftTail
    leftHeaderObserved leftTailObserved
  have rightCombined := runWordsObserved_append_success headerCode suffix right headerRight rightOut headerObs rightTail
    rightHeaderObserved rightTailObserved
  have leftWhole := runWordsObserved_code_cast (headerCode ++ suffix) (wholeCallCode count) left leftOut
    (headerObs ++ leftTail) shape.symm leftCombined
  have rightWhole := runWordsObserved_code_cast (headerCode ++ suffix) (wholeCallCode count) right rightOut
    (headerObs ++ rightTail) shape.symm rightCombined
  have leftEq : leftObs = headerObs ++ leftTail :=
    (Prod.mk.inj (Option.some.inj (leftObserved.symm.trans leftWhole))).2
  have rightEq : rightObs = headerObs ++ rightTail :=
    (Prod.mk.inj (Option.some.inj (rightObserved.symm.trans rightWhole))).2
  exact ⟨leftEq.trans ((congrArg (headerObs ++ ·) sameTail).trans rightEq.symm), returned⟩

theorem sha256_observations_equal (base : BitVec 64) (left right : Arm64.State)
    (leftData rightData : ByteArray)
    (leftEntry : CallInputs base left leftData) (rightEntry : CallInputs base right rightData)
    (publicInputs : SamePublicCall left right) (countEqual : leftData.size = rightData.size)
    (leftOut rightOut : Arm64.State) (leftObs rightObs : List InstructionObservation)
    (leftObserved : runWordsObserved (wholeCallCode (BitVec.ofNat 64 leftData.size)) left = some (leftOut, leftObs))
    (rightObserved : runWordsObserved (wholeCallCode (BitVec.ofNat 64 rightData.size)) right = some (rightOut, rightObs)) :
    leftObs = rightObs ∧ PublicRelation .returned leftOut rightOut := by
  let count := BitVec.ofNat 64 leftData.size
  let suffix := ((wholeCallIndices count).drop 4).map fun i => imageWords[i]!
  have countEq : BitVec.ofNat 64 rightData.size = count := congrArg (BitVec.ofNat 64) countEqual.symm
  have codeEq := congrArg wholeCallCode countEq
  have leftExec := fetch_observed_raw_execution _ left leftOut leftObs leftObserved
  have rightExecOriginal := fetch_observed_raw_execution _ right rightOut rightObs rightObserved
  have rightExec := runWords_code_cast (wholeCallCode (BitVec.ofNat 64 rightData.size)) (wholeCallCode count)
    right rightOut codeEq rightExecOriginal
  have leftRunning := observed_call_running base left leftData leftEntry leftOut leftObs leftObserved
  have rightRunning := observed_call_running base right rightData rightEntry rightOut rightObs rightObserved
  have countValues : left.mem.read64 (left.readReg64 .x0 + 16#64) =
      right.mem.read64 (right.readReg64 .x0 + 16#64) := by
    rw [leftEntry.countValue, rightEntry.countValue, countEqual]
  obtain ⟨headerLeft, headerRight, headerObs, leftHeader, rightHeader,
      leftHeaderObserved, rightHeaderObserved, relatedHeader⟩ :=
    paired_header left right (leftEntry.pc.trans rightEntry.pc.symm) publicInputs.stack
      publicInputs.input publicInputs.output publicInputs.link publicInputs.offset countValues
      leftEntry.offsetRead leftEntry.countRead rightEntry.offsetRead rightEntry.countRead
  have shape : wholeCallCode count = headerCode ++ suffix := wholeCallCode_header_suffix count
  have leftExpanded := runWords_code_cast (wholeCallCode count) (headerCode ++ suffix) left leftOut shape leftExec
  have rightExpanded := runWords_code_cast (wholeCallCode count) (headerCode ++ suffix) right rightOut shape rightExec
  have leftSuffix := runWords_suffix_of_prefix headerCode suffix left headerLeft leftOut leftHeader leftExpanded
  have rightSuffix := runWords_suffix_of_prefix headerCode suffix right headerRight rightOut rightHeader rightExpanded
  obtain ⟨leftTail, leftTailObserved⟩ := runWords_observed suffix headerLeft leftOut leftSuffix
  obtain ⟨rightTail, rightTailObserved⟩ := runWords_observed suffix headerRight rightOut rightSuffix
  have leftLabels := callInputs_labelPCPath base left leftData leftEntry
  have rightLabels := LabelPCPath_code_cast base (wholeCallIndices (BitVec.ofNat 64 rightData.size))
    (wholeCallIndices count) right (congrArg wholeCallIndices countEq)
    (callInputs_labelPCPath base right rightData rightEntry)
  have leftPath := wholeCallIndices_suffix_labelPCPath base count left headerLeft leftHeader leftLabels
  have rightPath := wholeCallIndices_suffix_labelPCPath base count right headerRight rightHeader rightLabels
  obtain ⟨sameTail, returned⟩ := paired_public_suffix count base headerLeft headerRight leftOut rightOut
    leftTail rightTail leftPath rightPath leftTailObserved rightTailObserved leftRunning rightRunning relatedHeader
  have leftCombined := runWordsObserved_append_success headerCode suffix left headerLeft leftOut headerObs leftTail
    leftHeaderObserved leftTailObserved
  have rightCombined := runWordsObserved_append_success headerCode suffix right headerRight rightOut headerObs rightTail
    rightHeaderObserved rightTailObserved
  have leftWhole := runWordsObserved_code_cast (headerCode ++ suffix) (wholeCallCode count) left leftOut
    (headerObs ++ leftTail) shape.symm leftCombined
  have rightWhole := runWordsObserved_code_cast (headerCode ++ suffix) (wholeCallCode (BitVec.ofNat 64 rightData.size)) right rightOut
    (headerObs ++ rightTail) (shape.symm.trans codeEq.symm) rightCombined
  have leftEq : leftObs = headerObs ++ leftTail :=
    (Prod.mk.inj (Option.some.inj (leftObserved.symm.trans leftWhole))).2
  have rightEq : rightObs = headerObs ++ rightTail :=
    (Prod.mk.inj (Option.some.inj (rightObserved.symm.trans rightWhole))).2
  exact ⟨leftEq.trans ((congrArg (headerObs ++ ·) sameTail).trans rightEq.symm), returned⟩

end Crypto.ARM64.Imported
