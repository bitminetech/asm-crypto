import Proofs.ARM64.ImportedStrictReadCallPreparation
import Proofs.ARM64.ImportedWholeCallFetch

/-!
Constructive success of the unchanged complete native SHA-256 word tape under
an auxiliary pool-only image-data read view. Header/padding, pool copies,
schedule/compression phases and RET use the existing imported ISA proofs.
The explicit pool values and guards come from RawSHAInputs, and the final
caller theorem derives them from unchanged PermissionViewInputs.

The actual observed word execution and static image path are produced, not
assumed as caller facts. This auxiliary theorem neither changes the real RX
loaded-image baseline nor claims a separate physical X-only memory profile.
A paired native-trace theorem can transfer its tighter data footprint to the
actual call; that transfer is a separate supporting result.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
attribute [local irreducible] runWords StaticPath

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem raw_whole_call_sha256 (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : RawSHAInputs base s data) :
    ∃ out, runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧ memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  obtain ⟨body, prepared⟩ := prepare_raw_call base s data entry
  obtain ⟨out, ho, ostate, onv, osp, opc, status, _, bytes⟩ :=
    hash_body_sha256 body data prepared.ready entry.bound prepared.count prepared.phase prepared.padCount
      prepared.fullReads prepared.fullSep prepared.padRead prepared.outWrite prepared.outSep
      prepared.initial prepared.input prepared.padding
  have lr := congrFun prepared.nonvolatile ⟨12, by decide⟩
  change body.readReg64 .x30 = s.readReg64 .x30 at lr
  have whole := @runWords_append_success (prologueCode (BitVec.ofNat 64 data.size))
    (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body out prepared.executed ho
  have state := ostate.trans prepared.state
  have running := congrArg Arm64.State.status state
  change out.status = s.status at running
  refine ⟨out, ?_, state, onv.trans prepared.nonvolatile, ?_, opc.trans lr, status,
    running.trans entry.running, ?_⟩
  · have shape : prologueCode (BitVec.ofNat 64 data.size) ++
        hashBodyCode (data.size / 64) (paddingBlockCount data) = wholeCallCode (BitVec.ofNat 64 data.size) := by
      simp only [wholeCallCode, prologueCode, headerPaddingCode, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hn, paddingBlockCount, List.append_assoc]
    exact runWords_code_cast _ _ s out shape whole
  · rw [osp, prepared.stack]
    exact BitVec.sub_add_cancel _ _
  · simpa only [prepared.output] using bytes


theorem raw_prologue_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : RawSHAInputs base s data) (out : Arm64.State)
    (executed : runWords (prologueCode (BitVec.ofNat 64 data.size)) s = some out)
    (running : out.status = .Running) : StaticPath base (prologueCode (BitVec.ofNat 64 data.size)) s := by
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  have tailIndex (i : Fin (data.size % 64)) : data.size / 64 * 64 + i.val < data.size := by
    have ih := i.isLt
    omega
  have chunks (i : Fin 16) : s.mem.canWrite (entryStack s + 288#64 + BitVec.ofNat 64 (8 * i.val)) 8 = true := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (288 + 8 * i.val) 8 (by have := i.isLt; omega)
  have padBytes (i : Fin 128) : s.mem.canWrite (entryStack s + 288#64 + BitVec.ofNat 64 i.val) 1 = true := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.stackWrite (288 + i.val) 1 (by have := i.isLt; omega)
  have tailReads (i : Fin (data.size % 64)) : s.mem.canRead (entryTail s data + BitVec.ofNat 64 i.val) 1 = true := by
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using
      entry.inputRead (data.size / 64 * 64 + i.val) 1 (by have := tailIndex i; omega)
  have tailSep (i : Fin (data.size % 64)) :
      128 ≤ (entryTail s data + BitVec.ofNat 64 i.val - (entryStack s + 288#64)).toNat := by
    have outside := entry.inputOutside ⟨data.size / 64 * 64 + i.val, tailIndex i⟩
    have dist := region_store_delta (entryStack s) _ 288 416 128 (by decide) outside
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using dist
  have tailValues (i : Fin (data.size % 64)) : s.mem.read8 (entryTail s data + BitVec.ofNat 64 i.val) =
      (data.get! (data.size / 64 * 64 + i.val)).toBitVec := by
    simpa only [entryTail, BitVec.ofNat_add, BitVec.add_assoc] using
      entry.inputBytes ⟨data.size / 64 * 64 + i.val, tailIndex i⟩
  obtain ⟨padded, hp, pstate, pnv, psp, ppc, _, p1, p2, p3, p6, _, _, _, padding, pframe, pread, pwrite⟩ :=
    header_padding s data entry.bound entry.offsetRead entry.countRead entry.countValue chunks padBytes tailReads tailSep tailValues
  have initExec : runWords hashInitCode padded = some out := by
    have expanded := padding_runWords_code_cast s out (prologueCode (BitVec.ofNat 64 data.size))
      (headerPaddingCode (BitVec.ofNat 64 data.size) ++ hashInitCode) rfl executed
    exact padding_runWords_suffix (headerPaddingCode (BitVec.ofNat 64 data.size)) hashInitCode s padded out hp expanded
  have paddedRunning := runWords_running_before hashInitCode padded out hash_init_words_permitted initExec running
  have paddedPC : padded.pc = base + 132#64 := by rw [ppc, entry.pc]
  have prefixPath := header_padding_staticPath base s data entry.bound entry.offsetRead entry.countRead
    entry.countValue chunks padBytes tailReads tailSep padded entry.pc hp paddedRunning
  have initPath := (hash_init_linear_path base padded out paddedPC initExec running).1
  have combined := @StaticPath.append base (headerPaddingCode (BitVec.ofNat 64 data.size)) hashInitCode s padded hp prefixPath initPath
  exact staticPath_code_cast base s (prologueCode (BitVec.ofNat 64 data.size))
    (headerPaddingCode (BitVec.ofNat 64 data.size) ++ hashInitCode) rfl combined

theorem raw_whole_call_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : RawSHAInputs base s data) (out : Arm64.State)
    (executed : runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out)
    (running : out.status = .Running) : StaticPath base (wholeCallCode (BitVec.ofNat 64 data.size)) s := by
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  have shape : wholeCallCode (BitVec.ofNat 64 data.size) =
      prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data) := by
    simp only [wholeCallCode, prologueCode, headerPaddingCode, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, paddingBlockCount, List.append_assoc]
  obtain ⟨body, prepared⟩ := prepare_raw_call base s data entry
  have bodyExec : runWords (hashBodyCode (data.size / 64) (paddingBlockCount data)) body = some out := by
    have expanded := padding_runWords_code_cast s out (wholeCallCode (BitVec.ofNat 64 data.size))
      (prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data)) shape executed
    exact padding_runWords_suffix (prologueCode (BitVec.ofNat 64 data.size))
      (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body out prepared.executed expanded
  have bodyRunning := congrArg Arm64.State.status prepared.state
  change body.status = s.status at bodyRunning
  have prefixPath := raw_prologue_staticPath base s data entry body prepared.executed (bodyRunning.trans entry.running)
  have suffixPath := hash_body_staticPath base body prepared.ready (data.size / 64) (paddingBlockCount data)
    (by omega) (paddingBlockCount_bounds data).2 prepared.count prepared.phase prepared.padCount
    prepared.fullReads prepared.fullSep prepared.padRead prepared.outWrite prepared.outSep out prepared.pc bodyExec running
  have combined := @StaticPath.append base (prologueCode (BitVec.ofNat 64 data.size)) (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body prepared.executed prefixPath suffixPath
  exact staticPath_code_cast base s (wholeCallCode (BitVec.ofNat 64 data.size))
    (prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data)) shape combined


structure StrictReadCallResult (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (out : Arm64.State) (observations : List InstructionObservation) : Prop where
  executed : runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (strictState base s message) = some out
  observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (strictState base s message) = some (out, observations)
  running : out.status = .Running
  path : StaticPath base (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) (strictState base s message)
  state : returnStable out = returnStable s
  nonvolatile : Crypto.ARM64.Imported.nonvolatile out = Crypto.ARM64.Imported.nonvolatile s
  stackRestored : out.sp = s.sp
  returnAddress : out.pc = s.readReg64 .x30
  status : out.readReg64 .x0 = 0#64
  digest : memoryBytes32 out.mem (s.readReg64 .x1) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec

theorem sha256_strict_read_call (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    ∃ out observations, StrictReadCallResult base s message out observations := by
  have inputs := strict_view_raw_inputs base s message extent authority entry
  obtain ⟨out, executed, state, nv, sp, pc, zero, running, digest⟩ :=
    raw_whole_call_sha256 base (strictState base s message) message.bytes inputs
  obtain ⟨observations, observed⟩ := runWords_observed _ _ out executed
  have path := raw_whole_call_staticPath base (strictState base s message) message.bytes inputs out executed running
  have erase : returnStable (strictState base s message) = returnStable s := by cases s; rfl
  refine ⟨out, observations, executed, observed, running, path, state.trans erase, ?_, ?_, ?_, zero, ?_⟩
  · simpa only [nonvolatile, strictState_readReg] using nv
  · simpa only [strictState_sp] using sp
  · simpa only [strictState_readReg] using pc
  · simpa only [strictState_readReg, Crypto.Reference.sha256] using digest

end Crypto.ARM64.Imported
