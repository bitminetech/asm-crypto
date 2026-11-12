import Proofs.ARM64.ImportedPaddingFetch
import Proofs.ARM64.ImportedWholeCall
import Proofs.ARM64.ImportedHashBodyFetch

/-!
The complete SHA-256 recorded-word path agrees with the loaded image address
at every instruction, from header decoding through the final return. The
existential theorem derives execution, the path and the pinned FIPS digest
from unchanged operational CallInputs; no execution/path/digest premise is
added to caller entry. Full architecture resource, trace, target-profile and
baseline requirements remain separate from this supporting certificate.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem prologue_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (out : Arm64.State)
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

theorem whole_call_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (out : Arm64.State)
    (executed : runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out)
    (running : out.status = .Running) : StaticPath base (wholeCallCode (BitVec.ofNat 64 data.size)) s := by
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  have shape : wholeCallCode (BitVec.ofNat 64 data.size) =
      prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data) := by
    simp only [wholeCallCode, prologueCode, headerPaddingCode, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, paddingBlockCount, List.append_assoc]
  obtain ⟨body, prepared⟩ := prepare_whole_call base s data entry
  have bodyExec : runWords (hashBodyCode (data.size / 64) (paddingBlockCount data)) body = some out := by
    have expanded := padding_runWords_code_cast s out (wholeCallCode (BitVec.ofNat 64 data.size))
      (prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data)) shape executed
    exact padding_runWords_suffix (prologueCode (BitVec.ofNat 64 data.size))
      (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body out prepared.executed expanded
  have bodyRunning := congrArg Arm64.State.status prepared.state
  change body.status = s.status at bodyRunning
  have prefixPath := prologue_staticPath base s data entry body prepared.executed (bodyRunning.trans entry.running)
  have suffixPath := hash_body_staticPath base body prepared.ready (data.size / 64) (paddingBlockCount data)
    (by omega) (paddingBlockCount_bounds data).2 prepared.count prepared.phase prepared.padCount
    prepared.fullReads prepared.fullSep prepared.padRead prepared.outWrite prepared.outSep out prepared.pc bodyExec running
  have combined := @StaticPath.append base (prologueCode (BitVec.ofNat 64 data.size)) (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body prepared.executed prefixPath suffixPath
  exact staticPath_code_cast base s (wholeCallCode (BitVec.ofNat 64 data.size))
    (prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data)) shape combined

theorem whole_call_sha256_staticPath (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) :
    ∃ out, runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out ∧
      StaticPath base (wholeCallCode (BitVec.ofNat 64 data.size)) s ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧ memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
  obtain ⟨out, executed, state, nv, sp, pc, zero, running, digest⟩ := whole_call_sha256 base s data entry
  exact ⟨out, executed, whole_call_staticPath base s data entry out executed running,
    state, nv, sp, pc, zero, running, digest⟩

end Crypto.ARM64.Imported
