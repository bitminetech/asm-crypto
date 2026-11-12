import Proofs.ARM64.ImportedWholeCallFetch
import Proofs.ARM64.ImportedHashBodyFrame

/-!
The complete native call preserves every memory cell outside its 416-byte
stack frame and 32-byte digest. This final-memory frame is distinct from the
remaining every-access, lifetime, interference and confidentiality obligations.
-/
namespace Crypto.ARM64.Imported

theorem whole_call_memory_frame (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) (out : Arm64.State)
    (executed : runWords (wholeCallCode (BitVec.ofNat 64 data.size)) s = some out) :
    ∀ p, 416 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.readReg64 .x1).toNat →
      out.mem.cells p = s.mem.cells p := by
  obtain ⟨body, prepared⟩ := prepare_whole_call base s data entry
  have hn : data.size < 2 ^ 64 := by have := entry.bound; omega
  have shape : wholeCallCode (BitVec.ofNat 64 data.size) =
      prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data) := by
    simp only [wholeCallCode, prologueCode, headerPaddingCode, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, paddingBlockCount, List.append_assoc]
  have expanded := runWords_code_cast (wholeCallCode (BitVec.ofNat 64 data.size))
    (prologueCode (BitVec.ofNat 64 data.size) ++ hashBodyCode (data.size / 64) (paddingBlockCount data))
    s out shape executed
  have bodyExec := runWords_suffix_of_prefix (prologueCode (BitVec.ofNat 64 data.size))
    (hashBodyCode (data.size / 64) (paddingBlockCount data)) s body out prepared.executed expanded
  intro p stackOutside outputOutside
  have outsideBody : 288 ≤ (p - body.sp).toNat := by rw [prepared.stack]; omega
  have outsideOutput : 32 ≤ (p - body.readReg64 .x1).toNat := by rw [prepared.output]; exact outputOutside
  have frame := hash_body_memory_frame body prepared.ready (data.size / 64) (paddingBlockCount data)
    (by omega) (paddingBlockCount_bounds data).2 prepared.count prepared.phase prepared.padCount
    prepared.fullReads prepared.fullSep prepared.padRead prepared.outWrite prepared.outSep
    out bodyExec p outsideBody outsideOutput
  exact frame.trans (prepared.outside p stackOutside)

end Crypto.ARM64.Imported
