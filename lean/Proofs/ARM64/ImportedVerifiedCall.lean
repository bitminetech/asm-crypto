import Proofs.ARM64.ImportedWholeCallFetch
import Proofs.ARM64.ImportedCallReturn
import Proofs.ARM64.ImportedCallerEntry
import Proofs.ARM64.ImportedAccess
import Proofs.ARM64.ImportedWholeCallFrame

/-!
Complete bounded, memory-fetched SHA-256 correctness under the imported model
and the explicit operational or typed caller-entry conditions. The result is
the unchanged pinned FIPS byte reference, with modeled state/ABI preservation.
The observed raw path erases to those same imported instruction executions.

These are supporting callable theorems, not the architecture equal baseline:
declared-region trace confinement, confidentiality/timing, lifetime/concurrency,
physical/OS profiles and independently pinned baseline validation remain.
-/
namespace Crypto.ARM64.Imported

theorem sha256_fetched (base : BitVec 64) (s : Arm64.State) (data : ByteArray)
    (entry : CallInputs base s data) :
    ∃ out, runToReturn (program base) (512 + 4000 * ((data.size + 8) / 64 + 1)) s = some out ∧
      Arm64.Steps (program base) s out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧
      memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec ∧
      (∀ p, 416 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.readReg64 .x1).toNat →
        out.mem.cells p = s.mem.cells p) ∧
      AccessPath (wholeCallCode (BitVec.ofNat 64 data.size)) s ∧
      ∃ observations, runWordsObserved (wholeCallCode (BitVec.ofNat 64 data.size)) s = some (out, observations) := by
  obtain ⟨out, executed, path, state, nv, sp, pc, zero, running, digest⟩ :=
    whole_call_sha256_staticPath base s data entry
  have bounded := whole_call_return_from_path base s out (BitVec.ofNat 64 data.size)
    entry.loaded executed path running
  have sizeBound : data.size < 2 ^ 64 := by have := entry.bound; omega
  have returned : runToReturn (program base) (512 + 4000 * ((data.size + 8) / 64 + 1)) s = some out := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeBound] using bounded
  exact ⟨out, returned, runToReturn_steps _ _ s out returned, state, nv, sp, pc, zero, running, digest,
    whole_call_memory_frame base s data entry out executed,
    runWords_accessPath _ s out (whole_call_permitted _) executed running,
    runWords_observed _ s out executed⟩

theorem sha256_callable (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out, runToReturn (program base) (512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) s = some out ∧
      Arm64.Steps (program base) s out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp ∧ out.pc = s.readReg64 .x30 ∧ out.readReg64 .x0 = 0#64 ∧
      out.status = .Running ∧
      memoryBytes32 out.mem (s.readReg64 .x1) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec ∧
      (∀ p, 416 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.readReg64 .x1).toNat →
        out.mem.cells p = s.mem.cells p) ∧
      AccessPath (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) s ∧
      ∃ observations, runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) s = some (out, observations) :=
  sha256_fetched base s message.bytes (caller_entry_inputs base s message extent entry)

end Crypto.ARM64.Imported
