import Proofs.HMACSHA256.Reference
import Proofs.ARM64.NativeEqual
import Proofs.X86_64.NativeEqual
import Proofs.RISCV64.ModeledBaseline

/-! Instantiate the existing SHA-256 baseline at a call boundary and express
its output bytes in the form used by EthLib's HMAC. Each invocation must
establish the corresponding SHA-256 entry predicate. -/
namespace Crypto.HMACSHA256

open Crypto.Reference
open EthLib.Cryptography.Hash

theorem ARM64.sha256_callee (base : BitVec 64) (state : Arm64.State) (input : ByteList)
    (extent : Nat) (authority : Crypto.Baseline.Authority) (fpcr : BitVec 32)
    (entry : Crypto.ARM64.Imported.PermissionViewInputs base state input extent authority) :
    ∃ out observations,
      Crypto.ARM64.Imported.SerialCallResult base state input extent authority fpcr out observations ∧
      Crypto.ARM64.Imported.memoryBytes32 out.mem (state.readReg64 .x1) =
        (Sha256.hash32 input.bytes).map UInt8.toBitVec := by
  have serial : Crypto.ARM64.NativeRequirements.Serial :=
    Crypto.ARM64.sha256.equal.referenceAndSafety.2
  obtain ⟨out, observations, result⟩ := serial base state input extent authority fpcr entry
  refine ⟨out, observations, result, ?_⟩
  rw [result.safe.digest, sha256_digest_eq_ethlib input entry.length]

theorem X86_64.sha256_callee {base : X86.Val} {state : X86.Cpu} {input : ByteList}
    {extent : Nat} {authority : Crypto.Baseline.Authority}
    (entry : Crypto.X86_64.PermissionEntry base state input extent authority) :
    ∃ out events,
      Crypto.X86_64.NativeSerial base state out input extent authority events ∧
      Crypto.ARM64.Imported.memoryBytes32 (Crypto.X86_64.byteView out.mem) (state.regs.get .rsi) =
        (Sha256.hash32 input.bytes).map UInt8.toBitVec := by
  have serial : Crypto.X86_64.NativeRequirements.Serial :=
    Crypto.X86_64.sha256.equal.referenceAndSafety.2
  obtain ⟨out, events, result⟩ := serial base state input extent authority entry
  refine ⟨out, events, result, ?_⟩
  rw [result.result.digest, sha256_digest_eq_ethlib input entry.bound]

theorem RISCV64.sha256_callee (base : Crypto.RISCV64.Addr) (state : Crypto.RISCV64.CPU)
    (input : ByteList) (extent : Nat) (entry : Crypto.RISCV64.CallerEntry base state input extent) :
    ∃ out,
      Crypto.RISCV64.runUntilReturn base state (Crypto.RISCV64.callSteps input.bytes.size) = some out ∧
      Crypto.RISCV64.CallResult state out input ∧ Crypto.RISCV64.FrameResult state out ∧
      Crypto.ARM64.Imported.memoryBytes32 out.mem (state.reg 11) =
        (Sha256.hash32 input.bytes).map UInt8.toBitVec := by
  have serial : Crypto.RISCV64.FunctionalSafety :=
    Crypto.RISCV64.modeled_baseline.referenceAndSafety
  obtain ⟨out, executed, result, frame⟩ := serial base state input extent entry
  refine ⟨out, executed, result, frame, ?_⟩
  rw [result.digest, sha256_digest_eq_ethlib input entry.length]

end Crypto.HMACSHA256
