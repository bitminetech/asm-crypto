import Proofs.RISCV64.CallCode
import Proofs.RISCV64.Permissions

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (memoryBytes32)

def callSteps (size : Nat) : Nat :=
  155 + 7*(size % 64) + 5126*(size / 64 + (if size % 64 < 56 then 1 else 2)) +
    (if size % 64 < 56 then 0 else 1)

/-- If the data-address trace has the required alignment and permissions in
the caller's memory, the permission-checked evaluator reaches the first
return with the FIPS digest and the serial frame guarantees. -/
theorem run_sha256 (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data)
    (outputOutside : ∀ i : Fin 32, 480 ≤ (s.reg 11 + BitVec.ofNat 64 i.val - entryStack s).toNat)
    (aligned : base.toNat % 2 = 0) (executable : s.mem.canExec base codeEnd = true)
    (readOnly : ImageReadOnly base s.mem)
    (dataPermitted : ((accessTrace (callCode data.size) s).filter Access.isData).all
      (Access.permitted s.mem) = true) :
    ∃ out, runUntilReturn base s (callSteps data.size) = some out ∧
      out.pc = s.reg 1 &&& ~~~(1 : Addr) ∧ out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 ∧
      savedRegisters out = savedRegisters s ∧
      memoryBytes32 out.mem (s.reg 11) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec ∧
      (∀ p, 480 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.reg 11).toNat →
        out.mem.cells p = s.mem.cells p) := by
  obtain ⟨out, actual, pos, status, sp, saved, bytes, cells⟩ := serial_sha256 base s data entry outputOutside
  have path := actual.decoded
  have allowed := path.initial_permitted s.mem aligned executable dataPermitted
  have permission := permittedPath_of_accesses base s _ entry.loaded readOnly allowed
  have executed := path.to_first_return permission (call_has_return data.size)
  have steps : (callCode data.size).length = callSteps data.size := call_instruction_count data.size
  rw [steps] at executed
  exact ⟨out, executed, pos, status, sp, saved, bytes, cells⟩

end Crypto.RISCV64
