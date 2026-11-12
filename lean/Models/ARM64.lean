import Arm64.Trusted.ISA.Semantics
import Models.ARM64Program

/-!
Unchanged upstream AArch64 execution semantics, pinned by the `lean/Imports/arm64` Git submodule.
The program has no extern/override hooks. A supervisor call faults: no software
or cryptographic primitive is substituted for any instruction in this image.

The upstream ISA is a trusted model, with documented differential tests; it is
not a theorem about physical hardware. Its process/loader model is Linux only.
macOS and Windows claims still require their own ABI/artifact/loading bridges.
-/
namespace Crypto.ARM64.Imported

def program (base : BitVec 64) : Arm64.Program :=
  Arm64.Program.ofWords base imageWords.toList [("crypto_sha256", base)] Arm64.noSyscalls

/-- A bounded evaluator for validation and constructive proofs. It succeeds
only after executing a RET with no fault; exhausting fuel is failure. Its
connection to the imported `Steps` relation is proved separately. -/
def runToReturn (prog : Arm64.Program) : Nat → Arm64.State → Option Arm64.State
  | 0, _ => none
  | fuel + 1, s =>
    if s.status ≠ .Running then none else do
      let instruction ← prog.fetchMem s.mem s.pc
      let after := prog.evalInst instruction s
      if after.status ≠ .Running then none else
        match instruction with
        | .ret _ => some after
        | _ => runToReturn prog fuel after

end Crypto.ARM64.Imported
