import Proofs.RISCV64.Phase
import Proofs.ARM64.ImportedReferenceFold

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (paddedSpecBlock paddedSpecFold paddingBlockCount padded_block_count)
open SHS.Equiv.SHA256.Padding.Layout (implPaddedBytes)
open SHS.Equiv.ArrayFold (fin_foldl_ext)

/-- The two phase hashes agree with FIPS once the initialized hash and the
message and padding memory blocks have been identified. -/
theorem phase_hash_reference (message padding : CPU) (data : ByteArray)
    (initial : storedHash message = SHS.SHA256.H0_256)
    (chaining : storedHash padding = phaseHash message (data.size / 64))
    (full : ∀ i : Fin (data.size / 64),
      blockWords message.mem (message.reg 12 + BitVec.ofNat 64 (64*i.val)) =
        paddedSpecBlock data i.val)
    (tail : ∀ i : Fin (paddingBlockCount data),
      blockWords padding.mem (padding.reg 12 + BitVec.ofNat 64 (64*i.val)) =
        paddedSpecBlock data (data.size / 64 + i.val)) :
    phaseHash padding (paddingBlockCount data) =
      paddedSpecFold data ((implPaddedBytes data).size / 64) := by
  rw [padded_block_count]
  unfold phaseHash paddedSpecFold
  rw [Fin.foldl_add, chaining]
  unfold phaseHash
  rw [initial]
  have messageFold := fin_foldl_ext (data.size / 64)
    (fun H i => SHS.SHA256.compress H
      (blockWords message.mem (message.reg 12 + BitVec.ofNat 64 (64*i.val))))
    (fun H i => SHS.SHA256.compress H (paddedSpecBlock data i.val)) SHS.SHA256.H0_256
    (fun H i => congrArg (SHS.SHA256.compress H) (full i))
  rw [messageFold]
  apply fin_foldl_ext
  intro H i
  exact congrArg (SHS.SHA256.compress H) (tail i)

end Crypto.RISCV64
