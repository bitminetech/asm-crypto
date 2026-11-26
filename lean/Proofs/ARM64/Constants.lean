import Models.ARM64Program
import EthLib.Cryptography.Hash.Sha256

namespace Crypto.ARM64

/-- Every round constant recorded in the machine-code image is the corresponding
constant of the imported byte-oriented reference. This is a data identity lemma,
not a theorem about instruction execution or loaded memory. -/
theorem image_round_constants :
    (Array.ofFn fun i : Fin 64 => imageWords[152 + i.val]!).map
      (fun word => UInt32.ofBitVec word) = EthLib.Cryptography.Hash.Sha256.K.toArray := by
  decide +kernel

theorem image_initial_hash :
    (Array.ofFn fun i : Fin 8 => imageWords[216 + i.val]!).map
      (fun word => UInt32.ofBitVec word) = EthLib.Cryptography.Hash.Sha256.IV.toArray := by
  decide +kernel

end Crypto.ARM64
