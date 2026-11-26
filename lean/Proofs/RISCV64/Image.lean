import Models.RISCV64SHA256Decode
import spec.Preprocessing

namespace Crypto.RISCV64

theorem image_constants :
    Vector.ofFn (fun i : Fin 64 => imageWord (constantsOffset + 4 * i.val)) = SHS.SHA256.K ∧
    Vector.ofFn (fun i : Fin 8 => imageWord (initialHashOffset + 4 * i.val)) = SHS.SHA256.H0_256 := by
  decide +kernel

def ImageLoaded (base : Addr) (m : Memory) : Prop :=
  ∀ j, j < image.size → m.read8 (base + BitVec.ofNat 64 j) = image[j]!.toBitVec

theorem loaded_word (base : Addr) (m : Memory) (loaded : ImageLoaded base m)
    (off : Nat) (bound : off + 4 ≤ image.size) :
    m.read32 (base + BitVec.ofNat 64 off) = imageWord off := by
  have read (i : Nat) (h : i < 4) :
      m.read8 (base + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = image[off+i]!.toBitVec := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact loaded _ (by omega)
  unfold Arm64.Memory.read32 imageWord littleWord
  exact congrArg₂ BitVec.append
    (congrArg₂ BitVec.append (congrArg₂ BitVec.append (read 3 (by decide)) (read 2 (by decide)))
      (read 1 (by decide))) (read 0 (by decide))

end Crypto.RISCV64
