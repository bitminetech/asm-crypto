import Proofs.X86_64.WordExecution
import Proofs.ARM64.ImportedMemory

/-! Both ISA models store bytes in little-endian order. Transport the existing
word-array lemmas along a byte-value projection. Permissions and CPU states
are outside this projection. -/
namespace Crypto.X86_64
open X86

def byteView (m : Mem) : Arm64.Memory := Arm64.Memory.ofFn m.read

@[simp] theorem byteView_read (m : Mem) (a : Val) : (byteView m).read8 a = m.read a := rfl

theorem byteView_write (m : Mem) (a : Val) (b : BitVec 8) :
    byteView (m.write a b) = (byteView m).write8 a b := by
  apply congrArg Arm64.Memory.mk
  funext p
  by_cases h : p = a <;> simp [byteView, Arm64.Memory.ofFn,
    Arm64.Memory.rawPerm, h, Mem.read_write_ne]

private theorem read_le (a b c d : BitVec 8) :
    (((((d.setWidth 32 <<< 8) ||| c.setWidth 32) <<< 8 ||| b.setWidth 32) <<< 8) |||
      a.setWidth 32) = d ++ c ++ b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      BitVec.getLsbD_shiftLeft] <;> simp (config := { decide := true })

theorem byteView_read32 (m : Mem) (a : Val) :
    (m.readSize .d a).setWidth 32 = (byteView m).read32 a := by
  simp [Mem.readSize, Size.bytes, Mem.readN, Arm64.Memory.read32, BitVec.add_assoc, read_le]

private theorem store_byte (w : Word) (i : Nat) :
    (((w.setWidth 64) >>> i).setWidth 8) = w.extractLsb' i 8 := by
  rw [← BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem byteView_write32 (m : Mem) (a : Val) (w : Word) :
    byteView (m.writeSize .d a (w.setWidth 64)) = (byteView m).write32 a w := by
  simp [Mem.writeSize, Size.bytes, Mem.writeN, byteView_write, Arm64.Memory.write32,
    BitVec.add_assoc, ← BitVec.shiftRight_add, store_byte, BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32)]

def stackWords (s : Cpu) : Vector Word 64 :=
  Crypto.ARM64.Imported.wordVector 64 (byteView s.mem) (s.regs.get .rsp)

end Crypto.X86_64
