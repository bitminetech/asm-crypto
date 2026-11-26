import Proofs.X86_64.Memory

namespace Crypto.X86_64
open X86

private theorem little_endian (a b c d e f g h : BitVec 8) :
    ((((((((h.setWidth 64 <<< 8 ||| g.setWidth 64) <<< 8 ||| f.setWidth 64)
      <<< 8 ||| e.setWidth 64) <<< 8 ||| d.setWidth 64) <<< 8 ||| c.setWidth 64)
      <<< 8 ||| b.setWidth 64) <<< 8) ||| a.setWidth 64) = h ++ g ++ f ++ e ++ d ++ c ++ b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append] <;> simp (config := { decide := true })

theorem byteView_read64 (m : Mem) (a : Val) : m.readSize .q a = (byteView m).read64 a := by
  simp [Mem.readSize, Size.bytes, Mem.readN, Arm64.Memory.read64, BitVec.add_assoc, little_endian]

theorem byteView_write64 (m : Mem) (a v : Val) :
    byteView (m.writeSize .q a v) = (byteView m).write64 a v := by
  have byte (k : Nat) : (v >>> k).extractLsb' 0 8 = v.extractLsb' k 8 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64), BitVec.setWidth_ushiftRight_eq_extractLsb]
  simp [Mem.writeSize, Size.bytes, Mem.writeN, byteView_write, Arm64.Memory.write64,
    BitVec.add_assoc, ← BitVec.shiftRight_add, byte,
    BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

theorem read64_write64 (m : Mem) (a v : Val) : (m.writeSize .q a v).readSize .q a = v := by
  rw [byteView_read64, byteView_write64]
  simp (config := { decide := true }) [Arm64.Memory.read64, Arm64.Memory.write64,
    Crypto.ARM64.Imported.read8_write8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  repeat' first | rw [BitVec.getLsbD_append] | rw [BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp (config := { decide := true })

end Crypto.X86_64
