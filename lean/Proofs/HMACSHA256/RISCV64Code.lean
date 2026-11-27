import Proofs.HMACSHA256.CodeLayout
import Proofs.HMACSHA256.LinkedCalls
import Models.RISCV64SHA256Decode
import Models.RISCV64HMACSHA256

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private def field (w lsb n : Nat) := (w >>> lsb) % 2 ^ n

/-- These three instructions extend the SHA-256 model. JAL stores the next
PC before moving to the linked callee. LUI sign-extends its 32-bit value. -/
def decodeAt (routine : Routine) (offset : Nat) : Option Op := do
  guard (offset % 2 = 0)
  let low ← routine.readLittle offset 2
  if low % 4 = 3 then
    let w ← routine.readLittle offset 4
    let d := BitVec.ofNat 5 (field w 7 5)
    match w % 128 with
    | 0x6f =>
      let disp := 2 * field w 21 10 + 2 ^ 11 * field w 20 1 +
        2 ^ 12 * field w 12 8 + 2 ^ 20 * field w 31 1
      return .jal d ((BitVec.ofNat 21 disp).signExtend 64)
    | 0x37 => return .lui d ((BitVec.ofNat 32 (field w 12 20 * 4096)).signExtend 64)
    | 0x33 =>
      if field w 25 7 = 0x20 ∧ field w 12 3 = 0 then
        return .sub d (BitVec.ofNat 5 (field w 15 5)) (BitVec.ofNat 5 (field w 20 5))
      else pure ()
    | _ => pure ()
  return .scalar (← Crypto.RISCV64.decodeBytes (fun i => routine.image[i]!.toBitVec) offset)

def decodeSite (routine : Routine) (offset : Nat) : Option (Nat × Flow) := do
  let op ← decodeAt routine offset
  let target (disp : Addr) := routine.offset + offset + disp.toInt
  let flow ← match op with
    | .scalar ⟨.branch _ _ _ d, _⟩ => some (.branch (target d))
    | .scalar ⟨.jump d, _⟩ => some (.jump (target d))
    | .scalar ⟨.ret, _⟩ => some .ret
    | .jal 1#5 d => some (.call (target d))
    | .jal .. => none
    | _ => some .next
  return (op.width, flow)

theorem entry_layout :
    checkedLayout entry (decodeSite entry) [(0x42, key.offset), (0x10c, finish.offset)] 0x12e =
      true := by decide +kernel

theorem key_layout :
    checkedLayout key (decodeSite key) [(0x84, sha256Offset)] 0xa4 = true := by decide +kernel

theorem finish_layout :
    checkedLayout finish (decodeSite finish) [(0x22, sha256Offset), (0xb8, sha256Offset)] 0xd8 =
      true := by decide +kernel

end Crypto.HMACSHA256.RISCV64
