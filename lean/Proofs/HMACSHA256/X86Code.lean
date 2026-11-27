import Proofs.HMACSHA256.CodeLayout
import Proofs.HMACSHA256.LinkedCalls
import Models.X86SHA256Decode

namespace Crypto.HMACSHA256.X86_64

open X86

/-- Extend the scalar SHA-256 decoder with the exact direct-call, branch and
repeat-prefix forms used by the linked HMAC routines. -/
def decodeAt (routine : Routine) (offset : Nat) : Option Instr := do
  let opcode ← routine.readLittle offset 1
  match opcode with
  | 0xe8 =>
    let disp ← routine.readLittle (offset + 1) 4
    return ⟨.call (.rel ((BitVec.ofNat 32 disp).signExtend 64)), 5⟩
  | 0x77 =>
    let disp ← routine.readLittle (offset + 1) 1
    return ⟨.jcc .a ((BitVec.ofNat 8 disp).signExtend 64), 2⟩
  | 0xf3 =>
    if routine.readLittle (offset + 1) 1 = some 0xa4 then
      return ⟨.repstrop .rep .movs .b, 2⟩
    else
      guard (routine.readLittle (offset + 1) 2 == some 0xab48)
      return ⟨.repstrop .rep .stos .q, 3⟩
  | 0x0f =>
    if routine.readLittle (offset + 1) 1 = some 0x82 then
      let disp ← routine.readLittle (offset + 2) 4
      return ⟨.jcc .b ((BitVec.ofNat 32 disp).signExtend 64), 6⟩
    else Crypto.X86_64.decodeAt routine.image offset
  | _ => Crypto.X86_64.decodeAt routine.image offset

def decodeSite (routine : Routine) (offset : Nat) : Option (Nat × Flow) := do
  let instr ← decodeAt routine offset
  let target (disp : Val) := routine.offset + offset + instr.len + disp.toInt
  let flow ← match instr.op with
    | .jmp (.rel d) => some (.jump (target d))
    | .jcc _ d => some (.branch (target d))
    | .call (.rel d) => some (.call (target d))
    | .ret => some .ret
    | .repstrop .. => some .repeat
    | .mov .. | .lea .. | .push .. | .pop .. | .bin .. => some .next
    | _ => none
  return (instr.len, flow)

theorem entry_layout :
    checkedLayout entry (decodeSite entry) [(0x40, key.offset), (0xf6, finish.offset)] 0x10e =
      true := by decide +kernel

theorem key_layout :
    checkedLayout key (decodeSite key) [(0x3f, sha256Offset)] 0x52 = true := by decide +kernel

theorem finish_layout :
    checkedLayout finish (decodeSite finish) [(0x1c, sha256Offset), (0xaa, sha256Offset)] 0xc0 =
      true := by decide +kernel

end Crypto.HMACSHA256.X86_64
