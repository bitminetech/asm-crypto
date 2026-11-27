import Proofs.HMACSHA256.CodeLayout
import Models.ARM64

namespace Crypto.HMACSHA256.ARM64

def programAt (routine : Routine) (base : BitVec 64) : Arm64.Program :=
  { Arm64.Program.ofSvc Arm64.noSyscalls with
    base := base
    code := routine.image.toList.map UInt8.toBitVec }

def decodeAt (routine : Routine) (offset : Nat) : Option Arm64.Instr :=
  ((programAt routine 0#64).readWordOff offset).bind Arm64.decode

def decodeSite (routine : Routine) (offset : Nat) : Option (Nat × Flow) := do
  let target (disp : BitVec 64) := routine.offset + offset + disp.toInt
  let flow ← match ← decodeAt routine offset with
    | .b d => some (.jump (target d))
    | .bCond _ d | .cbz _ _ _ d => some (.branch (target d))
    | .bl d => some (.call (target d))
    | .ret .lr => some .ret
    | .addSubImm .. | .addSubShift .. | .moveWide .. | .logicalImm .. |
      .logicalShift .. | .dataProc3 .. | .ldr .. | .str .. | .ldp .. | .stp .. => some .next
    | _ => none
  return (4, flow)

theorem entry_layout :
    checkedLayout entry (decodeSite entry) [(0x50, key.offset), (0x10c, finish.offset)] 0x12c =
      true := by decide +kernel

theorem key_layout :
    checkedLayout key (decodeSite key) [(0x70, sha256Offset)] 0x8c = true := by decide +kernel

theorem finish_layout :
    checkedLayout finish (decodeSite finish) [(0x28, sha256Offset), (0x9c, sha256Offset)] 0xb8 =
      true := by decide +kernel

end Crypto.HMACSHA256.ARM64
