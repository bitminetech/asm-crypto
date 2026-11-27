import Proofs.HMACSHA256.ARM64Code
import Proofs.ARM64.Decode

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64 (imageWords)

private def addressRegisters : Arm64.AddrMode → List Arm64.Reg
  | .Offset r _ | .UnscaledOffset r _ | .PreIndex r _ | .PostIndex r _ => [r]
  | .RegOffset r i .. => [r, i]

private def avoidsPlatformRegister (i : Arm64.Instr) : Bool :=
  let registers := match i with
    | .b .. | .bl .. | .bCond .. => some []
    | .adr _ d _ | .moveWide _ _ d .. | .cbz _ _ d _ | .ret d => some [d]
    | .addSubImm _ _ d n .. | .logicalImm _ _ d n _ | .bitfield _ _ d n .. |
      .dataProc1 _ _ d n => some [d, n]
    | .extr _ d n m _ | .logicalShift _ _ d n m .. | .addSubShift _ _ d n m .. |
      .addSubExt _ _ d n m .. => some [d, n, m]
    | .dataProc3 _ _ d n m a => some [d, n, m, a]
    | .ldr _ _ _ t address | .str _ t address => some (t :: addressRegisters address)
    | .ldp _ _ t u address | .stp _ t u address => some (t :: u :: addressRegisters address)
    | _ => none
  match registers with
  | none => false
  | some regs => regs.all (· != Arm64.Reg.x18)

private def avoidsX18 (routine : Routine) : Bool :=
  match scan (decodeSite routine) routine.image.size 0 routine.image.size with
  | none => false
  | some sites =>
    sites.all fun site => ((decodeAt routine site.offset).map avoidsPlatformRegister).getD false

/-- The decoded HMAC bodies and linked SHA-256 text have no operand using
the platform register. The check recognizes the scalar instruction forms,
including base, index and writeback registers in memory operands. -/
theorem linked_code_avoids_x18 :
    [entry, key, finish].all avoidsX18 = true ∧
      (imageWords.toList.take 151).all (fun word =>
        ((Arm64.decode word).map avoidsPlatformRegister).getD false) = true := by
  decide +kernel

end Crypto.HMACSHA256.ARM64
