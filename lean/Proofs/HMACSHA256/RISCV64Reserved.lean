import Proofs.HMACSHA256.RISCV64Code
import Proofs.RISCV64.ABI

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private def Op.destination : Op → Option Reg
  | .scalar i => i.op.destination
  | .sub d .. | .lui d .. | .jal d .. => some d

private def preservesPointers (d : Option Reg) : Bool := d != some 3#5 && d != some 4#5

private def pointerSafe (routine : Routine) : Bool :=
  match scan (decodeSite routine) routine.image.size 0 routine.image.size with
  | none => false
  | some sites =>
    sites.all fun site => ((decodeAt routine site.offset).map
      (fun i => preservesPointers i.destination)).getD false

/-- Every instruction of the three recorded HMAC bodies leaves the global
and thread pointer registers alone. The SHA-256 call path provides the same
LP64D guarantee via `CallPath.untouched_regs`. -/
theorem linked_hmac_preserves_pointers :
    [entry, key, finish].all pointerSafe = true := by decide +kernel

theorem linked_sha_preserves_pointer {base : Addr} {s out : CPU} {data : ByteArray}
    (path : CallPath base s out data) {r : Reg} (pointer : r = 3#5 ∨ r = 4#5) :
    out.reg r = s.reg r := by
  apply path.untouched_regs
  rcases pointer with rfl | rfl <;> decide

end Crypto.HMACSHA256.RISCV64
