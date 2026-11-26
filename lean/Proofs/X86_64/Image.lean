import Models.X86SHA256Decode
import spec.Preprocessing

namespace Crypto.X86_64
open X86

/-- Walk the 200 instructions from the entry. A gap, invalid length, missing
instruction or accidental decoding of alignment or constants fails the walk. -/
def layout (off : Nat) : Nat → Option (List (Nat × Instr))
  | 0 => if off = codeEnd then some [] else none
  | n+1 => do
    guard (off < codeEnd)
    let i ← decodeAt image off
    return (off, i) :: (← layout (off + i.len) n)

private def closedEdge (starts : List Nat) (entry : Nat × Instr) : Bool :=
  let (pc, i) := entry
  let next := pc + i.len
  let jump := fun (disp : Val) => starts.contains ((BitVec.ofNat 64 next + disp).toNat)
  match i.op with
  | .ret => pc == 0x384
  | .jmp (.rel disp) => jump disp
  | .jcc _ disp => jump disp && starts.contains next
  | .mov .. | .movx .. | .lea .. | .push .. | .pop .. | .bswap ..
  | .rot .. | .shift .. | .bin .. | .un .. => starts.contains next
  | _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem closed_control_flow :
    ((layout 0 200).map fun code => code.all (closedEdge (code.map Prod.fst))) = some true := by
  decide +kernel

def imageWord (off : Nat) : BitVec 32 :=
  image[off + 3]!.toBitVec ++ image[off + 2]!.toBitVec ++
  image[off + 1]!.toBitVec ++ image[off]!.toBitVec

theorem image_constants :
    Vector.ofFn (fun i : Fin 64 => imageWord (0x390 + 4 * i.val)) = SHS.SHA256.K ∧
    Vector.ofFn (fun i : Fin 8 => imageWord (0x490 + 4 * i.val)) = SHS.SHA256.H0_256 := by
  decide +kernel

end Crypto.X86_64
