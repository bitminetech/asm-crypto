import Models.ARM64

namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- A closed computation in Lean's kernel over the unchanged imported decoder.
This establishes vocabulary coverage, not termination or functional correctness. -/
theorem all_instructions_decode :
    ((imageWords.toList.take 151).all fun word => (Arm64.decode word).isSome) = true := by
  decide +kernel

/-- Every instruction is an ordinary integer/branch/load/store instruction.
In particular there is no syscall, software call, atomic, cache maintenance,
SIMD/FP operation or indirect branch other than the final return. -/
def permittedInstruction : Arm64.Instr → Bool
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield ..
  | .extr .. | .b .. | .bCond .. | .cbz .. | .ret .. | .logicalShift ..
  | .addSubShift .. | .addSubExt .. | .dataProc1 .. | .ldr .. | .str ..
  | .ldp .. | .stp .. => true
  | _ => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem all_instructions_permitted :
    ((imageWords.toList.take 151).all fun word =>
      ((Arm64.decode word).map permittedInstruction).getD false) = true := by
  decide +kernel

end Crypto.ARM64.Imported
