import Proofs.RISCV64.RoundLoop
import Proofs.RISCV64.LoadedExecution

namespace Crypto.RISCV64

def accessTrace : List Instruction → CPU → List Access
  | [], _ => []
  | i :: tail, s => i.observations s ++ accessTrace tail (i.step s)

theorem accessTrace_append (left right : List Instruction) (s : CPU) :
    accessTrace (left ++ right) s = accessTrace left s ++ accessTrace right (run left s) := by
  induction left generalizing s with
  | nil => rfl
  | cons i tail ih =>
    simp only [List.cons_append, accessTrace, List.append_assoc, ih]
    rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem round_public_accesses (s t : CPU) (pc : s.pc = t.pc)
    (stack : s.reg 2#5 = t.reg 2#5) (constantBase : s.reg 10#5 = t.reg 10#5)
    (index : s.reg 15#5 = t.reg 15#5) :
    accessTrace roundBody s = accessTrace roundBody t := by
  simp (config := { decide := true }) [accessTrace, Instruction.observations, Op.accesses,
    Instruction.step, roundBody, pc, stack, constantBase, index]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem expansion_public_accesses (s t : CPU) (pc : s.pc = t.pc)
    (stack : s.reg 2#5 = t.reg 2#5) (index : s.reg 15#5 = t.reg 15#5) :
    accessTrace expansionBody s = accessTrace expansionBody t := by
  simp (config := { decide := true }) [accessTrace, Instruction.observations, Op.accesses,
    Instruction.step, expansionBody, pc, stack, index]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem input_public_accesses (s t : CPU) (pc : s.pc = t.pc)
    (stack : s.reg 2#5 = t.reg 2#5) (payload : s.reg 12#5 = t.reg 12#5)
    (index : s.reg 15#5 = t.reg 15#5) :
    accessTrace inputWordBody s = accessTrace inputWordBody t := by
  simp (config := { decide := true }) [accessTrace, Instruction.observations, Op.accesses,
    Instruction.step, inputWordBody, pc, stack, payload, index]

end Crypto.RISCV64
