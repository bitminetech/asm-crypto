import Models.RISCV64SHA256

/-! Additional successful-instruction semantics needed by the scalar HMAC
routines. They share the RV64 machine state, register and memory definitions
used by the SHA-256 baseline. -/
namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

inductive Op where
  | scalar (instr : Instruction)
  | sub (dst lhs rhs : Reg)
  | lui (dst : Reg) (value : Addr)
  | jal (dst : Reg) (relative : Addr)
  deriving DecidableEq

def Op.width : Op → Nat
  | .scalar instr => instr.bytes
  | _ => 4

def Op.step (op : Op) (s : CPU) : CPU :=
  match op with
  | .scalar instr => instr.step s
  | .sub dst x y => (s.advance 4).put dst (s.reg x - s.reg y)
  | .lui dst imm => (s.advance 4).put dst imm
  | .jal dst rel => { s.put dst (s.pc + 4#64) with pc := s.pc + rel }

end Crypto.HMACSHA256.RISCV64
