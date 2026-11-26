import Models.RISCV64SHA256Decode

namespace Crypto.RISCV64

def Access.permitted (m : Memory) : Access → Bool
  | .fetch address bytes => address.toNat % 2 == 0 && m.canExec address bytes
  | .read address w => address.toNat % w.bytes == 0 && m.canRead address w.bytes
  | .write address w => address.toNat % w.bytes == 0 && m.canWrite address w.bytes

def fetched (base : Addr) (s : CPU) : Option Instruction :=
  decodeBytes (fun j => s.mem.read8 (base + BitVec.ofNat 64 j)) (s.pc - base).toNat

/-- Execute one instruction fetched from memory. Refuse unaligned accesses and
memory accesses outside the modeled permissions. A return retires once and
reports that it was the first one, so the caller's code is never fetched. -/
def checkedStep (base : Addr) (s : CPU) : Option (CPU × List Access × Bool) :=
  match fetched base s with
  | none => none
  | some i =>
    let trace := i.observations s
    if trace.all (Access.permitted s.mem) then
      some (i.step s, trace, i.op == .ret)
    else none

def runUntilReturn (base : Addr) (s : CPU) (fuel : Nat) : Option CPU :=
  match fuel with
  | 0 => none
  | n + 1 => do
    let (out, _, returned) ← checkedStep base s
    if returned then some out else runUntilReturn base out n

end Crypto.RISCV64
