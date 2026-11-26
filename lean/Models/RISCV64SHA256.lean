import Arm64.Trusted.ISA.Memory

/-! RV64GC instruction subset used by the scalar SHA-256 routine. Register
arithmetic wraps at XLEN, W-form instructions sign extend their 32-bit result,
and memory is little-endian. This semantics describes successful instructions
over byte memory. Mapping it to a platform that enforces permissions and
handles faults requires a separate refinement. -/
namespace Crypto.RISCV64

abbrev Addr := BitVec 64
abbrev Word := BitVec 32
abbrev Reg := BitVec 5
abbrev Memory := Arm64.Memory

inductive Width
  | byte | word | double
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .byte => 1
  | .word => 4
  | .double => 8

inductive Branch
  | eq | ne | ltu | geu
  deriving DecidableEq, Repr

inductive Op
  | add (dst lhs rhs : Reg)
  | addw (dst lhs rhs : Reg)
  | and (dst lhs rhs : Reg)
  | or (dst lhs rhs : Reg)
  | xor (dst lhs rhs : Reg)
  | addi (dst src : Reg) (imm : Addr)
  | andi (dst src : Reg) (imm : Addr)
  | slli (dst src : Reg) (count : BitVec 6)
  | srli (dst src : Reg) (count : BitVec 6)
  | slliw (dst src : Reg) (count : BitVec 5)
  | srliw (dst src : Reg) (count : BitVec 5)
  | auipc (dst : Reg) (imm : Addr)
  | load (width : Width) (dst base : Reg) (imm : Addr)
  | store (width : Width) (src base : Reg) (imm : Addr)
  | branch (test : Branch) (lhs rhs : Reg) (imm : Addr)
  | jump (imm : Addr)
  | ret
  deriving DecidableEq, Repr

structure Instruction where
  op : Op
  bytes : Nat
  deriving DecidableEq, Repr

structure CPU where
  pc : Addr
  regs : Vector Addr 32
  mem : Memory

def CPU.reg (s : CPU) (r : Reg) : Addr := if r = 0 then 0 else s.regs[r.toNat]

def CPU.put (s : CPU) (r : Reg) (v : Addr) : CPU :=
  { s with regs := s.regs.set r.toNat v r.isLt }

@[simp] theorem reg_put (s : CPU) (d r : Reg) (v : Addr) :
    (s.put d v).reg r = if r = 0 then 0 else if r = d then v else s.reg r := by
  unfold CPU.reg CPU.put
  simp only [Vector.getElem_set, BitVec.toNat_inj]
  by_cases e : r = d
  · subst d
    simp
  · rw [if_neg e, if_neg (Ne.symm e)]
    split <;> simp_all

@[simp] theorem pc_put (s : CPU) (d : Reg) (v : Addr) : (s.put d v).pc = s.pc := rfl

@[simp] theorem memory_put (s : CPU) (d : Reg) (v : Addr) : (s.put d v).mem = s.mem := rfl

@[simp] theorem reg_zero (s : CPU) : s.reg 0 = 0 := by simp [CPU.reg]

def CPU.write (s : CPU) (m : Memory) : CPU := { s with mem := m }

@[simp] theorem reg_write (s : CPU) (m : Memory) (r : Reg) :
    (s.write m).reg r = s.reg r := rfl

@[simp] theorem pc_write (s : CPU) (m : Memory) : (s.write m).pc = s.pc := rfl

@[simp] theorem memory_write (s : CPU) (m : Memory) : (s.write m).mem = m := rfl

def CPU.advance (s : CPU) (bytes : Nat) : CPU :=
  { s with pc := s.pc + BitVec.ofNat 64 bytes }

@[simp] theorem reg_advance (s : CPU) (n : Nat) (r : Reg) :
    (s.advance n).reg r = s.reg r := by rfl

@[simp] theorem pc_advance (s : CPU) (n : Nat) :
    (s.advance n).pc = s.pc + BitVec.ofNat 64 n := rfl

@[simp] theorem memory_advance (s : CPU) (n : Nat) : (s.advance n).mem = s.mem := rfl

inductive Access
  | fetch (address : Addr) (bytes : Nat)
  | read (address : Addr) (width : Width)
  | write (address : Addr) (width : Width)
  deriving DecidableEq, Repr

def Op.accesses (i : Op) (s : CPU) : List Access :=
  match i with
  | .load w _ base imm => [.read (s.reg base + imm) w]
  | .store w _ base imm => [.write (s.reg base + imm) w]
  | _ => []

def Width.load (w : Width) (m : Memory) (base : Addr) : Addr :=
  match w with
  | .byte => (m.read8 base).zeroExtend 64
  | .word => (m.read32 base).signExtend 64
  | .double => m.read64 base

def Width.store (w : Width) (m : Memory) (base : Addr) (v : Addr) : Memory :=
  match w with
  | .byte => m.write8 base (v.setWidth 8)
  | .word => m.write32 base (v.setWidth 32)
  | .double => m.write64 base v

def Branch.taken (b : Branch) (lhs rhs : Addr) : Bool :=
  match b with
  | .eq => lhs == rhs
  | .ne => lhs != rhs
  | .ltu => lhs.ult rhs
  | .geu => !lhs.ult rhs

def Instruction.step (i : Instruction) (s : CPU) : CPU :=
  let next := s.advance i.bytes
  match i.op with
  | .add d x y => next.put d (s.reg x + s.reg y)
  | .addw d x y => next.put d (((s.reg x).setWidth 32 + (s.reg y).setWidth 32).signExtend 64)
  | .and d x y => next.put d (s.reg x &&& s.reg y)
  | .or d x y => next.put d (s.reg x ||| s.reg y)
  | .xor d x y => next.put d (s.reg x ^^^ s.reg y)
  | .addi d x imm => next.put d (s.reg x + imm)
  | .andi d x imm => next.put d (s.reg x &&& imm)
  | .slli d x n => next.put d (s.reg x <<< n.toNat)
  | .srli d x n => next.put d (s.reg x >>> n.toNat)
  | .slliw d x n => next.put d (((s.reg x).setWidth 32 <<< n.toNat).signExtend 64)
  | .srliw d x n => next.put d (((s.reg x).setWidth 32 >>> n.toNat).signExtend 64)
  | .auipc d imm => next.put d (s.pc + imm)
  | .load w d base imm => next.put d (w.load s.mem (s.reg base + imm))
  | .store w r base imm => next.write (w.store s.mem (s.reg base + imm) (s.reg r))
  | .branch test x y imm => if test.taken (s.reg x) (s.reg y) then
      { s with pc := s.pc + imm } else next
  | .jump imm => { s with pc := s.pc + imm }
  | .ret => { s with pc := s.reg 1 &&& ~~~(1 : Addr) }

def Instruction.observations (i : Instruction) (s : CPU) : List Access :=
  .fetch s.pc i.bytes :: i.op.accesses s

def run (code : List Instruction) (s : CPU) : CPU :=
  code.foldl (fun st i => i.step st) s

end Crypto.RISCV64
