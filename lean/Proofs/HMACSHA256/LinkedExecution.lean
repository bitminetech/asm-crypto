import Proofs.HMACSHA256.ARM64Code
import Proofs.HMACSHA256.X86Code
import Proofs.HMACSHA256.RISCV64Code
import Proofs.ARM64.ImportedFetchBinding

namespace Crypto.HMACSHA256

abbrev Address := BitVec 64

def Routine.Loaded (routine : Routine) (base : Address) (read : Address → BitVec 8) : Prop :=
  ∀ i, i < routine.image.size → read (base + BitVec.ofNat 64 i) = routine.image[i]!.toBitVec

/-- Fetch only complete instructions and check the fetched bytes against the
linked image. Each ISA uses its decoder and its machine's actual fetch address. -/
def Routine.fetch {α : Type} (routine : Routine) (decode : Nat → Option α) (width : α → Nat)
    (base pc : Address) (read : Address → BitVec 8) : Option α := do
  let off := (pc - base).toNat
  guard (off < routine.image.size)
  let ins ← decode off
  guard (0 < width ins ∧ off + width ins ≤ routine.image.size)
  guard ((List.range (width ins)).all fun j =>
    read (pc + BitVec.ofNat 64 j) == routine.image[off + j]!.toBitVec)
  return ins

theorem Routine.fetch_at {α : Type} (routine : Routine) (decode : Nat → Option α) (width : α → Nat)
    (base pc : Address) (read : Address → BitVec 8) (off : Nat) (ins : α)
    (loaded : routine.Loaded base read) (atPC : pc = base + BitVec.ofNat 64 off)
    (addressable : off < 2 ^ 64) (decoded : decode off = some ins)
    (positive : 0 < width ins) (within : off + width ins ≤ routine.image.size) :
    routine.fetch decode width base pc read = some ins := by
  have offset : (pc - base).toNat = off := by
    rw [atPC, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt addressable]
  have start : off < routine.image.size := by omega
  have bytes : ∀ j, j < width ins →
      read (pc + BitVec.ofNat 64 j) = routine.image[off + j]!.toBitVec := by
    intro j hj
    rw [atPC, BitVec.add_assoc, ← BitVec.ofNat_add, loaded _ (by omega)]
  unfold Routine.fetch
  rw [offset]
  simp [guard, start, decoded, positive, within]
  rw [if_pos bytes]
  rfl

namespace ARM64

theorem fetch_at (routine : Routine) (base : Address) (s : Arm64.State) (off : Nat)
    (ins : Arm64.Instr) (loaded : (programAt routine base).CodeLoaded s.mem)
    (pc : s.pc = base + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt routine off = some ins) :
    (programAt routine base).fetchMem s.mem s.pc = some ins := by
  apply Crypto.ARM64.Imported.loaded_fetch_of_fetch loaded
  have delta : (s.pc - base).toNat = off := by
    rw [pc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt addressable]
  simpa [Arm64.Program.fetch, Arm64.Program.externAt?, Arm64.Program.hookAtOff?,
    Arm64.Program.ofSvc, programAt, decodeAt, delta] using decoded

theorem step_at (routine : Routine) (base : Address) (s : Arm64.State) (off : Nat)
    (ins : Arm64.Instr) (loaded : (programAt routine base).CodeLoaded s.mem)
    (pc : s.pc = base + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt routine off = some ins) (running : s.status = .Running) :
    Arm64.Step (programAt routine base) s ((programAt routine base).evalInst ins s) :=
  Arm64.Step.exec running (fetch_at routine base s off ins loaded pc addressable decoded)

end ARM64

namespace X86_64

def stepLoaded (routine : Routine) (base : Address) (s : X86.Cpu) : Option X86.Cpu := do
  guard (!s.stopped && X86.canonical s.rip)
  let ins ← routine.fetch (decodeAt routine) X86.Instr.len base s.rip s.mem.read
  return X86.step ins s

theorem step_at (routine : Routine) (base : Address) (s : X86.Cpu) (off : Nat)
    (ins : X86.Instr) (loaded : routine.Loaded base s.mem.read)
    (pc : s.rip = base + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt routine off = some ins) (positive : 0 < ins.len)
    (within : off + ins.len ≤ routine.image.size) (live : s.ms = none)
    (validAddress : X86.canonical s.rip = true) :
    stepLoaded routine base s = some (X86.step ins s) := by
  have fetched := routine.fetch_at _ _ _ _ _ _ _ loaded pc addressable decoded positive within
  simp [stepLoaded, guard, X86.Cpu.stopped, live, validAddress, fetched]

end X86_64

namespace RISCV64

open Crypto.RISCV64

def Op.accessesOK (op : Op) (s : CPU) : Bool :=
  let allowed : Access → Bool
    | .fetch p width => s.mem.canExec p width
    | .read p width => p.toNat % width.bytes == 0 && s.mem.canRead p width.bytes
    | .write p width => p.toNat % width.bytes == 0 && s.mem.canWrite p width.bytes
  match op with
  | .scalar i => (i.op.accesses s).all allowed
  | _ => true

def stepLoaded (routine : Routine) (base : Address) (s : CPU) : Option CPU := do
  let op ← routine.fetch (decodeAt routine) Op.width base s.pc s.mem.read8
  guard (s.pc.toNat % 2 == 0 && s.mem.canExec s.pc op.width && op.accessesOK s)
  return op.step s

theorem step_at (routine : Routine) (base : Address) (s : CPU) (off : Nat)
    (op : Op) (loaded : routine.Loaded base s.mem.read8)
    (pc : s.pc = base + BitVec.ofNat 64 off) (addressable : off < 2 ^ 64)
    (decoded : decodeAt routine off = some op) (positive : 0 < op.width)
    (within : off + op.width ≤ routine.image.size) (aligned : s.pc.toNat % 2 = 0)
    (executable : s.mem.canExec s.pc op.width = true) (allowed : op.accessesOK s = true) :
    stepLoaded routine base s = some (op.step s) := by
  have fetched := routine.fetch_at _ _ _ _ _ _ _ loaded pc addressable decoded positive within
  simp [stepLoaded, guard, aligned, executable, allowed, fetched]

end RISCV64

end Crypto.HMACSHA256
