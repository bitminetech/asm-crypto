import Models.HMACSHA256Image

/-! Relative call targets for the recorded Linux images. The equality checks
bind the two helper calls and the three calls to the baseline SHA-256 symbol. -/
namespace Crypto.HMACSHA256

def Routine.readLittle (routine : Routine) (offset width : Nat) : Option Nat :=
  (List.range width).foldlM (fun value i => do
    let byte ← routine.image[offset + i]?
    return value + byte.toNat * 256 ^ i) 0

def signedImmediate (width value : Nat) : Int :=
  if value < 2 ^ (width - 1) then Int.ofNat value else Int.ofNat value - 2 ^ width

def arm64CallTarget (routine : Routine) (offset : Nat) : Option Int := do
  let word ← routine.readLittle offset 4
  guard (offset % 4 == 0 && word >>> 26 == 0x25)
  return routine.offset + offset + 4 * signedImmediate 26 (word % 2 ^ 26)

def x86CallTarget (routine : Routine) (offset : Nat) : Option Int := do
  let opcode ← routine.image[offset]?
  guard (opcode == 0xe8)
  let displacement ← routine.readLittle (offset + 1) 4
  return routine.offset + offset + 5 + signedImmediate 32 displacement

def rv64CallTarget (routine : Routine) (offset : Nat) : Option Int := do
  let word ← routine.readLittle offset 4
  -- The linker relaxed each recorded call to JAL with destination x1.
  guard (offset % 2 == 0 && word % 2 ^ 12 == 0xef)
  let displacement := 2 * ((word >>> 21) % 2 ^ 10) + 2 ^ 11 * ((word >>> 20) % 2) +
    2 ^ 12 * ((word >>> 12) % 2 ^ 8) + 2 ^ 20 * (word >>> 31)
  return routine.offset + offset + signedImmediate 21 displacement

theorem ARM64.linked_calls :
    arm64CallTarget ARM64.entry 0x50 = some ARM64.key.offset ∧
    arm64CallTarget ARM64.entry 0x10c = some ARM64.finish.offset ∧
    arm64CallTarget ARM64.key 0x70 = some ARM64.sha256Offset ∧
    arm64CallTarget ARM64.finish 0x28 = some ARM64.sha256Offset ∧
    arm64CallTarget ARM64.finish 0x9c = some ARM64.sha256Offset := by
  decide +kernel

theorem X86_64.linked_calls :
    x86CallTarget X86_64.entry 0x40 = some X86_64.key.offset ∧
    x86CallTarget X86_64.entry 0xf6 = some X86_64.finish.offset ∧
    x86CallTarget X86_64.key 0x3f = some X86_64.sha256Offset ∧
    x86CallTarget X86_64.finish 0x1c = some X86_64.sha256Offset ∧
    x86CallTarget X86_64.finish 0xaa = some X86_64.sha256Offset := by
  decide +kernel

theorem RISCV64.linked_calls :
    rv64CallTarget RISCV64.entry 0x42 = some RISCV64.key.offset ∧
    rv64CallTarget RISCV64.entry 0x10c = some RISCV64.finish.offset ∧
    rv64CallTarget RISCV64.key 0x84 = some RISCV64.sha256Offset ∧
    rv64CallTarget RISCV64.finish 0x22 = some RISCV64.sha256Offset ∧
    rv64CallTarget RISCV64.finish 0xb8 = some RISCV64.sha256Offset := by
  decide +kernel

end Crypto.HMACSHA256
