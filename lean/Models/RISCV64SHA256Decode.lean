import Models.RISCV64SHA256
import Models.RISCV64SHA256Image

namespace Crypto.RISCV64

private def field (w : Nat) (lsb n : Nat) : Nat := (w >>> lsb) &&& (2^n - 1)
private def signed (n raw : Nat) : Addr := (BitVec.ofNat n raw).signExtend 64
private def reg (n : Nat) : Reg := BitVec.ofNat 5 n

private def decode32 (w : Nat) : Option Op := do
  let d := reg (field w 7 5)
  let x := reg (field w 15 5)
  let y := reg (field w 20 5)
  let f := field w 12 3
  let imm := signed 12 (field w 20 12)
  match field w 0 7 with
  | 0x03 =>
    match f with
    | 2 => return .load .word d x imm
    | 3 => return .load .double d x imm
    | 4 => return .load .byte d x imm
    | _ => none
  | 0x23 =>
    let offset := signed 12 (field w 25 7 * 32 + field w 7 5)
    match f with
    | 0 => return .store .byte y x offset
    | 2 => return .store .word y x offset
    | 3 => return .store .double y x offset
    | _ => none
  | 0x13 =>
    match f with
    | 0 => return .addi d x imm
    | 7 => return .andi d x imm
    | 1 | 5 =>
      guard (field w 26 6 = 0)
      let count := BitVec.ofNat 6 (field w 20 6)
      return if f = 1 then .slli d x count else .srli d x count
    | _ => none
  | 0x1b =>
    guard (field w 25 7 = 0)
    match f with
    | 1 => return .slliw d x y
    | 5 => return .srliw d x y
    | _ => none
  | 0x33 =>
    guard (field w 25 7 = 0)
    match f with
    | 0 => return .add d x y
    | 4 => return .xor d x y
    | 6 => return .or d x y
    | 7 => return .and d x y
    | _ => none
  | 0x3b =>
    guard (field w 25 7 = 0 ∧ f = 0)
    return .addw d x y
  | 0x17 => return .auipc d (signed 32 (field w 12 20 * 4096))
  | 0x63 =>
    let offset := signed 13
      (field w 31 1 * 4096 + field w 7 1 * 2048 + field w 25 6 * 32 + field w 8 4 * 2)
    match f with
    | 0 => return .branch .eq x y offset
    | 1 => return .branch .ne x y offset
    | 6 => return .branch .ltu x y offset
    | 7 => return .branch .geu x y offset
    | _ => none
  | _ => none

private def decode16 (w : Nat) : Option Op := do
  let d := reg (field w 7 5)
  let y := reg (field w 2 5)
  let short := signed 6 (field w 12 1 * 32 + field w 2 5)
  match field w 0 2, field w 13 3 with
  | 0, 0 =>
    let imm := field w 7 4 * 64 + field w 11 2 * 16 + field w 5 1 * 8 + field w 6 1 * 4
    guard (imm ≠ 0)
    return .addi (reg (8 + field w 2 3)) 2 (BitVec.ofNat 64 imm)
  | 1, 0 =>
    guard (d ≠ 0 ∨ short = 0)
    return .addi d d short
  | 1, 2 =>
    guard (d ≠ 0)
    return .addi d 0 short
  | 1, 3 =>
    guard (d = 2)
    let imm := signed 10
      (field w 12 1 * 512 + field w 3 2 * 128 + field w 5 1 * 64 +
        field w 2 1 * 32 + field w 6 1 * 16)
    guard (imm ≠ 0)
    return .addi 2 2 imm
  | 1, 5 =>
    let imm := signed 12
      (field w 12 1 * 2048 + field w 8 1 * 1024 + field w 9 2 * 256 +
        field w 6 1 * 128 + field w 7 1 * 64 + field w 2 1 * 32 +
        field w 11 1 * 16 + field w 3 3 * 2)
    return .jump imm
  | 1, 6 | 1, 7 =>
    let imm := signed 9
      (field w 12 1 * 256 + field w 5 2 * 64 + field w 2 1 * 32 +
        field w 10 2 * 8 + field w 3 2 * 2)
    return .branch (if field w 13 3 = 6 then .eq else .ne) (reg (8 + field w 7 3)) 0 imm
  | 2, 0 =>
    guard (d ≠ 0)
    return .slli d d (BitVec.ofNat 6 (field w 12 1 * 32 + field w 2 5))
  | 2, 3 =>
    guard (d ≠ 0)
    let imm := field w 2 3 * 64 + field w 12 1 * 32 + field w 5 2 * 8
    return .load .double d 2 (BitVec.ofNat 64 imm)
  | 2, 4 =>
    if w = 0x8082 then return .ret else
      guard (d ≠ 0 ∧ y ≠ 0)
      if field w 12 1 = 0 then return .add d 0 y else return .add d d y
  | 2, 7 =>
    let imm := field w 7 3 * 64 + field w 10 3 * 8
    return .store .double y 2 (BitVec.ofNat 64 imm)
  | _, _ => none

def littleWord (byte : Nat → BitVec 8) (off : Nat) : Word :=
  byte (off+3) ++ byte (off+2) ++ byte (off+1) ++ byte off

def imageWord : Nat → Word := littleWord fun i => image[i]!.toBitVec

/-- Decode only complete instructions in the function body. -/
def decodeBytes (byte : Nat → BitVec 8) (off : Nat) : Option Instruction := do
  guard (off % 2 = 0 ∧ off + 2 ≤ codeEnd)
  let low := (byte off).toNat + 256 * (byte (off+1)).toNat
  if low % 4 = 3 then
    guard (off + 4 ≤ codeEnd)
    return ⟨← decode32 (littleWord byte off).toNat, 4⟩
  else
    return ⟨← decode16 low, 2⟩

def decodeAt : Nat → Option Instruction := decodeBytes fun i => image[i]!.toBitVec

def decodeSeq (off : Nat) : Nat → Option (List Instruction)
  | 0 => some []
  | n + 1 => (decodeAt off).bind fun i =>
    (decodeSeq (off + i.bytes) n).map (List.cons i)

end Crypto.RISCV64
