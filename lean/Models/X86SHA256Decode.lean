import Models.X86SHA256Image
import X86.Semantics

/-! Decoder for the legacy long-mode instruction forms used in the scalar
SHA-256 entry. The execution of each decoded operation is upstream X86.step.
Code ends at the first byte following RET. Alignment and tables are data. -/
namespace Crypto.X86_64
open X86

abbrev ByteReader := StateT Nat Option

private def byte (bytes : Array UInt8) : ByteReader Nat := do
  let pos ← get
  let some value := bytes[pos]? | failure
  set (pos + 1)
  return value.toNat

private def immediate (bytes : Array UInt8) (count : Nat) : ByteReader Val := do
  let mut v := 0
  for i in [:count] do
    v := v + (← byte bytes) * 256 ^ i
  return (BitVec.ofNat (8 * count) v).signExtend 64

private def reg (n : Nat) := GPR.ofIndex (Fin.ofNat 16 n)

private structure Fields where
  ext : Nat
  r : GPR
  rm : Operand

private def fields (bytes : Array UInt8) (rex : Nat) : ByteReader Fields := do
  let m ← byte bytes
  let mode := m / 64
  let ext := m / 8 % 8
  let r := reg (ext + (rex / 4 % 2) * 8)
  let rm := m % 8
  let b := rex % 2 * 8
  if mode == 3 then return ⟨ext, r, .reg (reg (rm + b))⟩
  if mode == 0 && rm == 5 then
    return ⟨ext, r, .mem { ripRel := true, disp := ← immediate bytes 4 }⟩
  let mut ea : Ea := { base := some (reg (rm + b)) }
  if rm == 4 then
    let sib ← byte bytes
    let idx := sib / 8 % 8 + rex / 2 % 2 * 8
    let scale := #[Scale.s1, .s2, .s4, .s8][sib / 64]!
    -- The no-base SIB form needs a mandatory disp32.
    guard (!(mode == 0 && sib % 8 == 5))
    ea := { base := some (reg (sib % 8 + b)), index := if idx == 4 then none else some (reg idx), scale }
  let disp ← immediate bytes (if mode == 1 then 1 else if mode == 2 then 4 else 0)
  return ⟨ext, r, .mem { ea with disp }⟩

/-- The accepted scalar forms map directly to the pinned upstream operations.
The type also supplies a finite case split for the machine-state frame. -/
inductive ScalarForm where
  | mov (sz : Size) (dst src : Operand)
  | zeroExtendByte (sz : Size) (dst : GPR) (src : Operand)
  | lea (sz : Size) (dst : GPR) (src : Ea)
  | push (src : GPR)
  | pop (dst : GPR)
  | bin (kind : BinKind) (sz : Size) (dst src : Operand)
  | count (increment : Bool) (sz : Size) (dst : Operand)
  | ror (sz : Size) (dst : Operand) (count : BitVec 8)
  | shl (sz : Size) (dst : Operand) (count : BitVec 8)
  | shr (sz : Size) (dst : Operand) (count : BitVec 8)
  | bswap (sz : Size) (dst : GPR)
  | jump (disp : Val)
  | branch (cc : Cc) (disp : Val)
  | ret

def ScalarForm.op : ScalarForm → Op
  | .mov sz dst src => .mov sz dst src
  | .zeroExtendByte sz dst src => .movx .zero sz .b dst src
  | .lea sz dst src => .lea sz dst src
  | .push r => .push .q (.reg r)
  | .pop r => .pop .q (.reg r)
  | .bin k sz dst src => .bin k sz dst src
  | .count inc sz dst => .un (if inc then .inc else .dec) sz dst
  | .ror sz dst n => .rot .ror sz dst (.imm8 n)
  | .shl sz dst n => .shift .shl sz dst (.imm8 n)
  | .shr sz dst n => .shift .shr sz dst (.imm8 n)
  | .bswap sz r => .bswap sz r
  | .jump d => .jmp (.rel d)
  | .branch c d => .jcc c d
  | .ret => .ret

private def operation (bytes : Array UInt8) : ByteReader ScalarForm := do
  let first ← byte bytes
  let hasRex := first ≥ 0x40 && first ≤ 0x4f
  let rex := if hasRex then first - 0x40 else 0
  let op ← if hasRex then byte bytes else pure first
  let sz := if rex ≥ 8 then Size.q else .d
  let opcodeReg := reg (op % 8 + rex % 2 * 8)
  if 0x50 ≤ op && op < 0x58 then return .push opcodeReg
  if 0x58 ≤ op && op < 0x60 then return .pop opcodeReg
  if 0xb8 ≤ op && op < 0xc0 then
    return .mov sz (.reg opcodeReg) (.imm (← immediate bytes sz.bytes))
  match op with
  | 0xc3 => return .ret
  | 0xeb | 0xe9 => return .jump (← immediate bytes (if op == 0xeb then 1 else 4))
  | 0x72 | 0x73 | 0x74 | 0x75 =>
    return .branch (#[Cc.b, .ae, .e, .ne][op - 0x72]!) (← immediate bytes 1)
  | 0x0f =>
    let second ← byte bytes
    if 0xc8 ≤ second && second ≤ 0xcf then return .bswap sz (reg (second % 8 + rex % 2 * 8))
    if second == 0x84 then return .branch .e (← immediate bytes 4)
    guard (second == 0xb6)
    let f ← fields bytes rex
    -- A memory source avoids the legacy high-byte register encoding.
    guard f.rm.isMem
    return .zeroExtendByte sz f.r f.rm
  | _ =>
    let f ← fields bytes rex
    match op with
    | 0x89 => return .mov sz f.rm (.reg f.r)
    | 0x8b => return .mov sz (.reg f.r) f.rm
    | 0x88 =>
      guard (f.r == .rax && f.rm.isMem)
      return .mov .b f.rm (.reg .rax)
    | 0x8d =>
      let .mem ea := f.rm | failure
      return .lea sz f.r ea
    | 0xc7 | 0xc6 =>
      guard (f.ext == 0 && f.rm.isMem)
      return .mov (if op == 0xc6 then .b else sz) f.rm
        (.imm (← immediate bytes (if op == 0xc6 then 1 else 4)))
    | 0x01 => return .bin .add sz f.rm (.reg f.r)
    | 0x03 => return .bin .add sz (.reg f.r) f.rm
    | 0x09 => return .bin .or sz f.rm (.reg f.r)
    | 0x21 => return .bin .and sz f.rm (.reg f.r)
    | 0x31 => return .bin .xor sz f.rm (.reg f.r)
    | 0x39 => return .bin .cmp sz f.rm (.reg f.r)
    | 0x81 | 0x83 =>
      let imm ← immediate bytes (if op == 0x81 then 4 else 1)
      let kind ← match f.ext with
        | 0 => pure BinKind.add | 4 => pure .and | 5 => pure .sub | 7 => pure .cmp | _ => failure
      return .bin kind sz f.rm (.imm imm)
    | 0xc1 =>
      let count := BitVec.ofNat 8 (← byte bytes)
      match f.ext with
      | 1 => return .ror sz f.rm count
      | 4 => return .shl sz f.rm count
      | 5 => return .shr sz f.rm count
      | _ => failure
    | 0xff =>
      guard (f.ext < 2)
      return .count (f.ext == 0) sz f.rm
    | _ => failure

def decodeAt (bytes : Array UInt8) (offset : Nat) : Option Instr := do
  let (form, stop) ← (operation bytes).run offset
  guard (offset < stop && stop - offset ≤ 15)
  return ⟨form.op, stop - offset⟩

def ScalarLeaf (i : Instr) : Prop := ∃ form : ScalarForm, i.op = form.op

theorem decodeAt_scalar {bytes offset i} (h : decodeAt bytes offset = some i) : ScalarLeaf i := by
  unfold decodeAt at h
  obtain ⟨⟨form,stop⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Option.some.inj h ▸ ⟨form,rfl⟩

def codeEnd : Nat := 0x385

/-- A loaded instruction is fetched at RIP and checked against its image bytes
before executing it. The caller supplies a 64-bit load address. -/
def fetch (base : Val) (s : Cpu) : Option Instr := do
  let off := (s.rip - base).toNat
  guard (off < codeEnd)
  let i ← decodeAt image off
  guard (off + i.len ≤ codeEnd)
  guard ((List.range i.len).all fun j =>
    s.mem.read (s.rip + BitVec.ofNat 64 j) == image[off + j]!.toBitVec)
  return i

def stepLoaded (base : Val) (s : Cpu) : Option Cpu := do
  guard (!s.stopped)
  return X86.step (← fetch base s) s

end Crypto.X86_64
