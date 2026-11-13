import Models.ARM64Program

/-!
A restricted local A64 model for the straight-line compression-round fragment.
Unsupported encodings fail, and each step records its read footprint.
Instruction meaning and decoding are trusted model assumptions. The complete
call uses the pinned imported ISA in Models.ARM64.
-/
namespace Crypto.ARM64.Round

abbrev Word := BitVec 32
abbrev Address := BitVec 64
abbrev Memory := Address → BitVec 8

structure State where
  registers : Fin 31 → Address
  sp : Address
  pc : Address
  memory : Memory
  reads : List Address := []

def readX (s : State) (index : Nat) : Address :=
  if h : index < 31 then s.registers ⟨index, h⟩ else 0

def readBase (s : State) (index : Nat) : Address :=
  if index = 31 then s.sp else readX s index

def readW (s : State) (index : Nat) : Word := (readX s index).truncate 32

def writeW (s : State) (index : Nat) (value : Word) : State :=
  { s with registers := fun i => if i.val = index then value.zeroExtend 64 else s.registers i }

def read32 (memory : Memory) (address : Address) : Word :=
  memory (address + 3) ++ memory (address + 2) ++ memory (address + 1) ++ memory address

def field (word : Word) (low width : Nat) : Nat := (word.toNat / 2 ^ low) % 2 ^ width

def shifted (word : Word) (kind amount : Nat) : Word :=
  match kind with
  | 0 => word <<< amount
  | 1 => word >>> amount
  | 2 => word.sshiftRight amount
  | _ => word.rotateRight amount

/-- One supported instruction, with modulo-64-bit address arithmetic and
zero-extension of every W-register write. No branch or store is supported. -/
def stepWord (word : Word) (s : State) : Option State := do
  let rd := field word 0 5
  let rn := field word 5 5
  let rm := field word 16 5
  let amount := field word 10 6
  let next := { s with pc := s.pc + 4 }
  if word &&& 0xffe00000#32 == 0x0b000000#32 then
    -- ADD (shifted register), W form, LSL only.
    if amount < 32 then
      return writeW next rd (readW s rn + (readW s rm <<< amount))
    else none
  else if word &&& 0x1f000000#32 == 0x0a000000#32 && field word 31 1 == 0 then
    -- Logical (shifted register), W form: AND/BIC, ORR/ORN, EOR/EON.
    if amount < 32 && field word 29 2 < 3 then
      let rhs := shifted (readW s rm) (field word 22 2) amount
      let rhs := if field word 21 1 == 1 then ~~~rhs else rhs
      let result := match field word 29 2 with
        | 0 => readW s rn &&& rhs
        | 1 => readW s rn ||| rhs
        | _ => readW s rn ^^^ rhs
      return writeW next rd result
    else none
  else if word &&& 0xffe00000#32 == 0x13800000#32 then
    -- EXTR Wd, Wn, Wm, #lsb (ROR is the Rn=Rm alias).
    if amount < 32 then
      return writeW next rd (((readW s rn ++ readW s rm) >>> amount).truncate 32)
    else none
  else if word &&& 0xffe0fc00#32 == 0xb8607800#32 then
    -- LDR Wt, [Xn|SP, Xm, LSL #2], UXTX scaled register offset.
    let address := readBase s rn + (readX s rm <<< 2)
    let loaded := writeW next rd (read32 s.memory address)
    return { loaded with reads := s.reads ++ [address, address + 1, address + 2, address + 3] }
  else none

def runWords : List Word → State → Option State
  | [], s => some s
  | instruction :: rest, s => (stepWord instruction s).bind (runWords rest)

/-- Offsets 0x124 through 0x198 inclusive: exactly 30 instructions. The loop
counter update and branch at 0x19c onward are outside this fragment. -/
def code : List Word := (imageWords.toList.drop 73).take 30

def working (s : State) : Vector Word 8 :=
  #v[readW s 7, readW s 8, readW s 9, readW s 10,
     readW s 11, readW s 12, readW s 13, readW s 14]

end Crypto.ARM64.Round
