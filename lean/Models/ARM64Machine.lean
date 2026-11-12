import Models.ARM64Round

/-!
Local A64 operational model for the complete instruction vocabulary of the
recorded SHA-256 function. Unsupported/illegal encodings fail. Data memory is
byte addressed, little endian and total; the entry/safety proof must separately
establish accessible memory. Instruction fetch uses that same memory.

`returned` and the access logs are ghost observations of a single library call,
not architectural registers. RET sets the architectural PC and ends this call.
The model/decoder remain a named trust boundary pending independent ISA review.
-/
namespace Crypto.ARM64.Machine

open Round (Word Address Memory read32 field)

structure Flags where
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  deriving DecidableEq, Repr

structure State extends Round.State where
  flags : Flags := {}
  simd : Fin 32 → BitVec 128 := fun _ => 0
  fpcr : BitVec 32 := 0
  fpsr : BitVec 32 := 0
  writes : List Address := []
  fetches : List Address := []
  stackPointers : List Address := []
  returned : Bool := false

def readX (s : State) (index : Nat) : Address := Round.readX s.toState index
def readBase (s : State) (index : Nat) : Address := Round.readBase s.toState index

def writeX (s : State) (index : Nat) (value : Address) : State :=
  { s with registers := fun i => if i.val = index then value else s.registers i }

def writeBase (s : State) (index : Nat) (value : Address) : State :=
  if index = 31 then { s with sp := value } else writeX s index value

def signedImmediate (width value : Nat) : Address :=
  BitVec.ofInt 64 (if value < 2 ^ (width - 1) then Int.ofNat value else
    Int.ofNat value - Int.ofNat (2 ^ width))

def byteAt (value : Address) (index : Nat) : BitVec 8 := (value >>> (8 * index)).truncate 8

def loadLE (memory : Memory) (address : Address) (size : Nat) : Address :=
  (List.range size).foldl
    (fun value i => value ||| ((memory (address + BitVec.ofNat 64 i)).zeroExtend 64 <<< (8 * i))) 0

/-- A store updates exactly the modular byte interval starting at `address`.
All modeled store widths are at most eight bytes. -/
def storeLE (memory : Memory) (address : Address) (size : Nat) (value : Address) : Memory :=
  fun p => if (p - address).toNat < size then byteAt value (p - address).toNat else memory p

def addresses (address : Address) (size : Nat) : List Address :=
  (List.range size).map fun i => address + BitVec.ofNat 64 i

def load (s : State) (rt : Nat) (address : Address) (size : Nat) : State :=
  let value := loadLE s.memory address size
  let s := writeX s rt value
  { s with reads := s.reads ++ addresses address size }

def store (s : State) (rt : Nat) (address : Address) (size : Nat) : State :=
  { s with memory := storeLE s.memory address size (readX s rt)
           writes := s.writes ++ addresses address size }

def arithmeticFlags (x y result : Address) (subtract : Bool) : Flags :=
  { n := result.msb
    z := result == 0
    c := if subtract then decide (y.toNat ≤ x.toNat) else decide (2 ^ 64 ≤ x.toNat + y.toNat)
    v := if subtract then (x.msb != y.msb) && (result.msb != x.msb)
         else (x.msb == y.msb) && (result.msb != x.msb) }

def arithmetic (s : State) (rd : Nat) (x y : Address) (subtract setFlags baseDest : Bool) : State :=
  let result := if subtract then x - y else x + y
  let s := if setFlags then { s with flags := arithmeticFlags x y result subtract } else s
  if baseDest && !setFlags then writeBase s rd result else writeX s rd result

def condition (flags : Flags) (cond : Nat) : Bool :=
  let result := match cond / 2 with
    | 0 => flags.z
    | 1 => flags.c
    | 2 => flags.n
    | 3 => flags.v
    | 4 => flags.c && !flags.z
    | 5 => flags.n == flags.v
    | 6 => (flags.n == flags.v) && !flags.z
    | _ => true
  if cond % 2 == 1 && cond != 15 then !result else result

def reverseBytes (value : Address) (size : Nat) : Address :=
  (List.range size).foldl
    (fun acc i => acc ||| ((byteAt value i).zeroExtend 64 <<< (8 * (size - 1 - i)))) 0

/-- Extra instructions beyond the previously proved round vocabulary. -/
def extraStep (word : Word) (s : State) : Option State := do
  let rd := field word 0 5
  let rn := field word 5 5
  let rm := field word 16 5
  let next := { s with pc := s.pc + 4 }
  if word &&& 0x9f800000#32 == 0x91000000#32 then
    -- ADD/SUB (immediate), X form, including CMP and SP destinations.
    let amount := field word 10 12 * 2 ^ (12 * field word 22 1)
    return arithmetic next rd (readBase s rn) (BitVec.ofNat 64 amount)
      (field word 30 1 == 1) (field word 29 1 == 1) true
  else if word &&& 0x9fe00000#32 == 0x8b000000#32 then
    -- ADD/SUB (shifted register), X form, LSL only, including CMP.
    return arithmetic next rd (readX s rn) (readX s rm <<< field word 10 6)
      (field word 30 1 == 1) (field word 29 1 == 1) false
  else if word &&& 0xffe0e000#32 == 0x8b206000#32 then
    -- ADD (extended register), X form, UXTX; Rn/Rd may denote SP.
    let amount := field word 10 3
    if amount ≤ 4 then
      return writeBase next rd (readBase s rn + (readX s rm <<< amount))
    else none
  else if word &&& 0xfffffc00#32 == 0x92401400#32 then
    -- AND Xd,Xn,#63: the only logical-immediate encoding in this program.
    return writeX next rd (readX s rn &&& 63)
  else if word &&& 0xffc00000#32 == 0xd3400000#32 then
    -- UBFM X aliases: LSR and LSL. Other bitfield forms are unsupported.
    let immr := field word 16 6
    let imms := field word 10 6
    if imms = 63 then return writeX next rd (readX s rn >>> immr)
    else if imms + 1 = immr then return writeX next rd (readX s rn <<< (64 - immr))
    else none
  else if word &&& 0x7f800000#32 == 0x52800000#32 then
    -- MOVZ W/X, including MOV immediate aliases. MOVN/MOVK are unsupported.
    let wide := field word 31 1 == 1
    let halfword := field word 21 2
    if wide || halfword < 2 then
      let value := (BitVec.ofNat 64 (field word 5 16)) <<< (16 * halfword)
      return writeX next rd (if wide then value else (value.truncate 32).zeroExtend 64)
    else none
  else if word &&& 0xffe0fc00#32 == 0xaa000000#32 then
    -- ORR Xd,Xn,Xm, LSL #0, including MOV register aliases.
    return writeX next rd (readX s rn ||| readX s rm)
  else if word &&& 0xfffffc00#32 == 0x5ac00800#32 then
    return writeX next rd (reverseBytes (readX s rn) 4)
  else if word &&& 0xfffffc00#32 == 0xdac00c00#32 then
    return writeX next rd (reverseBytes (readX s rn) 8)
  else if word &&& 0x9f000000#32 == 0x10000000#32 then
    -- ADR: signed 21-bit byte offset from the address of this instruction.
    let imm := field word 5 19 * 4 + field word 29 2
    return writeX next rd (s.pc + signedImmediate 21 imm)
  else if word &&& 0xffc00000#32 == 0xf9400000#32 then
    return load next rd (readBase s rn + BitVec.ofNat 64 (8 * field word 10 12)) 8
  else if word &&& 0xffc00000#32 == 0xb9400000#32 then
    return load next rd (readBase s rn + BitVec.ofNat 64 (4 * field word 10 12)) 4
  else if word &&& 0xffc00000#32 == 0xb9000000#32 then
    return store next rd (readBase s rn + BitVec.ofNat 64 (4 * field word 10 12)) 4
  else if word &&& 0xffe0fc00#32 == 0xb8207800#32 then
    return store next rd (readBase s rn + (readX s rm <<< 2)) 4
  else if word &&& 0xffe0fc00#32 == 0x38606800#32 then
    return load next rd (readBase s rn + readX s rm) 1
  else if word &&& 0xffe0fc00#32 == 0x38206800#32 then
    return store next rd (readBase s rn + readX s rm) 1
  else if word &&& 0xffe00c00#32 == 0xb8400000#32 then
    return load next rd (readBase s rn + signedImmediate 9 (field word 12 9)) 4
  else if word &&& 0xffe00c00#32 == 0xf8000000#32 then
    return store next rd (readBase s rn + signedImmediate 9 (field word 12 9)) 8
  else if word &&& 0x7fc00000#32 == 0x29000000#32 ||
          word &&& 0x7fc00000#32 == 0x29400000#32 then
    -- Integer STP/LDP with signed offset, no writeback, W or X form.
    let size := if field word 31 1 == 1 then 8 else 4
    let address := readBase s rn + (signedImmediate 7 (field word 15 7)) * BitVec.ofNat 64 size
    let rt2 := field word 10 5
    if field word 22 1 == 1 then
      if rd == rt2 then none else
      let first := loadLE s.memory address size
      let second := loadLE s.memory (address + BitVec.ofNat 64 size) size
      let result := writeX (writeX next rd first) rt2 second
      return { result with reads := s.reads ++ addresses address (2 * size) }
    else
      return store (store next rd address size) rt2 (address + BitVec.ofNat 64 size) size
  else if word &&& 0xfc000000#32 == 0x14000000#32 then
    return { s with pc := s.pc + (signedImmediate 26 (field word 0 26) <<< 2) }
  else if word &&& 0xff000010#32 == 0x54000000#32 then
    if condition s.flags (field word 0 4) then
      return { s with pc := s.pc + (signedImmediate 19 (field word 5 19) <<< 2) }
    else return next
  else if word &&& 0xfe000000#32 == 0xb4000000#32 then
    -- CBZ/CBNZ X only. Bit 24 selects the nonzero form.
    let nonzero := field word 24 1 == 1
    if (readX s rd != 0) == nonzero then
      return { s with pc := s.pc + (signedImmediate 19 (field word 5 19) <<< 2) }
    else return next
  else if word &&& 0xfffffc1f#32 == 0xd65f0000#32 then
    return { s with pc := readX s rn, returned := true }
  else if word == 0xd503201f#32 then return next
  else none

def stepWord (word : Word) (s : State) : Option State :=
  match Round.stepWord word s.toState with
  | some core => some { s with toState := core }
  | none => extraStep word s

def step (s : State) : Option State :=
  if s.returned then none else
  stepWord (read32 s.memory s.pc)
    { s with fetches := s.fetches ++ [s.pc], stackPointers := s.stackPointers ++ [s.sp] }

def run : Nat → State → Option State
  | 0, s => some s
  | fuel + 1, s =>
    if s.returned then some s else (step s).bind (run fuel)

/-- External steps may change only memory. The baseline quantifies over every
oracle that preserves the call's protected memory footprint. -/
def runInterleaved (external : Nat → Memory → Memory) : Nat → Nat → State → Option State
  | 0, _, s => some s
  | fuel + 1, tick, s =>
    if s.returned then some s else
    let s := { s with memory := external tick s.memory }
    (step s).bind (runInterleaved external fuel (tick + 1))

def start (s : State) : State :=
  { s with reads := [], writes := [], fetches := [], stackPointers := [], returned := false }

def runWords : List Word → State → Option State
  | [], s => some s
  | instruction :: rest, s => (stepWord instruction s).bind (runWords rest)

end Crypto.ARM64.Machine
