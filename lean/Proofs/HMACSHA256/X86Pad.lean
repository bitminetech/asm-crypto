import Proofs.HMACSHA256.X86Setup
import Proofs.HMACSHA256.ARM64Memory
import Proofs.X86_64.Memory64

namespace Crypto.HMACSHA256.X86_64

open X86
open Crypto.X86_64 (byteView byteView_read byteView_read64 byteView_write64)
open Crypto.HMACSHA256.ARM64 (writeWords writeWords_byte writeWords_outside read64_eq_of_cells maskedByte)

def sourceReg (outer : Bool) : GPR := if outer then .rbx else .rsp
def destReg (outer : Bool) : GPR := if outer then .rsp else .r12
def destOffset (outer : Bool) : Nat := if outer then 24 else 32

def padDestination (s : Cpu) (outer : Bool) : Val :=
  s.regs.get (destReg outer) + BitVec.ofNat 64 (destOffset outer)

def loadBytes (outer : Bool) (i : Nat) : Nat :=
  (if outer then 3 else 4) + (if i = 0 then 0 else 1)

def padBytes (outer : Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => padBytes outer i + (loadBytes outer i + 8)

def padWord (outer : Bool) (n : Nat) : List Instr :=
  let source := { base := some (sourceReg outer), disp := BitVec.ofNat 64 (8 * n) : Ea }
  let dest := { base := some (destReg outer), disp := BitVec.ofNat 64 (destOffset outer + 8 * n) : Ea }
  let loadLen := loadBytes outer n
  [⟨.mov .q (.reg .rax) (.mem source), loadLen⟩,
   ⟨.bin .xor .q (.reg .rax) (.reg .r8), 3⟩,
   ⟨.mov .q (.mem dest) (.reg .rax), 5⟩]

def padCode (outer : Bool) : Nat → List Instr
  | 0 => []
  | n + 1 => padCode outer n ++ padWord outer n

theorem entry_pad_decoded :
    decodeRange entry 0x72 24 = some (padCode false 8) := by decide +kernel

theorem finish_pad_decoded :
    decodeRange finish 0x45 24 = some (padCode true 8) := by decide +kernel

theorem load_word (s : Cpu) (base : GPR) (disp : Val) (len : Nat) (live : s.ms = none) :
    X86.step ⟨.mov .q (.reg .rax) (.mem { base := some base, disp := disp }), len⟩ s =
      { s with
        regs := s.regs.set .rax (s.mem.readSize .q (s.regs.get base + disp))
        rip := s.rip + BitVec.ofNat 64 len } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.readMem,
    Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Value.writeView, Ea.addr, Ea.offset]

theorem xor_word (s : Cpu) (live : s.ms = none) :
    X86.step ⟨.bin .xor .q (.reg .rax) (.reg .r8), 3⟩ s =
      let value := s.regs.get .rax ^^^ s.regs.get .r8
      let (af, state) := s.undefBit
      { state with
        regs := s.regs.set .rax value
        flags := Flags.logic .q value af s.flags
        rip := s.rip + 3#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand,
    Cpu.getReg, Cpu.setReg, Cpu.setFlags, Cpu.setRip, Value.writeView, Cpu.undefBit]

theorem store_word (s : Cpu) (base : GPR) (disp : Val) (live : s.ms = none) :
    X86.step ⟨.mov .q (.mem { base := some base, disp := disp }) (.reg .rax), 5⟩ s =
      { s with
        mem := s.mem.writeSize .q (s.regs.get base + disp) (s.regs.get .rax)
        rip := s.rip + 5#64 } := by
  simp [X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand,
    Cpu.writeMem, Cpu.getReg, Cpu.setRip, Ea.addr, Ea.offset]

private def wordValue (s : Cpu) (outer : Bool) (i : Nat) : Val :=
  s.mem.readSize .q (s.regs.get (sourceReg outer) + BitVec.ofNat 64 (8 * i)) ^^^ s.regs.get .r8

private theorem run_word (s : Cpu) (outer : Bool) (i : Nat) (live : s.ms = none) :
    let out := X86.run (padWord outer i) s
    out.mem = s.mem.writeSize .q (padDestination s outer + BitVec.ofNat 64 (8 * i))
        (wordValue s outer i) ∧
      out.ms = none ∧ out.rip = s.rip + BitVec.ofNat 64 (loadBytes outer i + 8) ∧
      out.flags.df = s.flags.df ∧
      ∀ reg, reg ≠ .rax → out.regs.get reg = s.regs.get reg := by
  dsimp only
  let len := loadBytes outer i
  let a := X86.step ⟨.mov .q (.reg .rax)
    (.mem { base := some (sourceReg outer), disp := BitVec.ofNat 64 (8 * i) }), len⟩ s
  have aEq := load_word s (sourceReg outer) (BitVec.ofNat 64 (8 * i)) len live
  have aLive : a.ms = none := by simp [a, aEq, live]
  let b := X86.step ⟨.bin .xor .q (.reg .rax) (.reg .r8), 3⟩ a
  have bEq := xor_word a aLive
  have bLive : b.ms = none := by simp [b, bEq, a, aEq, live, Cpu.undefBit]
  let dest : Ea := {
    base := some (destReg outer)
    disp := BitVec.ofNat 64 (destOffset outer + 8 * i) }
  let ins : Instr := ⟨.mov .q (.mem dest) (.reg .rax), 5⟩
  change (X86.step ins b).mem = _ ∧ (X86.step ins b).ms = _ ∧ (X86.step ins b).rip = _ ∧
    (X86.step ins b).flags.df = s.flags.df ∧
    ∀ reg, reg ≠ .rax → (X86.step ins b).regs.get reg = s.regs.get reg
  have effect := store_word b (destReg outer) (BitVec.ofNat 64 (destOffset outer + 8 * i)) bLive
  change X86.step ins b = _ at effect
  rw [effect]
  cases outer <;>
    simp (config := { decide := true }) [b, bEq, a, aEq, live, len, Cpu.undefBit, padDestination, wordValue, Flags.logic, Flags.fromResult,
      destReg, sourceReg, destOffset, BitVec.ofNat_add, BitVec.add_assoc]
  all_goals
    intro reg keep
    repeat' rw [Regs.get_set_ne _ _ _ _ (Ne.symm keep)]

structure PadPrefix (start out : Cpu) (outer : Bool) (count : Nat) : Prop where
  memory : byteView out.mem = writeWords (byteView start.mem) (padDestination start outer)
    (wordValue start outer) count
  live : out.ms = none
  pc : out.rip = start.rip + BitVec.ofNat 64 (padBytes outer count)
  direction : out.flags.df = start.flags.df
  regs : ∀ reg, reg ≠ .rax → out.regs.get reg = start.regs.get reg

theorem pad_run_prefix (s : Cpu) (outer : Bool) (count : Nat) (live : s.ms = none)
    (bound : count ≤ 8)
    (apart : ∀ i : Fin 64, 64 ≤
      (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val - padDestination s outer).toNat) :
    PadPrefix s (X86.run (padCode outer count) s) outer count := by
  induction count with
  | zero => exact ⟨rfl, live, by simp [padBytes, padCode, X86.run], rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let a := X86.run (padCode outer n) s
    have prev := ih (by omega)
    have run : X86.run (padCode outer (n + 1)) s = X86.run (padWord outer n) a := by
      simp only [X86.run, padCode, List.foldl_append, a]
    let b := X86.run (padWord outer n) a
    obtain ⟨m, ok, pc, direction, regs⟩ := run_word a outer n prev.live
    change b.mem = _ at m
    have address : padDestination a outer = padDestination s outer := by
      have safe : destReg outer ≠ .rax := by cases outer <;> decide
      unfold padDestination
      exact congrArg (· + BitVec.ofNat 64 (destOffset outer)) (prev.regs _ safe)
    have masks : a.regs.get .r8 = s.regs.get .r8 := prev.regs _ (by decide)
    have ptr : a.regs.get (sourceReg outer) = s.regs.get (sourceReg outer) := by
      apply prev.regs
      cases outer <;> decide
    have sameWord : wordValue a outer n = wordValue s outer n := by
      unfold wordValue
      rw [masks, ptr, byteView_read64, byteView_read64]
      congr 1
      apply read64_eq_of_cells
      intro i
      rw [prev.memory, BitVec.add_assoc, ← BitVec.ofNat_add]
      apply writeWords_outside
      have near := apart ⟨8 * n + i.val, by have := i.isLt; omega⟩
      change 64 ≤ (s.regs.get (sourceReg outer) + BitVec.ofNat 64 (8 * n + i.val) -
        padDestination s outer).toNat at near
      omega
    rw [run]
    refine ⟨?_, ok, ?_, direction.trans prev.direction, fun r safe => (regs r safe).trans (prev.regs r safe)⟩
    · change byteView b.mem = _
      rw [m, byteView_write64, address, sameWord, prev.memory]
      rfl
    · change b.rip = _
      rw [show b.rip = a.rip + BitVec.ofNat 64 (loadBytes outer n + 8) from pc, prev.pc]
      simp only [padBytes, BitVec.ofNat_add, BitVec.add_assoc]

/-- The eight decoded XOR-and-store groups write all 64 pad bytes and leave
all other addresses unchanged. -/
theorem pad_run (s : Cpu) (outer : Bool) (live : s.ms = none)
    (apart : ∀ i : Fin 64, 64 ≤
      (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val - padDestination s outer).toNat) :
    ∃ out, (if outer then runRange finish 0x45 24 s else runRange entry 0x72 24 s) = some out ∧
      (∀ i : Fin 64, out.mem.read (padDestination s outer + BitVec.ofNat 64 i.val) =
        s.mem.read (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val) ^^^
          (s.regs.get .r8).extractLsb' (8 * (i.val % 8)) 8) ∧
      (∀ p, 64 ≤ (p - padDestination s outer).toNat → out.mem.read p = s.mem.read p) ∧
      out.ms = none ∧ (∀ reg, reg ≠ .rax → out.regs.get reg = s.regs.get reg) ∧
      out.rip = s.rip + (if outer then 95#64 else 103#64) := by
  let out := X86.run (padCode outer 8) s
  have ran : (if outer then runRange finish 0x45 24 s else runRange entry 0x72 24 s) = some out := by
    cases outer <;> simp [runRange, entry_pad_decoded, finish_pad_decoded, out]
  have p := pad_run_prefix s outer 8 live (by decide) apart
  refine ⟨out, ran, ?_, ?_, p.live, p.regs, ?_⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have addr : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    have memory : byteView out.mem = _ := p.memory
    rw [← byteView_read, memory]
    have wrote := writeWords_byte (byteView s.mem) (padDestination s outer) (wordValue s outer) 8 (i.val / 8) byte lt (by decide)
    unfold wordValue at wrote
    rw [byteView_read64, maskedByte] at wrote
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, addr, byteView_read] using wrote
  · intro address outside
    have memory : byteView out.mem = _ := p.memory
    rw [← byteView_read, memory, ← byteView_read]
    unfold Arm64.Memory.read8
    rw [writeWords_outside _ _ _ 8 _ outside]
  · cases outer <;> exact p.pc

theorem pad_preserves_direction {s out : Cpu} (outer : Bool) (live : s.ms = none)
    (apart : ∀ i : Fin 64, 64 ≤
      (s.regs.get (sourceReg outer) + BitVec.ofNat 64 i.val - padDestination s outer).toNat)
    (ran : (if outer then runRange finish 0x45 24 s else runRange entry 0x72 24 s) = some out) :
    out.flags.df = s.flags.df := by
  have exactRun : (if outer then runRange finish 0x45 24 s else runRange entry 0x72 24 s) =
      some (X86.run (padCode outer 8) s) := by
    cases outer <;> simp [runRange, entry_pad_decoded, finish_pad_decoded]
  rw [Option.some.inj (ran.symm.trans exactRun)]
  exact (pad_run_prefix s outer 8 live (by decide) apart).direction

end Crypto.HMACSHA256.X86_64
