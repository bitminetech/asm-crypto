import Models.X86SHA256Decode
import Proofs.ARM64.Round

/-! Register and memory projections of the imported x86 instruction step used
by the word schedule and compression round. A dword write clears the upper
half of its destination. The incoming flags and undefined-flag oracle may be
arbitrary. -/
namespace Crypto.X86_64
open X86

abbrev Word := BitVec 32

structure DataState where
  regs : Regs
  mem : Mem
  deriving Inhabited

def project (s : Cpu) : DataState := ⟨s.regs, s.mem⟩

def DataState.word (s : DataState) (r : GPR) : Word := (s.regs.get r).setWidth 32

def DataState.put (s : DataState) (r : GPR) (v : Word) : DataState :=
  { s with regs := s.regs.set r (v.setWidth 64) }

structure Indexed where
  base : GPR
  disp : Val := 0
  deriving DecidableEq, Repr

def Indexed.ea (a : Indexed) : Ea :=
  { base := some a.base, index := some .rbx, scale := .s4, disp := a.disp }

def Indexed.addr (a : Indexed) (s : DataState) : Val :=
  s.regs.get a.base + s.regs.get .rbx * 4 + a.disp

def Indexed.read (a : Indexed) (s : DataState) : Word :=
  (s.mem.readSize .d (a.addr s)).setWidth 32

inductive WordOp where
  | mov | add | xor | and | or
  deriving DecidableEq, Repr

def WordOp.apply (op : WordOp) (x y : Word) : Word :=
  match op with
  | .mov => y | .add => x + y | .xor => x ^^^ y | .and => x &&& y | .or => x ||| y

def WordOp.opcode (op : WordOp) (dst : GPR) (src : Operand) : Op :=
  match op with
  | .mov => .mov .d (.reg dst) src
  | .add => .bin .add .d (.reg dst) src
  | .xor => .bin .xor .d (.reg dst) src
  | .and => .bin .and .d (.reg dst) src
  | .or => .bin .or .d (.reg dst) src

inductive WordInst where
  | rr (op : WordOp) (dst src : GPR)
  | rm (op : WordOp) (dst : GPR) (src : Indexed)
  | bswap (dst : GPR)
  | loadStack (dst : GPR) (disp : Val)
  | store (dst : Indexed) (src : GPR)
  | ror (dst : GPR) (count : BitVec 8)
  | shr (dst : GPR) (count : BitVec 8)
  deriving DecidableEq, Repr

def WordInst.op (i : WordInst) : Op :=
  match i with
  | .rr op dst src => op.opcode dst (.reg src)
  | .rm op dst src => op.opcode dst (.mem src.ea)
  | .bswap dst => .bswap .d dst
  | .loadStack dst disp => .mov .d (.reg dst) (.mem { base := some .rsp, disp })
  | .store dst src => .mov .d (.mem dst.ea) (.reg src)
  | .ror dst n => .rot .ror .d (.reg dst) (.imm8 n)
  | .shr dst n => .shift .shr .d (.reg dst) (.imm8 n)

def WordInst.eval (i : WordInst) (s : DataState) : DataState :=
  match i with
  | .rr op dst src => s.put dst (op.apply (s.word dst) (s.word src))
  | .rm op dst src => s.put dst (op.apply (s.word dst) (src.read s))
  | .bswap dst => s.put dst ((Value.bswap .d ((s.word dst).setWidth 64)).setWidth 32)
  | .loadStack dst disp => s.put dst ((s.mem.readSize .d (s.regs.get .rsp + disp)).setWidth 32)
  | .store dst src =>
    { s with mem := s.mem.writeSize .d (dst.addr s) ((s.word src).setWidth 64) }
  | .ror dst n => s.put dst ((s.word dst).rotateRight (n.toNat % 32))
  | .shr dst n => s.put dst ((s.word dst) >>> (n.toNat % 32))

theorem trunc32 (v : Val) : Value.trunc .d v = (v.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Value.trunc, BitVec.getLsbD_and, Size.mask_getLsbD, Size.bits,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Bool.and_comm]
  rfl

private theorem narrow (x : Word) (t : Nat) :
    ((x.setWidth 64 >>> t).setWidth 32) = x >>> t :=
  Crypto.ARM64.Round.narrow_shift x t

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem word_step (i : WordInst) (s : Cpu) (len : Nat) (live : s.ms = none) :
    let out := X86.step ⟨i.op, len⟩ s
    project out = i.eval (project s) ∧ out.ms = none ∧ out.rip = s.rip + BitVec.ofNat 64 len := by
  cases i with
  | rr op dst src | rm op dst src =>
    cases op <;>
      simp [WordInst.op, WordOp.opcode, WordInst.eval, WordOp.apply, X86.step,
        Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand,
        Cpu.getReg, Cpu.setReg, Cpu.readMem, Cpu.setRip, Cpu.setFlags, Cpu.undefBit,
        DataState.put, DataState.word, Indexed.read, Indexed.addr, Indexed.ea, Ea.addr,
        Ea.offset, Scale.toVal, project, Flags.addResult, Value.writeView, trunc32,
        BitVec.setWidth_add _ _ (by decide : 32 ≤ 64)]
  | bswap dst =>
    simp [WordInst.op, WordInst.eval, X86.step, Cpu.stopped, live, Cpu.setReg, Cpu.getReg,
      Value.writeView, Cpu.setRip, DataState.put, DataState.word, project, trunc32]
  | loadStack dst disp =>
    simp [WordInst.op, WordInst.eval, X86.step, Cpu.stopped, live, wellFormed2,
      Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.readMem, Cpu.setRip,
      Cpu.setReg, DataState.put, Ea.addr, Ea.offset, project, Value.writeView, trunc32]
  | store dst src =>
    simp [WordInst.op, WordInst.eval, X86.step, Cpu.stopped, live, wellFormed2,
      Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.writeMem, Cpu.setRip, Cpu.getReg,
      project, DataState.word, Indexed.addr, Indexed.ea, Ea.addr, Ea.offset, Scale.toVal, trunc32]
  | ror dst n | shr dst n =>
    simp [WordInst.op, WordInst.eval, X86.step, Cpu.stopped, live,
      Cpu.readOperand, Cpu.writeOperand, Cpu.getReg, Cpu.setReg,
      Cpu.setRip, Cpu.setFlags, Cpu.undefBit, project, DataState.put, DataState.word,
      Value.writeView, Flags.rotMasked, Flags.rotReduced, Flags.rotResult, Size.bits,
      Flags.shiftCount, trunc32]
    split <;> simp_all [narrow, BitVec.rotateRight_def]

def decodeSeq (off : Nat) : Nat → Option (List Instr)
  | 0 => some []
  | n + 1 => do
    let i ← decodeAt image off
    guard (off < codeEnd ∧ off + i.len ≤ codeEnd)
    return i :: (← decodeSeq (off + i.len) n)

abbrev WordBlock := List (WordInst × Nat)

def instructions (block : WordBlock) : List Instr :=
  block.map fun (i, len) => ⟨i.op, len⟩

def evalBlock (block : WordBlock) (s : DataState) : DataState :=
  block.foldl (fun st i => i.1.eval st) s

theorem word_block (block : WordBlock) (s : Cpu) (live : s.ms = none) :
    project (X86.run (instructions block) s) = evalBlock block (project s) ∧
    (X86.run (instructions block) s).ms = none ∧
    (X86.run (instructions block) s).rip = s.rip + BitVec.ofNat 64 (block.map Prod.snd).sum := by
  induction block generalizing s with
  | nil => simp [X86.run, instructions, evalBlock, live]
  | cons pair rest ih =>
    obtain ⟨i, len⟩ := pair
    obtain ⟨proj, ok, pc⟩ := word_step i s len live
    obtain ⟨final, ok', pc'⟩ := ih (X86.step ⟨i.op, len⟩ s) ok
    exact ⟨final.trans (congrArg (evalBlock rest) proj), ok',
      by simpa [X86.run, instructions, pc, BitVec.ofNat_add, BitVec.add_assoc] using pc'⟩

end Crypto.X86_64
