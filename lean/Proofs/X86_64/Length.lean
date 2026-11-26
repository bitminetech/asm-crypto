import Proofs.X86_64.SetupMoves
import Proofs.X86_64.Return

namespace Crypto.X86_64
open X86

/-- Register operations used to prepare the public lengths and pointers. -/
inductive LengthOp where
  | mov (dst src : GPR)
  | shr6 (r : GPR)
  | shl6 (r : GPR)
  | shl3 (r : GPR)
  | and63 (r : GPR)
  | add (dst src : GPR)
  | clear (r : GPR)
  | swap (r : GPR)

def LengthOp.op : LengthOp → Op
  | .mov d s => .mov .q (.reg d) (.reg s)
  | .shr6 r => .shift .shr .q (.reg r) (.imm8 6)
  | .shl6 r => .shift .shl .q (.reg r) (.imm8 6)
  | .shl3 r => .shift .shl .q (.reg r) (.imm8 3)
  | .and63 r => .bin .and .q (.reg r) (.imm 63)
  | .add d s => .bin .add .q (.reg d) (.reg s)
  | .clear r => (WordInst.rr .xor r r).op
  | .swap r => .bswap .q r

def LengthOp.eval (o : LengthOp) (rs : Regs) : Regs :=
  match o with
  | .mov d s => rs.set d (rs.get s)
  | .shr6 r => rs.set r (rs.get r >>> 6)
  | .shl6 r => rs.set r (rs.get r <<< 6)
  | .shl3 r => rs.set r (rs.get r <<< 3)
  | .and63 r => rs.set r (rs.get r &&& 63)
  | .add d s => rs.set d (rs.get d + rs.get s)
  | .clear r => rs.set r 0
  | .swap r => rs.set r (Value.bswap .q (rs.get r))

private theorem length_step (o : LengthOp) (s : Cpu) (len : Nat) (live : s.ms = none) :
    let out := X86.step ⟨o.op,len⟩ s
    out.ms = none ∧ out.rip = s.rip+BitVec.ofNat 64 len ∧ out.regs = o.eval s.regs ∧ out.mem = s.mem := by
  cases o <;> simp [LengthOp.op, LengthOp.eval, WordInst.op, WordOp.opcode, X86.step, Cpu.stopped,
    live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.writeOperand, Cpu.setReg, Cpu.getReg,
    Cpu.setRip, Cpu.setFlags, Cpu.undefBit, Value.writeView, Flags.addResult, Flags.shiftCount,
    trunc32]

abbrev LengthCode := List (LengthOp × Nat)
def lengthInstrs (code : LengthCode) := code.map (fun (o,n) => (⟨o.op,n⟩ : Instr))
def lengthRegs (code : LengthCode) (rs : Regs) := code.foldl (fun v p => p.1.eval v) rs

theorem length_loaded (base : Val) (code : LengthCode) (s : Cpu) (off : Nat)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem) (pc : s.rip = base+BitVec.ofNat 64 off)
    (decode : decodeSeq off code.length = some (lengthInstrs code)) :
    ∃ out, steps base code.length s = some out ∧ out.ms = none ∧ out.mem = s.mem ∧
      out.rip = s.rip+BitVec.ofNat 64 (code.map Prod.snd).sum ∧ out.regs = lengthRegs code s.regs := by
  induction code generalizing s off with
  | nil => exact ⟨s,rfl,live,rfl,by simp,rfl⟩
  | cons head tail ih =>
    obtain ⟨o,n⟩ := head
    simp only [List.length_cons,decodeSeq] at decode
    cases hd : decodeAt image off with
    | none => simp [hd] at decode
    | some i =>
      by_cases bound : off < codeEnd ∧ off+i.len ≤ codeEnd
      · cases more : decodeSeq (off+i.len) tail.length with
        | none => simp [hd,guard,bound,more] at decode
        | some rest =>
          simp [hd,guard,bound,more,lengthInstrs] at decode
          obtain ⟨rfl,restEq⟩ := decode
          have one := one_at _ _ _ _ live loaded pc hd bound.1 bound.2 (by cases o <;> rfl)
          obtain ⟨ok,rip,regs,mem⟩ := length_step o s n live
          obtain ⟨out,run,hl,hm,hp,hr⟩ := ih _ _ ok (mem ▸ loaded)
            (rip.trans (by rw [pc,BitVec.ofNat_add,BitVec.add_assoc])) (more.trans (congrArg some restEq))
          exact ⟨out, by simpa [Nat.add_comm 1 tail.length] using steps_append one run, hl,hm.trans mem,
            by simpa [rip,BitVec.ofNat_add,BitVec.add_assoc] using hp, by simpa [lengthRegs,regs] using hr⟩
      · simp [hd,guard,bound] at decode

private def divide : LengthCode := [(.mov .rdx .rcx,3),(.shr6 .rdx,4)]
private def saveCount : FrameCode := [(.store 424 .rdx,8)]
private def tailAddr : LengthCode := [(.mov .r8 .rcx,3),(.and63 .r8,4),(.mov .r9 .rdx,3),
  (.shl6 .r9,4),(.add .r9 .rbp,3),(.clear .rbx,2)]

private theorem length_bytes :
    decodeSeq 0xa7 divide.length = some (lengthInstrs divide) ∧
    decodeSeq 0xae saveCount.length = some (moveInstructions saveCount) ∧
    decodeSeq 0xb6 tailAddr.length = some (lengthInstrs tailAddr) := by decide +kernel

structure LengthState (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base+0xc9
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rbp = s.regs.get .rbp
  size : out.regs.get .rcx = s.regs.get .rcx
  index : out.regs.get .rbx = 0
  remainder : out.regs.get .r8 = BitVec.ofNat 64 ((s.regs.get .rcx).toNat % 64)
  tail : out.regs.get .r9 = s.regs.get .rbp + BitVec.ofNat 64 ((s.regs.get .rcx).toNat/64*64)
  mem : out.mem = s.mem.writeSize .q (s.regs.get .rsp+424) (BitVec.ofNat 64 ((s.regs.get .rcx).toNat/64))

theorem length_setup_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xa7)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 432 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base 9 s = some out ∧ LengthState base s out := by
  obtain ⟨a,divRun,alive,am,ap,ar⟩ := length_loaded base divide s 0xa7 live loaded pc length_bytes.1
  have stack : a.regs.get .rsp = s.regs.get .rsp := by simp [ar,lengthRegs,divide,LengthOp.eval,Regs.get_set_ne]
  let b := moveRun saveCount a
  have save := moves_loaded base saveCount 0xae 432 a alive (by simpa [divide,pc,BitVec.add_assoc] using ap)
    (am ▸ loaded) (by simpa only [stack] using sep) (by intro p hp; simp [saveCount] at hp; subst p; decide) length_bytes.2.1
  have mem : b.mem = s.mem.writeSize .q (s.regs.get .rsp+424) (s.regs.get .rcx >>> 6) := by
    simp [b, moveRun, saveCount, FrameMove.eval, ar, lengthRegs, divide, LengthOp.eval, Regs.get_set_ne, am]
  have next : b.rip = base+0xb6 := by simp [b, moveRun, saveCount, FrameMove.eval, ap, divide, pc, BitVec.add_assoc]
  have code : ImageLoaded base b.mem := by
    intro j hj
    exact (congrArg (fun m : Mem => m.read _) mem).trans ((counter_frame _ _ _ _
      (Crypto.ARM64.Imported.region_store_delta _ _ 424 432 8 (by decide) (sep j hj))).trans (loaded j hj))
  obtain ⟨out, tailRun, ok, outputMem, rip, regs⟩ := length_loaded base tailAddr b 0xb6 alive code next length_bytes.2.2
  have division (x : Val) : x >>> 6 = BitVec.ofNat 64 (x.toNat/64) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]
  have rem (x : Val) : x &&& 63 = BitVec.ofNat 64 (x.toNat%64) := by
    change x &&& (BitVec.ofNat 64 (2^6-1)) = _
    apply BitVec.eq_of_toNat_eq
    change x.toNat &&& (2^6-1) = x.toNat % 64 % (2^64)
    exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 6).trans
      (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt x.toNat (by decide : 0 < 64)) (by decide : 64 < 2^64))).symm
  have mul (x : Val) : (x >>> 6) <<< 6 = BitVec.ofNat 64 (x.toNat/64*64) := by
    rw [division, ← BitVec.mul_twoPow_eq_shiftLeft, BitVec.ofNat_mul]; rfl
  have br : b.regs = a.regs := by simp [b,moveRun,saveCount,FrameMove.eval]
  refine ⟨out, steps_append divRun (steps_append save tailRun), ⟨ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [tailAddr,next,BitVec.add_assoc] using rip
  all_goals simp [regs,lengthRegs,tailAddr,br,ar,divide,LengthOp.eval,Regs.get_set_ne,
    outputMem,mem,rem,mul,division,BitVec.add_comm]
  all_goals first | exact rem _ | rw [← BitVec.mul_twoPow_eq_shiftLeft, BitVec.ofNat_mul]; rfl

end Crypto.X86_64
