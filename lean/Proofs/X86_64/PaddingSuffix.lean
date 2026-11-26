import Proofs.X86_64.TailCopy
import Proofs.X86_64.Length
import Proofs.ARM64.ImportedPaddingSuffix

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (lengthOffset)

private def marker : Instr := ⟨.mov .b (.mem {base := some .rsp,index := some .r8,disp := 288}) (.imm (-128)),9⟩
private def setSmall (n : Val) : Instr := ⟨.mov .d (.reg .rax) (.imm n),5⟩
private def cmpRem : Instr := ⟨.bin .cmp .q (.reg .r8) (.imm 56),4⟩
private def skipTwo : Instr := ⟨.jcc .b 5,2⟩
private def savePadding : FrameCode := [(.store 440 .rax,8)]
private def bitLength : LengthCode := [(.shl6 .rax,4),(.shl3 .rcx,4),(.swap .rcx,3)]
private def saveBits : Instr := ⟨.mov .q (.mem {base := some .rsp,index := some .rax,disp := 280}) (.reg .rcx),8⟩

private theorem suffix_bytes :
    decodeAt image 0xdf = some marker ∧ decodeAt image 0xe8 = some (setSmall 1) ∧
    decodeAt image 0xed = some cmpRem ∧ decodeAt image 0xf1 = some skipTwo ∧
    decodeAt image 0xf3 = some (setSmall 2) ∧
    decodeSeq 0xf8 1 = some (moveInstructions savePadding) ∧
    decodeSeq 0x100 3 = some (lengthInstrs bitLength) ∧ decodeAt image 0x10b = some saveBits := by decide +kernel

private theorem marker_step (s : Cpu) (live : s.ms = none) :
    X86.step marker s = {s with mem := s.mem.write (padBase s+s.regs.get .r8) 128, rip := s.rip+9} := by
  simp [marker,X86.step,Cpu.stopped,live,wellFormed2,Operand.isMem,Cpu.readOperand,Cpu.writeOperand,
    Cpu.writeMem,Cpu.setRip,Ea.addr,Ea.offset,Scale.toVal,Mem.writeSize,Size.bytes,Mem.writeN,padBase]
  congr 1; ac_rfl

private theorem small_step (s : Cpu) (n : Val) (live : s.ms = none) :
    X86.step (setSmall n) s = {s with regs := s.regs.set .rax ((n.setWidth 32).setWidth 64), rip := s.rip+5} := by
  simp [setSmall,X86.step,Cpu.stopped,live,wellFormed2,Operand.isMem,Cpu.readOperand,Cpu.writeOperand,
    Cpu.setReg,Cpu.setRip,Value.writeView,trunc32]

private theorem cmp_step (s : Cpu) (live : s.ms = none) :
    X86.step cmpRem s = {s with flags := Flags.sub .q (s.regs.get .r8) 56 s.flags, rip := s.rip+4} := by
  simp [cmpRem,X86.step,Cpu.stopped,live,wellFormed2,Operand.isMem,Cpu.readOperand,Cpu.getReg,Cpu.setFlags,Cpu.setRip]

def padBlocks (r : Nat) : Nat := if r < 56 then 1 else 2
def optionalMove (r : Nat) : Nat := if r < 56 then 0 else 1

def choosePaddingEvents (base sp : Val) (r : Nat) : List Event :=
  frameFragment base sp 0xe8 3 ++
    if r < 56 then [] else frameFragment base sp 0xf3 1

private theorem select_count (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xe8)
    (loaded : ImageLoaded base s.mem) (valid : canonical (base+0xf8) = true) :
    let r := (s.regs.get .r8).toNat
    ∃ out, steps base (3+optionalMove r) s = some out ∧ out.ms = none ∧ out.rip = base+0xf8 ∧ out.mem = s.mem ∧
      out.regs = s.regs.set .rax (BitVec.ofNat 64 (padBlocks r)) ∧
      ObservedExecution base s (choosePaddingEvents base (s.regs.get .rsp) r) out := by
  let a := X86.step (setSmall 1) s
  let b := X86.step cmpRem a
  let c := X86.step skipTwo b
  have r1 := one_at base s 0xe8 _ live loaded pc suffix_bytes.2.1 (by decide) (by decide)
  have ao : a.ms = none := by simp [a,small_step _ _ live,live]
  have am : a.mem = s.mem := by simp [a,small_step _ _ live]
  have ap : a.rip = base+0xed := by simp [a,small_step _ _ live,pc,BitVec.add_assoc]
  have r2 := one_at base a 0xed _ ao (am ▸ loaded) ap suffix_bytes.2.2.1 (by decide) (by decide)
  have bo : b.ms = none := by simp [b,cmp_step _ ao,ao]
  have bm : b.mem = s.mem := by simp [b,cmp_step _ ao,am]
  have bp : b.rip = base+0xf1 := by simp [b,cmp_step _ ao,ap,BitVec.add_assoc]
  have r3 := one_at base b 0xf1 _ bo (bm ▸ loaded) bp suffix_bytes.2.2.2.1 (by decide) (by decide)
  have branch : c = _ := branch_run b .b 2 5 bo (by simpa [bp,BitVec.add_assoc] using valid)
  have co : c.ms = none := by rw [branch]; exact bo
  have cm : c.mem = s.mem := by rw [branch]; exact bm
  have cr : c.regs = s.regs.set .rax 1 := by rw [branch]; simp [b,cmp_step _ ao,a,small_step _ _ live]
  have cp : c.rip = if (s.regs.get .r8).toNat < 56 then base+0xf8 else base+0xf3 := by
    rw [branch]; simp [b,cmp_step _ ao,a,small_step _ _ live,Cc.eval,Flags.sub,Flags.subCF,Value.uval,
      Regs.get_set_ne,pc,BitVec.add_assoc]
  have initial := steps_observe_fragment (steps_append r1 (steps_append r2 r3)) pc (by decide +kernel)
  by_cases h : (s.regs.get .r8).toNat < 56
  · exact ⟨c, by simpa [optionalMove,h] using steps_append r1 (steps_append r2 r3),
      co,by simpa [h] using cp,cm,by simpa [padBlocks,h] using cr,
      by simpa [choosePaddingEvents,h] using initial⟩
  · have r4 := one_at base c 0xf3 _ co (cm ▸ loaded) (by simpa [h] using cp) suffix_bytes.2.2.2.2.1 (by decide) (by decide)
    have cpc : c.rip = base+0xf3 := by simpa [h] using cp
    have cs : c.regs.get .rsp = s.regs.get .rsp := by simp [cr,Regs.get_set_ne]
    have optional := steps_observe_fragment r4 cpc (by decide +kernel)
    rw [cs] at optional
    refine ⟨_,by simpa [optionalMove,h] using steps_append r1 (steps_append r2 (steps_append r3 r4)),?_,?_,?_,?_,?_⟩
    · rw [small_step _ _ co]; exact co
    · rw [small_step _ _ co]; simp [cpc,BitVec.add_assoc]
    · rw [small_step _ _ co]; exact cm
    · rw [small_step _ _ co]; simp [cr,Regs.set,padBlocks,h]
    · simpa only [choosePaddingEvents, if_neg h] using initial.append optional

private theorem bits_step (s : Cpu) (live : s.ms = none) :
    X86.step saveBits s = {s with
      mem := s.mem.writeSize .q (s.regs.get .rsp+s.regs.get .rax+280) (s.regs.get .rcx), rip := s.rip+8} := by
  simp [saveBits,X86.step,Cpu.stopped,live,wellFormed2,Operand.isMem,Cpu.readOperand,Cpu.writeOperand,
    Cpu.getReg,Cpu.writeMem,Cpu.setRip,Ea.addr,Ea.offset,Scale.toVal]

def markedMemory (s : Cpu) (r : Nat) := s.mem.write (padBase s+BitVec.ofNat 64 r) 128

def suffixMemory (s : Cpu) (r : Nat) :=
  let counts := (markedMemory s r).writeSize .q (s.regs.get .rsp+440) (BitVec.ofNat 64 (padBlocks r))
  counts.writeSize .q (padBase s+BitVec.ofNat 64 (lengthOffset r)) (Value.bswap .q (s.regs.get .rcx <<< 3))

def suffixEvents (base sp : Val) (r : Nat) : List Event :=
  [(base+0xdf,marker,[⟨true,sp+288+BitVec.ofNat 64 r,1⟩])] ++
    choosePaddingEvents base sp r ++ frameFragment base sp 0xf8 4 ++
    [(base+0x10b,saveBits,[⟨true,sp+288+BitVec.ofNat 64 (lengthOffset r),8⟩])]

structure SuffixState (base : Val) (s out : Cpu) (r : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x113
  stack : out.regs.get .rsp = s.regs.get .rsp
  payload : out.regs.get .rbp = s.regs.get .rbp
  mem : out.mem = suffixMemory s r
  observations : ObservedExecution base s (suffixEvents base (s.regs.get .rsp) r) out

theorem padding_suffix_loaded (base : Val) (s : Cpu) (r : Nat) (live : s.ms = none) (pc : s.rip = base+0xdf)
    (loaded : ImageLoaded base s.mem) (length : (s.regs.get .r8).toNat = r) (small : r < 64)
    (valid : canonical (base+0xf8) = true)
    (sep : ∀ j, j < image.size → 448 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base (9+optionalMove r) s = some out ∧ SuffixState base s out r := by
  let a := X86.step marker s
  have first := one_at base s 0xdf _ live loaded pc suffix_bytes.1 (by decide) (by decide)
  have av : s.regs.get .r8 = BitVec.ofNat 64 r := by rw [← length]; simp
  have am : a.mem = markedMemory s r := by simp [a,marker_step _ live,markedMemory,av]
  have aok : a.ms = none := by simp [a,marker_step _ live,live]
  have ar : a.regs = s.regs := by simp [a,marker_step _ live]
  have ap : a.rip = base+0xe8 := by simp [a,marker_step _ live,pc,BitVec.add_assoc]
  have codeA : ImageLoaded base a.mem := by
    intro j hj
    rw [am,markedMemory,Mem.read_write_ne,loaded _ hj]
    intro eq
    have h := sep j hj
    rw [eq,padBase] at h
    change 448 ≤ (s.regs.get .rsp+288#64+BitVec.ofNat 64 r-s.regs.get .rsp).toNat at h
    rw [BitVec.add_assoc,← BitVec.ofNat_add (n := 64) 288 r,Crypto.ARM64.Imported.address_delta,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
    omega
  obtain ⟨b,choose,bok,bp,bm,br,choiceTrace⟩ := select_count base a aok ap codeA valid
  simp only [ar,length] at choose br choiceTrace
  let c := moveRun savePadding b
  have bs : b.regs.get .rsp = s.regs.get .rsp := by simp [br,Regs.get_set_ne]
  have save := moves_loaded base savePadding 0xf8 448 b bok bp (bm ▸ codeA) (by simpa only [bs] using sep)
    (by intro p hp; simp [savePadding] at hp; subst p; decide) suffix_bytes.2.2.2.2.2.1
  have cr : c.regs = b.regs := by simp [c,moveRun,savePadding,FrameMove.eval]
  have cm : c.mem = (markedMemory s r).writeSize .q (s.regs.get .rsp+440) (BitVec.ofNat 64 (padBlocks r)) := by
    simp [c,moveRun,savePadding,FrameMove.eval,br,bm,am,Regs.get_set_ne]
  have cp : c.rip = base+0x100 := by simp [c,moveRun,savePadding,FrameMove.eval,bp,BitVec.add_assoc]
  have codeC : ImageLoaded base c.mem := by
    intro j hj
    exact (congrArg (fun m : Mem => m.read _) cm).trans ((counter_frame _ _ _ _
      (Crypto.ARM64.Imported.region_store_delta _ _ 440 448 8 (by decide) (sep j hj))).trans (am ▸ codeA j hj))
  obtain ⟨d,arithmetic,dok,dm,dp,dr⟩ := length_loaded base bitLength c 0x100 bok codeC cp suffix_bytes.2.2.2.2.2.2.1
  have dpc : d.rip = base+0x10b := by simpa [bitLength,cp,BitVec.add_assoc] using dp
  have last := one_at base d 0x10b _ dok (dm ▸ codeC) dpc suffix_bytes.2.2.2.2.2.2.2 (by decide) (by decide)
  have sp : d.regs.get .rsp = s.regs.get .rsp := by simp [dr,lengthRegs,bitLength,LengthOp.eval,cr,br,Regs.get_set_ne]
  have payload : d.regs.get .rbp = s.regs.get .rbp := by simp [dr,lengthRegs,bitLength,LengthOp.eval,cr,br,Regs.get_set_ne]
  have stored : s.regs.get .rsp + (BitVec.ofNat 64 (padBlocks r) <<< 6) + 280 =
      padBase s+BitVec.ofNat 64 (lengthOffset r) := by
    by_cases h : r < 56 <;> simp [padBase,padBlocks,lengthOffset,h,BitVec.add_assoc]
  have firstTrace := steps_observe_single first pc suffix_bytes.1 (by decide) (by decide)
    (show dataAccesses marker s = some [⟨true,s.regs.get .rsp+288+BitVec.ofNat 64 r,1⟩] from by
      simp [marker,dataAccesses,operandAccess,Ea.addr,Ea.offset,Size.bytes,Scale.toVal,av]
      ac_rfl)
  have savedTrace := steps_observe_fragment (steps_append save arithmetic) bp (by decide +kernel)
  have indexValue : d.regs.get .rax = BitVec.ofNat 64 (padBlocks r) <<< 6 := by
    simp [dr,lengthRegs,bitLength,LengthOp.eval,cr,br,Regs.get_set_ne]
  have lastTrace := steps_observe_single last dpc suffix_bytes.2.2.2.2.2.2.2 (by decide) (by decide)
    (show dataAccesses saveBits d = some [⟨true,s.regs.get .rsp+288+BitVec.ofNat 64 (lengthOffset r),8⟩] from by
      simpa [saveBits,dataAccesses,operandAccess,Ea.addr,Ea.offset,Size.bytes,Scale.toVal,sp,indexValue,padBase] using stored)
  rw [bs] at savedTrace
  have observations : ObservedExecution base s (suffixEvents base (s.regs.get .rsp) r) (X86.step saveBits d) :=
    by simpa only [suffixEvents,List.append_assoc] using firstTrace.append (choiceTrace.append (savedTrace.append lastTrace))
  refine ⟨X86.step saveBits d,?_,?_⟩
  · have run := steps_append first (steps_append choose (steps_append save (steps_append arithmetic last)))
    simpa only [show 9+optionalMove r = 1+(3+optionalMove r+(1+(3+1))) by omega] using run
  · change SuffixState base s (X86.step saveBits d) r
    refine ⟨?_,?_,?_,?_,?_,observations⟩ <;> rw [bits_step _ dok]
    · exact dok
    · simp [dpc,BitVec.add_assoc]
    · exact sp
    · exact payload
    · simp [dr,lengthRegs,bitLength,LengthOp.eval,cr,br,Regs.get_set_ne,dm,cm,suffixMemory]
      exact congrArg (fun p => Mem.writeSize _ .q p _) stored

end Crypto.X86_64
