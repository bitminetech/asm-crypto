import Proofs.X86_64.Fragments
import Proofs.X86_64.Memory64
import Proofs.ARM64.ImportedPaddingSuffix

namespace Crypto.X86_64
open X86

theorem one_at (base : Val) (s : Cpu) (off : Nat) (i : Instr)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + BitVec.ofNat 64 off) (decoded : decodeAt image off = some i)
    (a : off < codeEnd) (b : off+i.len ≤ codeEnd) (regular : isReturn i = false := by rfl) : steps base 1 s = some (X86.step i s) := by
  have f := fetch_at _ _ _ _ loaded pc decoded a b
  simp [steps, stepInside, guard, Cpu.stopped, live, f, regular]

private def cmpSlot (disp : Val) : Instr :=
  ⟨.bin .cmp .q (.mem {base := some .rsp, disp}) (.imm 0),9⟩

private def testSlot (disp : Val) (s : Cpu) := s.mem.readSize .q (s.regs.get .rsp + disp)

private theorem compare_slot (s : Cpu) (disp : Val) (live : s.ms = none) :
    X86.step (cmpSlot disp) s = {s with
      flags := Flags.sub .q (testSlot disp s) 0 s.flags, rip := s.rip+9} := by
  simp [cmpSlot, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.readMem, Cpu.setFlags, Cpu.setRip, Ea.addr, Ea.offset, testSlot]

theorem branch_run (s : Cpu) (c : Cc) (len : Nat) (disp : Val)
    (live : s.ms = none) (target : canonical (s.rip + BitVec.ofNat 64 len + disp) = true) :
    X86.step ⟨.jcc c disp,len⟩ s = {s with
      rip := if c.eval s.flags then s.rip + BitVec.ofNat 64 len + disp else s.rip + BitVec.ofNat 64 len} := by
  cases b : c.eval s.flags <;> simp [X86.step, Cpu.stopped, live, b, Cpu.setRip, Cpu.setRipChecked, target]

private theorem slot_branch (base : Val) (s : Cpu) (off len : Nat) (field delta : Val) (c : Cc)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem) (pc : s.rip = base + BitVec.ofNat 64 off)
    (d1 : decodeAt image off = some (cmpSlot field))
    (d2 : decodeAt image (off+9) = some ⟨.jcc c delta,len⟩)
    (bound : off+9+len ≤ codeEnd) (pos : 0 < len)
    (target : canonical (s.rip+9+BitVec.ofNat 64 len+delta) = true) :
    ∃ out, steps base 2 s = some out ∧ out.ms = none ∧ out.mem = s.mem ∧ out.regs = s.regs ∧
      out.rip = if c.eval (Flags.sub .q (testSlot field s) 0 s.flags)
        then s.rip+9+BitVec.ofNat 64 len+delta else s.rip+9+BitVec.ofNat 64 len := by
  let mid := X86.step (cmpSlot field) s
  have one := one_at base s off _ live loaded pc d1 (by omega) (by change off+9 ≤ codeEnd; omega)
  have ok : mid.ms = none := by rw [show mid = _ from compare_slot _ _ live]; exact live
  have mem : mid.mem = s.mem := by rw [show mid = _ from compare_slot _ _ live]
  have rip : mid.rip = s.rip+9 := by rw [show mid = _ from compare_slot _ _ live]
  have two := one_at base mid (off+9) _ ok (mem ▸ loaded)
    (by rw [rip, pc, BitVec.ofNat_add, BitVec.add_assoc]; rfl) d2 (by omega) bound
  refine ⟨_, steps_append one two, ?_⟩
  rw [branch_run mid c len delta ok (by rw [rip]; exact target), show mid = _ from compare_slot _ _ live]
  exact ⟨live,rfl,rfl,rfl⟩

def blocksLeft (s : Cpu) := s.mem.readSize .q (s.regs.get .rsp+424)
def phase (s : Cpu) := s.mem.readSize .q (s.regs.get .rsp+432)

private theorem check_bytes :
    decodeAt image 0x15c = some (cmpSlot 424) ∧ decodeAt image 0x165 = some ⟨.jcc .e 0x168,6⟩ ∧
    decodeAt image 0x2d3 = some (cmpSlot 432) ∧ decodeAt image 0x2dc = some ⟨.jcc .ne 0x29,2⟩ := by decide +kernel

theorem blocks_test (base : Val) (s : Cpu) (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + 0x15c) (valid : canonical (base + 0x2d3) = true) :
    ∃ out, steps base 2 s = some out ∧ out.ms = none ∧ out.mem = s.mem ∧ out.regs = s.regs ∧
      out.rip = if blocksLeft s = 0 then base+0x2d3 else base+0x16b := by
  obtain ⟨out,run,ok,mem,regs,rip⟩ := slot_branch base s 0x15c 6 424 0x168 .e live loaded pc
    check_bytes.1 check_bytes.2.1 (by decide) (by decide) (by simpa [pc, BitVec.add_assoc] using valid)
  exact ⟨out,run,ok,mem,regs,by simpa [Cc.eval, Flags.sub, Flags.fromResult, Flags.subResult,
    Value.isZero, testSlot, blocksLeft, pc, BitVec.add_assoc] using rip⟩

theorem phase_test (base : Val) (s : Cpu) (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + 0x2d3) (valid : canonical (base + 0x307) = true) :
    ∃ out, steps base 2 s = some out ∧ out.ms = none ∧ out.mem = s.mem ∧ out.regs = s.regs ∧
      out.rip = if phase s = 0 then base+0x2de else base+0x307 := by
  obtain ⟨out,run,ok,mem,regs,rip⟩ := slot_branch base s 0x2d3 2 432 0x29 .ne live loaded pc
    check_bytes.2.2.1 check_bytes.2.2.2 (by decide) (by decide) (by simpa [pc, BitVec.add_assoc] using valid)
  exact ⟨out,run,ok,mem,regs,by simpa [Cc.eval, Flags.sub, Flags.fromResult, Flags.subResult,
    Value.isZero, testSlot, phase, pc, BitVec.add_assoc] using rip⟩


private def nextPtr : Instr := ⟨.bin .add .q (.reg .rbp) (.imm 64),4⟩
private def decrement : Instr := ⟨.un .dec .q (.mem {base := some .rsp, disp := 424}),8⟩
private def repeatBlocks : Instr := ⟨.jmp (.rel (-375)),5⟩

private theorem advance_bytes :
    decodeAt image 0x2c2 = some nextPtr ∧ decodeAt image 0x2c6 = some decrement ∧
    decodeAt image 0x2ce = some repeatBlocks := by decide +kernel

private theorem bump_step (s : Cpu) (live : s.ms = none) :
    X86.step nextPtr s = {s with
      regs := s.regs.set .rbp (s.regs.get .rbp + 64),
      rip := s.rip+4, flags := Flags.add .q (s.regs.get .rbp) 64 s.flags} := by
  simp [nextPtr, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand,
    Cpu.getReg, Cpu.writeOperand, Cpu.setReg, Cpu.setFlags, Cpu.setRip, Value.writeView, Flags.addResult]

private theorem decrement_step (s : Cpu) (live : s.ms = none) :
    X86.step decrement s = {s with
      mem := s.mem.writeSize .q (s.regs.get .rsp+424) (blocksLeft s - 1),
      flags := Flags.dec .q (blocksLeft s) s.flags, rip := s.rip+8} := by
  simp [decrement, X86.step, Cpu.stopped, live, Cpu.readOperand, Cpu.readMem, Cpu.writeOperand,
    Cpu.writeMem, Cpu.setFlags, Cpu.setRip, Ea.addr, Ea.offset, blocksLeft, Flags.subResult]

private theorem repeat_step (s : Cpu) (live : s.ms = none) (valid : canonical (s.rip+5-375) = true) :
    X86.step repeatBlocks s = {s with rip := s.rip+5-375} := by
  simp_all [repeatBlocks, X86.step, Cpu.stopped, Cpu.setRipChecked, Cpu.setRip, BitVec.sub_eq_add_neg]

theorem counter_frame (m : Mem) (a p v : Val) (outside : 8 ≤ (p-a).toNat) :
    (m.writeSize .q a v).read p = m.read p := by
  rw [← byteView_read, byteView_write64, Crypto.ARM64.Imported.read8_write64_outside_ne]
  · rfl
  · intro b eq
    rw [eq, Crypto.ARM64.Imported.address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at outside
    have := b.isLt
    omega

/-- The three instructions after feed-forward advance the source pointer and
decrement the remaining block count before returning to the phase test. -/
theorem advance_loaded (base : Val) (s : Cpu) (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + 0x2c2) (valid : canonical (base+0x15c) = true)
    (sep : ∀ j, j < image.size → 8 ≤ (base+BitVec.ofNat 64 j-(s.regs.get .rsp+424)).toNat) :
    ∃ out, steps base 3 s = some out ∧ out.ms = none ∧ out.rip = base + 0x15c ∧
      out.regs = s.regs.set .rbp (s.regs.get .rbp + 64) ∧
      out.mem = s.mem.writeSize .q (s.regs.get .rsp+424) (blocksLeft s-1) := by
  let a := X86.step nextPtr s
  have runA := one_at base s 0x2c2 _ live loaded pc advance_bytes.1 (by decide) (by decide)
  have aOK : a.ms = none := by rw [show a = _ from bump_step _ live]; exact live
  have aPC : a.rip = base+0x2c6 := by simp [a, bump_step _ live, pc, BitVec.add_assoc]
  have aSP : a.regs.get .rsp = s.regs.get .rsp := by simp [a, bump_step _ live, Regs.get_set_ne]
  have aMem : a.mem = s.mem := by simp [a, bump_step _ live]
  have runB := one_at base a 0x2c6 _ aOK (aMem ▸ loaded) aPC advance_bytes.2.1 (by decide) (by decide)
  let b := X86.step decrement a
  have bOK : b.ms = none := by rw [show b = _ from decrement_step _ aOK]; exact aOK
  have bPC : b.rip = base+0x2ce := by simp [b, decrement_step _ aOK, aPC, BitVec.add_assoc]
  have bMem : b.mem = s.mem.writeSize .q (s.regs.get .rsp+424) (blocksLeft s-1) := by
    simp [b, decrement_step _ aOK, blocksLeft, aSP, aMem]
  have code : ImageLoaded base b.mem := by
    intro j hj
    rw [bMem, counter_frame _ _ _ _ (sep j hj), loaded _ hj]
  have runC := one_at base b 0x2ce _ bOK code bPC advance_bytes.2.2 (by decide) (by decide)
  have back : b.rip+5-375 = base+0x15c := by simp [bPC, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  refine ⟨_, steps_append runA (steps_append runB runC), ?_⟩
  rw [repeat_step b bOK (back ▸ valid)]
  exact ⟨bOK, back, by simp [b, decrement_step _ aOK, a, bump_step _ live], bMem⟩

end Crypto.X86_64
