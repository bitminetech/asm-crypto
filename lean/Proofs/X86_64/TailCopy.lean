import Proofs.X86_64.Header
import Proofs.X86_64.FrameTrace

namespace Crypto.X86_64
open X86

private def testTail : Instr := ⟨.bin .cmp .q (.reg .rbx) (.reg .r8),3⟩
private def tailExit : Instr := ⟨.jcc .ae 17,2⟩
private def loadByte : Instr := ⟨.movx .zero .d .b .rax (.mem {base := some .r9,index := some .rbx}),5⟩
private def storeByte : Instr := ⟨.mov .b (.mem {base := some .rsp,index := some .rbx,disp := 288}) (.reg .rax),7⟩
private def jumpTail : Instr := ⟨.jmp (.rel (-22)),2⟩

private theorem tail_bytes :
    decodeAt image 0xc9 = some testTail ∧ decodeAt image 0xcc = some tailExit ∧
    decodeAt image 0xce = some loadByte ∧ decodeAt image 0xd3 = some storeByte ∧
    decodeAt image 0xda = some incIndex ∧ decodeAt image 0xdd = some jumpTail := by decide +kernel

def padBase (s : Cpu) := s.regs.get .rsp+288
private def copyAddr (s : Cpu) := padBase s + s.regs.get .rbx
private def sourceByte (s : Cpu) := s.mem.read (s.regs.get .r9+s.regs.get .rbx)

private theorem cmp_tail_step (s : Cpu) (live : s.ms = none) :
    X86.step testTail s = {s with rip := s.rip+3, flags := Flags.sub .q (s.regs.get .rbx) (s.regs.get .r8) s.flags} := by
  simp [testTail, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.getReg, Cpu.setFlags, Cpu.setRip]

private theorem copy_test (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xc9)
    (loaded : ImageLoaded base s.mem) (valid : canonical (base+0xdf) = true) :
    ∃ out, steps base 2 s = some out ∧ out.ms = none ∧ out.mem = s.mem ∧ out.regs = s.regs ∧
      out.rip = if (s.regs.get .rbx).toNat < (s.regs.get .r8).toNat then base+0xce else base+0xdf := by
  let a := X86.step testTail s
  have one := one_at base s 0xc9 _ live loaded pc tail_bytes.1 (by decide) (by decide)
  have ok : a.ms = none := by simp [a,cmp_tail_step _ live,live]
  have next : a.rip = base+0xcc := by simp [a,cmp_tail_step _ live,pc,BitVec.add_assoc]
  have mem : a.mem = s.mem := by simp [a,cmp_tail_step _ live]
  have two := one_at base a 0xcc _ ok (mem ▸ loaded) next tail_bytes.2.1 (by decide) (by decide)
  have good : canonical (a.rip+2+17) = true := by simpa [next,BitVec.add_assoc] using valid
  refine ⟨_,steps_append one two,?_⟩
  rw [show X86.step tailExit a = _ from branch_run a .ae 2 17 ok good]
  simp [a,cmp_tail_step _ live,pc,live,Cc.eval,Flags.sub,Flags.subCF,Value.uval,BitVec.add_assoc]
  split <;> split <;> first | rfl | omega

private theorem trunc8 (v : Val) : Value.trunc .b v = (v.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Value.trunc, BitVec.getLsbD_and, Size.mask_getLsbD, Size.bits,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Bool.and_comm]
  rfl

private theorem load_byte_step (s : Cpu) (live : s.ms = none) :
    X86.step loadByte s = {s with regs := s.regs.set .rax ((sourceByte s).setWidth 64), rip := s.rip+5} := by
  simp [loadByte, X86.step, Cpu.stopped, live, Cpu.readOperand, Cpu.readMem, Cpu.setReg, Cpu.setRip,
    Ea.addr, Ea.offset, Scale.toVal, Mem.readSize, Size.bytes, Mem.readN, Value.zext, Value.writeView,
    trunc8, trunc32, sourceByte]


private theorem store_byte_step (s : Cpu) (live : s.ms = none) :
    X86.step storeByte s = {s with mem := s.mem.write (copyAddr s) ((s.regs.get .rax).setWidth 8), rip := s.rip+7} := by
  simp [storeByte, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.getReg,
    Cpu.writeOperand, Cpu.writeMem, Cpu.setRip, Ea.addr, Ea.offset, Scale.toVal, Mem.writeSize,
    Size.bytes, Mem.writeN, trunc8, padBase, copyAddr, BitVec.add_assoc]
  congr 1
  congr 1
  ac_rfl

private theorem jump_tail_step (s : Cpu) (live : s.ms = none) (base : Val) (pc : s.rip = base+0xdd)
    (good : canonical (base+0xc9) = true) : X86.step jumpTail s = {s with rip := base+0xc9} := by
  change canonical (base+0xc9#64) = true at good
  simp [jumpTail,X86.step,Cpu.stopped,live,Cpu.setRipChecked,pc,BitVec.add_assoc,good]

private def copyBodyCode := [loadByte, storeByte, incIndex, jumpTail]

def copyBodyEvents (base sp src : Val) (n : Nat) : List Event :=
  [(base+0xce, loadByte, [⟨false, src+BitVec.ofNat 64 n, 1⟩]),
   (base+0xd3, storeByte, [⟨true, sp+288+BitVec.ofNat 64 n, 1⟩]),
   (base+0xda, incIndex, []),
   (base+0xdd, jumpTail, [])]

private theorem copy_body_observer (base : Val) (s out : Cpu) (n : Nat)
    (live : s.ms = none) (pc : s.rip = base+0xce) (idx : s.regs.get .rbx = BitVec.ofNat 64 n)
    (run : steps base 4 s = some out) :
    ObservedExecution base s (copyBodyEvents base (s.regs.get .rsp) (s.regs.get .r9) n) out := by
  have actual := steps_observe_linear (code := copyBodyCode) run pc (by decide +kernel) (by decide +kernel)
  have one : (X86.step loadByte s).ms = none := by rw [load_byte_step _ live]; exact live
  have two : (X86.step storeByte (X86.step loadByte s)).ms = none := by rw [store_byte_step _ one]; exact one
  have result : observeCode copyBodyCode s =
      copyBodyEvents base (s.regs.get .rsp) (s.regs.get .r9) n := by
    simp only [copyBodyCode,observeCode]
    rw [inc_step _ two,store_byte_step _ one,load_byte_step _ live]
    simp [copyBodyEvents, dataAccesses, operandAccess, loadByte, storeByte, incIndex, jumpTail,
      Ea.addr, Ea.offset, Scale.toVal, Size.bytes, pc, idx, Regs.get_set_ne, BitVec.add_assoc]
    exact BitVec.add_comm _ _
  rwa [result] at actual

def copyTestEvents (base sp : Val) := frameFragment base sp 0xc9 2

def copyPrefixEvents (base sp src : Val) : Nat → List Event
  | 0 => []
  | n+1 => copyPrefixEvents base sp src n ++ copyTestEvents base sp ++ copyBodyEvents base sp src n

def tailCopyEvents (base sp src : Val) (r : Nat) : List Event :=
  copyPrefixEvents base sp src r ++ copyTestEvents base sp

private theorem copy_body (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xce)
    (loaded : ImageLoaded base s.mem) (good : canonical (base+0xc9) = true)
    (sep : ∀ j, j < image.size → base+BitVec.ofNat 64 j ≠ copyAddr s) :
    ∃ out, steps base 4 s = some out ∧ out.ms = none ∧ out.rip = base+0xc9 ∧
      out.mem = s.mem.write (copyAddr s) (sourceByte s) ∧
      out.regs = (s.regs.set .rax ((sourceByte s).setWidth 64)).set .rbx (s.regs.get .rbx+1) := by
  let a := X86.step loadByte s
  have r1 := one_at base s 0xce _ live loaded pc tail_bytes.2.2.1 (by decide) (by decide)
  have aok : a.ms = none := by simp [a, load_byte_step _ live, live]
  have ap : a.rip = base+0xd3 := by simp [a, load_byte_step _ live, pc, BitVec.add_assoc]
  have am : a.mem = s.mem := by simp [a,load_byte_step _ live]
  have r2 := one_at base a 0xd3 _ aok (am ▸ loaded) ap tail_bytes.2.2.2.1 (by decide) (by decide)
  let b := X86.step storeByte a
  have bm : b.mem = s.mem.write (copyAddr s) (sourceByte s) := by
    simp [b, store_byte_step _ aok,a,load_byte_step _ live,copyAddr,padBase,Regs.get_set_ne]
  have bok : b.ms = none := by simp [b,store_byte_step _ aok,aok]
  have bp : b.rip = base+0xda := by simp [b,store_byte_step _ aok,ap,BitVec.add_assoc]
  have code : ImageLoaded base b.mem := by
    intro j hj; rw [bm, Mem.read_write_ne _ _ _ _ (sep j hj), loaded _ hj]
  have r3 := one_at base b 0xda _ bok code bp tail_bytes.2.2.2.2.1 (by decide) (by decide)
  let c := X86.step incIndex b
  have cok : c.ms = none := by simp [c,inc_step _ bok,bok]
  have cp : c.rip = base+0xdd := by simp [c,inc_step _ bok,bp,BitVec.add_assoc]
  have cm : c.mem = b.mem := by simp [c,inc_step _ bok]
  have r4 := one_at base c 0xdd _ cok (cm ▸ code) cp tail_bytes.2.2.2.2.2 (by decide) (by decide)
  refine ⟨_,steps_append r1 (steps_append r2 (steps_append r3 r4)),?_⟩
  rw [jump_tail_step c cok base cp good]
  exact ⟨cok,rfl,cm.trans bm,by simp [c,inc_step _ bok,b,store_byte_step _ aok,a,load_byte_step _ live,Regs.get_set_ne]⟩


structure CopyState (s out : Cpu) (n : Nat) : Prop where
  live : out.ms = none
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → out.regs.get r = s.regs.get r
  index : out.regs.get .rbx = BitVec.ofNat 64 n
  frame : ∀ p, n ≤ (p-padBase s).toNat → out.mem.read p = s.mem.read p
  bytes : ∀ j, j < n → out.mem.read (padBase s+BitVec.ofNat 64 j) = s.mem.read (s.regs.get .r9+BitVec.ofNat 64 j)

attribute [local irreducible] steps image X86.step

private theorem copy_prefix (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xc9)
    (loaded : ImageLoaded base s.mem) (index : s.regs.get .rbx = 0)
    (sites : canonical (base+0xdf) = true ∧ canonical (base+0xc9) = true)
    (rem : Nat) (length : (s.regs.get .r8).toNat = rem) (small : rem < 64)
    (sep : ∀ j, j < image.size → 64 ≤ (base+BitVec.ofNat 64 j-padBase s).toNat)
    (src : ∀ j, j < rem → 64 ≤ (s.regs.get .r9+BitVec.ofNat 64 j-padBase s).toNat)
    (n : Nat) (bound : n ≤ rem) :
    ∃ out, steps base (6*n) s = some out ∧ out.rip = base+0xc9 ∧ CopyState s out n ∧
      ObservedExecution base s (copyPrefixEvents base (s.regs.get .rsp) (s.regs.get .r9) n) out := by
  induction n with
  | zero => exact ⟨s,by simp [steps],pc,⟨live,fun _ _ _ => rfl,index,fun _ _ => rfl,fun _ h => by omega⟩,.nil _⟩
  | succ n ih =>
    obtain ⟨mid, prefixRun, mpc, prev, observedBefore⟩ := ih (by omega)
    have code : ImageLoaded base mid.mem := fun j hj => (prev.frame _ (Nat.le_trans (by omega) (sep j hj))).trans (loaded j hj)
    obtain ⟨a, test, ok, mem, regs, rip⟩ := copy_test base mid prev.live mpc code sites.1
    have taken : (mid.regs.get .rbx).toNat < (mid.regs.get .r8).toNat := by
      rw [prev.index, prev.regs _ (by decide) (by decide), length, BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_pos taken] at rip
    have idx : a.regs.get .rbx = BitVec.ofNat 64 n := (congrArg (fun r : Regs => r.get .rbx) regs).trans prev.index
    have reg (r : GPR) (x : r ≠ .rax) (y : r ≠ .rbx) : a.regs.get r = s.regs.get r :=
      (congrArg (fun rs : Regs => rs.get r) regs).trans (prev.regs _ x y)
    have addr : copyAddr a = padBase s+BitVec.ofNat 64 n := by rw [copyAddr,padBase,reg _ (by decide) (by decide),idx,padBase]
    have different (p : Val) (h : n < (p-padBase s).toNat) : p ≠ copyAddr a := by
      intro eq
      rw [eq,addr,Crypto.ARM64.Imported.address_delta,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
      omega
    obtain ⟨out, body, hl, hp, hm, hr⟩ := copy_body base a ok rip (mem ▸ code) sites.2
      (fun j hj => different _ (Nat.lt_of_lt_of_le (by omega) (sep j hj)))
    have value : sourceByte a = s.mem.read (s.regs.get .r9+BitVec.ofNat 64 n) := by
      rw [sourceByte,reg _ (by decide) (by decide),idx,mem]
      exact prev.frame _ (Nat.le_trans (by omega) (src n (by omega)))
    have observedTest := steps_observe_fragment test mpc (by decide +kernel)
    rw [prev.regs .rsp (by decide) (by decide)] at observedTest
    have observedCopy := copy_body_observer base a out n ok rip idx body
    rw [reg .rsp (by decide) (by decide), reg .r9 (by decide) (by decide)] at observedCopy
    refine ⟨out, by simpa only [Nat.mul_succ] using steps_append prefixRun (steps_append test body),
      hp, ⟨hl, ?_, ?_, ?_, ?_⟩, (observedBefore.append observedTest).append observedCopy⟩
    · intro r x y
      simpa [hr, Regs.get_set_ne _ _ _ _ (Ne.symm x), Regs.get_set_ne _ _ _ _ (Ne.symm y)] using reg r x y
    · simp [hr,idx,BitVec.ofNat_add]
    · intro p h
      rw [hm,Mem.read_write_ne _ _ _ _ (different p (by omega)),mem,prev.frame _ (by omega)]
    · intro j hj
      by_cases eq : j = n
      · subst j; rw [hm,← addr,Mem.read_write_same,value]
      · have ne : padBase s+BitVec.ofNat 64 j ≠ copyAddr a := by
          intro e
          rw [addr] at e
          have h := congrArg (fun v => (v-padBase s).toNat) e
          simp only [Crypto.ARM64.Imported.address_delta,BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : j < 2^64),Nat.mod_eq_of_lt (by omega : n < 2^64)] at h
          exact eq h
        rw [hm,Mem.read_write_ne _ _ _ _ ne,mem,prev.bytes j (by omega)]

theorem tail_copy_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0xc9)
    (loaded : ImageLoaded base s.mem) (index : s.regs.get .rbx = 0)
    (sites : canonical (base+0xdf) = true ∧ canonical (base+0xc9) = true)
    (rem : Nat) (length : (s.regs.get .r8).toNat = rem) (small : rem < 64)
    (sep : ∀ j, j < image.size → 64 ≤ (base+BitVec.ofNat 64 j-padBase s).toNat)
    (src : ∀ j, j < rem → 64 ≤ (s.regs.get .r9+BitVec.ofNat 64 j-padBase s).toNat) :
    ∃ out, steps base (6*rem+2) s = some out ∧ out.rip = base+0xdf ∧ CopyState s out rem ∧
      ObservedExecution base s (tailCopyEvents base (s.regs.get .rsp) (s.regs.get .r9) rem) out := by
  obtain ⟨mid, run, mpc, copy, observedBefore⟩ := copy_prefix base s live pc loaded index sites rem length small sep src rem (by omega)
  obtain ⟨out, test, ok, mem, regs, rip⟩ := copy_test base mid copy.live mpc
    (fun j hj => (copy.frame _ (Nat.le_trans (by omega) (sep j hj))).trans (loaded j hj)) sites.1
  have stop : ¬ (mid.regs.get .rbx).toNat < (mid.regs.get .r8).toNat := by
    rw [copy.index,copy.regs _ (by decide) (by decide),length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have observedTest := steps_observe_fragment test mpc (by decide +kernel)
  rw [copy.regs .rsp (by decide) (by decide)] at observedTest
  exact ⟨out,steps_append run test,by simpa only [if_neg stop] using rip,
    ⟨ok,fun r x y => (congrArg (fun v : Regs => v.get r) regs).trans (copy.regs r x y),
      (congrArg (fun v : Regs => v.get .rbx) regs).trans copy.index,
      fun p h => (congrArg (fun m : Mem => m.read p) mem).trans (copy.frame p h),
      fun j h => (congrArg (fun m : Mem => m.read _) mem).trans (copy.bytes j h)⟩,observedBefore.append observedTest⟩

end Crypto.X86_64
