import Proofs.X86_64.SetupMoves

namespace Crypto.X86_64
open X86

private def switchCode : FrameCode :=
  [(.constant 432 1,12),(.lea .rbp .rsp 288,8),(.load .rax .rsp 440,8),(.store 424 .rax,8)]
private def jumpBack : Instr := ⟨.jmp (.rel (-427)),5⟩

private theorem switch_bytes : decodeSeq 0x2de switchCode.length = some (moveInstructions switchCode) ∧
    decodeAt image 0x302 = some jumpBack := by decide +kernel

private theorem wellPlaced : ∀ p ∈ switchCode, p.1.wellPlaced 440 := by
  intro p h
  simp only [switchCode,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> subst p <;> decide

theorem stack_delta (sp a d : Val) : sp+a-(sp+d) = a-d := by
  rw [← BitVec.sub_sub, BitVec.add_comm sp, BitVec.add_sub_cancel]

theorem stack_read_other (m : Mem) (sp a d v : Val)
    (apart : ∀ b : Fin 8, 8 ≤ (a + BitVec.ofNat 64 b.val - d).toNat) :
    (m.writeSize .q (sp+d) v).readSize .q (sp+a) = m.readSize .q (sp+a) := by
  apply Mem.readN_congr _ _ _ 8
  intro b hb
  apply counter_frame
  rw [BitVec.add_assoc, stack_delta]
  exact apart ⟨b,hb⟩

def paddingCount (s : Cpu) := s.mem.readSize .q (s.regs.get .rsp+440)
def switchMemory (s : Cpu) :=
  (s.mem.writeSize .q (s.regs.get .rsp+432) 1).writeSize .q (s.regs.get .rsp+424) (paddingCount s)

private theorem switch_eval (s : Cpu) :
    let out := moveRun switchCode s
    out.mem = switchMemory s ∧ out.rip = s.rip+36 ∧ out.ms = s.ms ∧
      out.regs.get .rbp = s.regs.get .rsp+288 ∧ out.regs.get .rsp = s.regs.get .rsp ∧
      out.regs.get .rdi = s.regs.get .rdi := by
  simp (config := {decide := true}) [switchCode, moveRun, FrameMove.eval, Regs.get_set_ne,
    switchMemory, paddingCount, BitVec.add_assoc, stack_read_other _ _ 440#64 432#64 _ (by decide +kernel)]

structure SwitchResult (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x15c
  stack : out.regs.get .rsp = s.regs.get .rsp
  constants : out.regs.get .rdi = s.regs.get .rdi
  ptr : out.regs.get .rbp = s.regs.get .rsp+288
  count : blocksLeft out = paddingCount s
  phase : phase out = 1
  frame : ∀ p, 16 ≤ (p-(s.regs.get .rsp+424)).toNat → out.mem.read p = s.mem.read p

private theorem switch_frame (s : Cpu) (p : Val) (outside : 16 ≤ (p-(s.regs.get .rsp+424)).toNat) :
    (switchMemory s).read p = s.mem.read p := by
  unfold switchMemory
  rw [counter_frame _ _ _ _ (Nat.le_trans (by decide : 8 ≤ 16) outside), counter_frame]
  have bound := Crypto.ARM64.Imported.region_store_delta _ _ 8 16 8 (by decide) outside
  simpa [BitVec.add_assoc] using bound

theorem switch_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x2de)
    (loaded : ImageLoaded base s.mem) (valid : canonical (base+0x15c) = true)
    (sep : ∀ j, j < image.size → 440 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base 5 s = some out ∧ SwitchResult base s out := by
  let mid := moveRun switchCode s
  have moves := moves_loaded base switchCode 0x2de 440 s live pc loaded sep wellPlaced switch_bytes.1
  obtain ⟨mem, rip, hl, ptr, sp, k⟩ := switch_eval s
  change mid.mem = _ at mem
  have ok : mid.ms = none := hl.trans live
  have midPC : mid.rip = base+0x302 := by rw [show mid.rip = _ from rip, pc, BitVec.add_assoc]; rfl
  have code : ImageLoaded base mid.mem := by
    intro j hj
    rw [mem, switch_frame _ _ (Crypto.ARM64.Imported.region_store_delta _ _ 424 440 16 (by decide) (sep j hj)), loaded _ hj]
  have one := one_at base mid 0x302 _ ok code midPC switch_bytes.2 (by decide) (by decide)
  change canonical (base+0x15c#64) = true at valid
  have jump : X86.step jumpBack mid = {mid with rip := base+0x15c} := by
    simp [jumpBack, X86.step, Cpu.stopped, ok, Cpu.setRipChecked, midPC, BitVec.add_assoc, valid]
  refine ⟨_, steps_append moves one, ?_⟩
  rw [jump]
  refine ⟨ok,rfl,sp,k,ptr,?_,?_,?_⟩
  · change mid.mem.readSize .q (mid.regs.get .rsp+424) = _
    rw [mem, show mid.regs.get .rsp = _ from sp, switchMemory, read64_write64]
  · change mid.mem.readSize .q (mid.regs.get .rsp+432) = _
    rw [mem, show mid.regs.get .rsp = _ from sp, switchMemory,
      stack_read_other _ _ _ _ _ (by decide +kernel), read64_write64]
  · intro p hp
    exact (congrArg (fun m : Mem => m.read p) mem).trans (switch_frame _ _ hp)

end Crypto.X86_64
