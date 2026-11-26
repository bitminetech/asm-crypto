import Proofs.X86_64.TracePaths
import Proofs.X86_64.Fragments
import Proofs.X86_64.Memory64
import Proofs.ARM64.ImportedHashInitFrame
import Proofs.ARM64.ImportedPaddingSuffix

namespace Crypto.X86_64
open X86

def savedReg (i : Fin 6) : GPR :=
  (#v[.rbx,.rbp,.r12,.r13,.r14,.r15] : Vector GPR 6)[i.val]

private def pushPC (n : Nat) := if n < 2 then n else 2*n-2
private def pushLen (i : Fin 6) := if i.val < 2 then 1 else 2
private def pushInstr (i : Fin 6) : Instr := ⟨.push .q (.reg (savedReg i)), pushLen i⟩
private def allocate : Instr := ⟨.bin .sub .q (.reg .rsp) (.imm 456), 7⟩

private theorem push_table : ∀ i : Fin 6,
    decodeAt image (pushPC i.val) = some (pushInstr i) ∧
    pushPC i.val + (pushInstr i).len = pushPC (i.val+1) ∧
    pushPC (i.val+1) ≤ codeEnd ∧ (pushInstr i).len > 0 ∧ savedReg i ≠ .rsp := by decide +kernel

private theorem alloc_bytes : decodeAt image 10 = some allocate := by decide +kernel

private theorem push_step (i : Fin 6) (s : Cpu) (live : s.ms = none) :
    let sp := s.regs.get .rsp - 8
    X86.step (pushInstr i) s = {s with
      regs := s.regs.set .rsp sp, mem := s.mem.writeSize .q sp (s.regs.get (savedReg i)),
      rip := s.rip + BitVec.ofNat 64 (pushLen i)} := by
  simp [pushInstr, X86.step, Cpu.stopped, live, Cpu.readOperand, Cpu.getReg, Cpu.push,
    Cpu.writeMem, Cpu.setReg, Cpu.setRip, Size.bytes, Value.writeView]

private theorem allocate_step (s : Cpu) (live : s.ms = none) :
    X86.step allocate s = {s with
      regs := s.regs.set .rsp (s.regs.get .rsp - 456), rip := s.rip + 7,
      flags := Flags.sub .q (s.regs.get .rsp) 456 s.flags} := by
  simp [allocate, X86.step, Cpu.stopped, live, wellFormed2, Operand.isMem, Cpu.readOperand, Cpu.getReg,
    Cpu.writeOperand, Cpu.setReg, Cpu.setRip, Cpu.setFlags, Value.writeView, Flags.subResult]

private def saveBase (s : Cpu) := s.regs.get .rsp - 48
private def saveSlot (i : Fin 6) := BitVec.ofNat 64 (40 - 8*i.val)
private def saveSP (s : Cpu) (n : Nat) := saveBase s + BitVec.ofNat 64 (48 - 8*n)

private theorem slots_distinct : ∀ i j : Fin 6, i ≠ j → ∀ k b : Fin 8,
    saveSlot j + BitVec.ofNat 64 k.val ≠ saveSlot i + BitVec.ofNat 64 b.val := by decide +kernel

private theorem slot_store (m : Mem) (a v p : Val)
    (sep : ∀ b : Fin 8, p ≠ a + BitVec.ofNat 64 b.val) :
    (m.writeSize .q a v).read p = m.read p := by
  rw [← byteView_read, byteView_write64, Crypto.ARM64.Imported.read8_write64_outside_ne _ _ _ _ sep]
  rfl

private theorem save_outside (s : Cpu) (m : Mem) (i : Fin 6) (p v : Val)
    (h : 48 ≤ (p-saveBase s).toNat) :
    (m.writeSize .q (saveBase s + saveSlot i) v).read p = m.read p := by
  apply slot_store
  intro b eq
  have bound : 40-8*i.val + b.val < 48 := by have := b.isLt; omega
  rw [eq, saveSlot, BitVec.add_assoc, ← BitVec.ofNat_add, Crypto.ARM64.Imported.address_delta,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  omega

def pushEvents (base sp : Val) : Nat → List Event
  | 0 => []
  | n+1 => pushEvents base sp n ++ if h : n < 6 then
      [(base+BitVec.ofNat 64 (pushPC n),pushInstr ⟨n,h⟩,
        [⟨true,sp-48+BitVec.ofNat 64 (40-8*n),8⟩])]
    else []

def entryEvents (base sp : Val) : List Event :=
  pushEvents base sp 6 ++ [(base+10,allocate,[])]

private structure Saved (base : Val) (s out : Cpu) (n : Nat) : Prop where
  live : out.ms = none
  pc : out.rip = base + BitVec.ofNat 64 (pushPC n)
  stack : out.regs.get .rsp = saveSP s n
  regs : ∀ r, r ≠ .rsp → out.regs.get r = s.regs.get r
  frame : ∀ p, 48 ≤ (p-saveBase s).toNat → out.mem.read p = s.mem.read p
  saved : ∀ i : Fin 6, i.val < n → out.mem.readSize .q (saveBase s + saveSlot i) = s.regs.get (savedReg i)
  observations : ObservedExecution base s (pushEvents base (s.regs.get .rsp) n) out

attribute [local irreducible] steps X86.step image

private theorem pushes_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (pc : s.rip = base) (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 48 ≤ (base + BitVec.ofNat 64 j - saveBase s).toNat)
    (n : Nat) (bound : n ≤ 6) : ∃ out, steps base n s = some out ∧ Saved base s out n := by
  induction n with
  | zero =>
    exact ⟨s, by simp [steps], ⟨live, by simpa [pushPC] using pc, by simp [saveSP,saveBase, BitVec.sub_eq_add_neg, BitVec.add_assoc],
      fun _ _ => rfl, fun _ _ => rfl, fun _ h => by omega,.nil _⟩⟩
  | succ n ih =>
    let i : Fin 6 := ⟨n,by omega⟩
    obtain ⟨mid, before, prev⟩ := ih (by omega)
    obtain ⟨decode, next, stop, length, other⟩ := push_table i
    have code : ImageLoaded base mid.mem := fun j hj => (prev.frame _ (sep j hj)).trans (loaded j hj)
    have fetched := fetch_at base mid (pushPC i.val) _ code prev.pc decode (by omega) (by omega)
    let out := X86.step (pushInstr i) mid
    have one : steps base 1 mid = some out := by simp [steps, stepInside, guard, Cpu.stopped, prev.live, fetched, out, show isReturn (pushInstr i) = false from rfl]
    have sp : mid.regs.get .rsp - 8 = saveBase s + saveSlot i := by
      rw [prev.stack, saveSP, saveSlot, show 48 - 8*n = (40 - 8*n)+8 by omega, BitVec.ofNat_add]
      simp [i, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    have slot : saveBase s + saveSlot i = saveSP s (n+1) := by
      unfold saveSlot saveSP
      rw [show 48-8*(n+1) = 40-8*n by omega]
    have reg := prev.regs _ other
    have mem : out.mem = mid.mem.writeSize .q (saveBase s + saveSlot i) (s.regs.get (savedReg i)) := by
      simp only [out, push_step _ _ prev.live, sp, reg]
    have seen : dataAccesses (pushInstr i) mid = some
        [⟨true,s.regs.get .rsp-48+BitVec.ofNat 64 (40-8*n),8⟩] := by
      change (some [⟨true,mid.regs.get .rsp-8,8⟩] : Option (List Crypto.ARM64.Imported.DataAccess)) = _
      rw [sp]
      rfl
    have pushed := steps_observe_single (off := pushPC i.val) one prev.pc decode (by omega) (by omega) seen
    have observations := prev.observations.append pushed
    refine ⟨out, steps_append before one, ⟨?_, ?_, ?_, ?_, ?_, ?_,
      by simpa only [pushEvents,dif_pos (show n < 6 by omega)] using observations⟩⟩
    · simp [out, push_step _ _ prev.live, prev.live]
    · change (X86.step (pushInstr i) mid).rip = _
      rw [push_step _ _ prev.live, ← next, prev.pc, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · simpa only [out, push_step _ _ prev.live, Regs.get_set_same] using sp.trans slot
    · intro r hr
      simpa [out, push_step _ _ prev.live, Regs.get_set_ne _ _ _ _ (Ne.symm hr)] using prev.regs r hr
    · intro p hp
      rw [mem, save_outside _ _ _ _ _ hp]
      exact prev.frame _ hp
    · intro j hj
      rw [mem]
      by_cases eq : i = j
      · subst j; exact read64_write64 _ _ _
      · have small : j.val < n := by
          have ne : n ≠ j.val := fun h => eq (Fin.ext h)
          omega
        refine Eq.trans (Mem.readN_congr _ _ _ 8 ?_) (prev.saved _ small)
        intro k hk
        apply slot_store
        intro b same
        rw [BitVec.add_assoc, BitVec.add_assoc] at same
        exact slots_distinct i j eq ⟨k,hk⟩ b (by simpa only [BitVec.add_comm (saveBase s), BitVec.add_sub_cancel] using congrArg (fun x => x - saveBase s) same)

structure EntryState (s out : Cpu) (base : Val) : Prop where
  live : out.ms = none
  pc : out.rip = base + 0x11
  stack : out.regs.get .rsp = s.regs.get .rsp - 504
  regs : ∀ r, r ≠ .rsp → out.regs.get r = s.regs.get r
  frame : ∀ p, 48 ≤ (p - (s.regs.get .rsp - 48)).toNat → out.mem.read p = s.mem.read p
  saved : ∀ i : Fin 6, out.mem.readSize .q
    ((s.regs.get .rsp - 48) + BitVec.ofNat 64 (40-8*i.val)) = s.regs.get (savedReg i)
  observations : ObservedExecution base s (entryEvents base (s.regs.get .rsp)) out

theorem entry_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (pc : s.rip = base) (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 48 ≤ (base + BitVec.ofNat 64 j - (s.regs.get .rsp - 48)).toNat) :
    ∃ out, steps base 7 s = some out ∧ EntryState s out base := by
  obtain ⟨mid, run, state⟩ := pushes_loaded base s live pc loaded sep 6 (by decide)
  have code : ImageLoaded base mid.mem := fun j hj => (state.frame _ (sep j hj)).trans (loaded j hj)
  have fetched := fetch_at base mid 10 allocate code state.pc alloc_bytes (by decide) (by decide)
  let out := X86.step allocate mid
  have one : steps base 1 mid = some out := by simp [steps, stepInside, guard, Cpu.stopped, state.live, fetched,out, show isReturn allocate = false from rfl]
  have seen := steps_observe_single one state.pc alloc_bytes (by decide) (by decide) rfl
  refine ⟨out, steps_append run one, ⟨?_, ?_, ?_, ?_, ?_, ?_,state.observations.append seen⟩⟩
  · simp [out, allocate_step _ state.live, state.live]
  · simp [out, allocate_step _ state.live, state.pc, pushPC, BitVec.add_assoc]
  · simp [out, allocate_step _ state.live, state.stack, saveSP, saveBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · intro r h
    simpa [out, allocate_step _ state.live, Regs.get_set_ne _ _ _ _ (Ne.symm h)] using state.regs r h
  · exact fun p hp => (congrArg (fun m : Mem => m.read p) (show out.mem = mid.mem by
      simp [out, allocate_step _ state.live])).trans (state.frame p hp)
  · intro i
    simpa [out, allocate_step _ state.live, saveBase, saveSlot] using state.saved i i.isLt

end Crypto.X86_64
