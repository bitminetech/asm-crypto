import Proofs.X86_64.TailCopy
import Proofs.X86_64.Length
import Proofs.X86_64.PhaseSwitch

namespace Crypto.X86_64
open X86

structure CopySites (base : Val) : Prop where
  done : canonical (base+0xdf) = true
  back : canonical (base+0xc9) = true

def prepareTailEvents (base sp payload : Val) (len : Nat) : List Event :=
  frameFragment base sp 0x25 17 ++ frameFragment base sp 0xa7 9 ++
    tailCopyEvents base sp (payload+BitVec.ofNat 64 (len/64*64)) (len%64)

structure TailReady (base : Val) (s out : Cpu) (data : ByteArray) : Prop where
  live : out.ms = none
  pc : out.rip = base+0xdf
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rbp = s.regs.get .rbp
  size : out.regs.get .rcx = s.regs.get .rcx
  rem : (out.regs.get .r8).toNat = data.size%64
  count : blocksLeft out = BitVec.ofNat 64 (data.size/64)
  bytes : ∀ i : Fin 128, out.mem.read (padBase s+BitVec.ofNat 64 i.val) =
    if i.val < data.size%64 then (data.get! (data.size/64*64+i.val)).toBitVec else 0
  frame : ∀ p, 128 ≤ (p-padBase s).toNat → 8 ≤ (p-(s.regs.get .rsp+424)).toNat → out.mem.read p = s.mem.read p
  observations : ObservedExecution base s
    (prepareTailEvents base (s.regs.get .rsp) (s.regs.get .rbp) data.size) out

attribute [local irreducible] steps image

theorem prepare_tail_loaded (base : Val) (s : Cpu) (data : ByteArray)
    (live : s.ms = none) (pc : s.rip = base+0x25) (loaded : ImageLoaded base s.mem)
    (sites : CopySites base) (size : (s.regs.get .rcx).toNat = data.size)
    (codeSep : ∀ j, j < image.size → 512 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (inputSep : ∀ i : Fin data.size, 512 ≤ (s.regs.get .rbp+BitVec.ofNat 64 i.val-s.regs.get .rsp).toNat)
    (input : ∀ i : Fin data.size, s.mem.read (s.regs.get .rbp+BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec) :
    ∃ out, steps base (28+6*(data.size%64)) s = some out ∧ TailReady base s out data := by
  let rem := data.size%64
  have small : rem < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨z, zeroRun, zo, zp, zr, zeros, zFrame⟩ := zero_padding_loaded base s live pc loaded
    (fun j hj => Nat.le_trans (by decide : 416 ≤ 512) (codeSep j hj))
  have zsp : z.regs.get .rsp = s.regs.get .rsp := by simp [zr,Regs.get_set_ne]
  have zbp : z.regs.get .rbp = s.regs.get .rbp := by simp [zr,Regs.get_set_ne]
  have zlen : z.regs.get .rcx = s.regs.get .rcx := by simp [zr,Regs.get_set_ne]
  have padSep (p : Val) (outside : 512 ≤ (p-s.regs.get .rsp).toNat) : 128 ≤ (p-padBase s).toNat :=
    Crypto.ARM64.Imported.region_store_delta _ _ 288 512 128 (by decide) outside
  have countSep (p : Val) (outside : 512 ≤ (p-s.regs.get .rsp).toNat) : 8 ≤ (p-(s.regs.get .rsp+424)).toNat :=
    Crypto.ARM64.Imported.region_store_delta _ _ 424 512 8 (by decide) outside
  have codeZ : ImageLoaded base z.mem := fun j hj => (zFrame _ (padSep _ (codeSep j hj))).trans (loaded j hj)
  obtain ⟨a, setup, ready⟩ := length_setup_loaded base z zo zp codeZ
    (fun j hj => by rw [zsp]; exact Nat.le_trans (by decide : 432 ≤ 512) (codeSep j hj))
  have sp := ready.stack.trans zsp
  have area : padBase a = padBase s := by simp only [padBase,sp]
  have stored : a.mem = z.mem.writeSize .q (s.regs.get .rsp+424) (BitVec.ofNat 64 (data.size/64)) := by
    simpa only [zlen,zsp,size] using ready.mem
  have stable (p : Val) (ph : 128 ≤ (p-padBase s).toNat) (ch : 8 ≤ (p-(s.regs.get .rsp+424)).toNat) :
      a.mem.read p = s.mem.read p := by rw [stored,counter_frame _ _ _ _ ch,zFrame _ ph]
  have codeA : ImageLoaded base a.mem := fun j hj =>
    (stable _ (padSep _ (codeSep j hj)) (countSep _ (codeSep j hj))).trans (loaded j hj)
  have r8 : (a.regs.get .r8).toNat = rem := by
    rw [ready.remainder,zlen,size,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have tail j : a.regs.get .r9+BitVec.ofNat 64 j = s.regs.get .rbp+BitVec.ofNat 64 (data.size/64*64+j) := by
    rw [ready.tail,zbp,zlen,size,BitVec.ofNat_add,BitVec.add_assoc]
  have src j (hj : j < rem) : 512 ≤ (a.regs.get .r9+BitVec.ofNat 64 j-s.regs.get .rsp).toNat := by
    rw [tail]; apply inputSep ⟨data.size/64*64+j,by dsimp [rem] at hj; omega⟩
  obtain ⟨out, copy, exitPC, post, copyTrace⟩ := tail_copy_loaded base a ready.live ready.pc codeA ready.index
    ⟨sites.done,sites.back⟩ rem r8 small
    (fun j hj => by rw [area]; exact Nat.le_trans (by decide : 64 ≤ 128) (padSep _ (codeSep j hj)))
    (fun j hj => by rw [area]; exact Nat.le_trans (by decide : 64 ≤ 128) (padSep _ (src j hj)))
  have after (p : Val) (hp : rem ≤ (p-padBase s).toNat) : out.mem.read p = a.mem.read p :=
    post.frame p (by rw [area]; exact hp)
  have stack := (post.regs .rsp (by decide) (by decide)).trans sp
  have zeroTrace := steps_observe_fragment zeroRun pc (by decide +kernel)
  have setupTrace := steps_observe_fragment setup zp (by decide +kernel)
  have srcAddr : a.regs.get .r9 = s.regs.get .rbp+BitVec.ofNat 64 (data.size/64*64) := by
    simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero,Nat.add_zero] using tail 0
  rw [zsp] at setupTrace
  rw [sp,srcAddr] at copyTrace
  have observations : ObservedExecution base s
      (prepareTailEvents base (s.regs.get .rsp) (s.regs.get .rbp) data.size) out :=
    by simpa only [prepareTailEvents,List.append_assoc] using zeroTrace.append (setupTrace.append copyTrace)
  refine ⟨out, ?_, ⟨post.live,exitPC,stack,(post.regs _ (by decide) (by decide)).trans (ready.ptr.trans zbp),
    (post.regs _ (by decide) (by decide)).trans (ready.size.trans zlen),
    (congrArg BitVec.toNat (post.regs .r8 (by decide) (by decide))).trans r8,?_,?_,?_,observations⟩⟩
  · rw [show 28+6*(data.size%64) = 17+(9+(6*rem+2)) by dsimp [rem]; omega]
    exact steps_append zeroRun (steps_append setup copy)
  · unfold blocksLeft
    rw [stack]
    apply Eq.trans _ (show a.mem.readSize .q (s.regs.get .rsp+424) = _ by rw [stored,read64_write64])
    apply Mem.readN_congr _ _ _ 8
    intro b hb
    apply after
    unfold padBase
    rw [BitVec.add_assoc,stack_delta]
    have finite : ∀ j : Fin 8, 64 ≤ (424+BitVec.ofNat 64 j.val-288).toNat := by decide +kernel
    exact Nat.le_trans (by omega) (finite ⟨b,hb⟩)
  · intro i
    by_cases h : i.val < rem
    · rw [if_pos h,← area,post.bytes _ h,stable _ (padSep _ (src _ h)) (countSep _ (src _ h)),tail]
      exact input ⟨_,by dsimp [rem] at h; omega⟩
    · rw [if_neg h,after,stored,counter_frame]
      · exact zeros i
      · unfold padBase; rw [BitVec.add_assoc,stack_delta]
        have finite : ∀ j : Fin 128, 8 ≤ (288+BitVec.ofNat 64 j.val-424).toNat := by decide +kernel
        exact finite i
      · rw [Crypto.ARM64.Imported.address_delta,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
        omega
  · intro p ph ch
    exact (after _ (Nat.le_trans (by omega) ph)).trans (stable p ph ch)

end Crypto.X86_64
