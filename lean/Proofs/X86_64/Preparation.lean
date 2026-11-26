import Proofs.X86_64.PrepareCopy
import Proofs.X86_64.PaddingBytes
import Proofs.X86_64.InitialHash
import Proofs.ARM64.ImportedReferenceLayout

namespace Crypto.X86_64
open X86
open Crypto.ARM64.Imported (lengthOffset paddingBlockCount)
open Crypto.Reference.ByteLayout

private theorem reference_tail (data : ByteArray) (v : Val) (size : v.toNat = data.size) (i : Nat)
    (hi : i < lengthOffset (data.size%64)+8) :
    (if lengthOffset (data.size%64) ≤ i ∧ i < lengthOffset (data.size%64)+8 then
       (v <<< 3).extractLsb' (8*(7-(i-lengthOffset (data.size%64)))) 8
     else if i = data.size%64 then 128 else if i < data.size%64 then (data.get! (data.size/64*64+i)).toBitVec else 0) =
      ((implPaddedBytes data).get! (data.size/64*64+i)).toBitVec := by
  let rem := data.size%64
  let off := lengthOffset rem
  have lengthStart := Crypto.ARM64.Imported.padded_tail_length_start data
  change data.size+1+zerosCount data = data.size/64*64+off at lengthStart
  have limits := Crypto.ARM64.Imported.lengthOffset_bounds rem (Nat.mod_lt _ (by decide))
  change rem < off ∧ off+8 ≤ 128 at limits
  have full : data.size/64*64+rem = data.size := by dsimp [rem]; omega
  change i < off+8 at hi
  have total : data.size/64*64+i < (implPaddedBytes data).size := by
    rw [Crypto.ARM64.Imported.padded_tail_size]; change _ < data.size/64*64+off+8; omega
  rw [get!_implPaddedBytes_eq data _ total]
  by_cases a : i < rem
  · rw [if_neg (by omega : ¬ (off ≤ i ∧ i < off+8)),if_neg (by omega : i ≠ rem),if_pos a,
      if_pos (by omega : data.size/64*64+i < data.size)]
  · rw [if_neg (by omega : ¬ data.size/64*64+i < data.size)]
    by_cases b : i = rem
    · rw [if_neg (by omega : ¬ (off ≤ i ∧ i < off+8)),if_pos b,
        if_pos (by omega : data.size/64*64+i = data.size)]; rfl
    · rw [if_neg (by omega : data.size/64*64+i ≠ data.size)]
      by_cases c : i < off
      · rw [if_neg (by omega : ¬ (off ≤ i ∧ i < off+8)),if_neg b,if_neg a,
          if_pos (by omega : data.size/64*64+i < data.size+1+zerosCount data)]; rfl
      · rw [if_pos (by omega : off ≤ i ∧ i < off+8),
          if_neg (by omega : ¬ data.size/64*64+i < data.size+1+zerosCount data),
          show data.size/64*64+i-(data.size+1+zerosCount data) = i-off by omega]
        have bits := Crypto.ARM64.Imported.count_length_bits v
        rw [size] at bits
        rw [← bits]
        exact (Crypto.ARM64.Imported.reference_length_byte _ ⟨i-off,by omega⟩).symm

def prepKept (sp p : Val) : Prop := 288 ≤ (p-sp).toNat ∧ 128 ≤ (p-(sp+288)).toNat ∧
  8 ≤ (p-(sp+424)).toNat ∧ 8 ≤ (p-(sp+432)).toNat ∧ 8 ≤ (p-(sp+440)).toNat

theorem prepKept_of_outside (sp p : Val) (h : 512 ≤ (p-sp).toNat) : prepKept sp p :=
  ⟨Nat.le_trans (by decide) h,Crypto.ARM64.Imported.region_store_delta _ _ 288 512 128 (by decide) h,
    Crypto.ARM64.Imported.region_store_delta _ _ 424 512 8 (by decide) h,
    Crypto.ARM64.Imported.region_store_delta _ _ 432 512 8 (by decide) h,
    Crypto.ARM64.Imported.region_store_delta _ _ 440 512 8 (by decide) h⟩

private theorem fixed_offset (sp : Val) (n : Nat) (b : Fin 8) :
    (sp+BitVec.ofNat 64 n+BitVec.ofNat 64 b.val-sp).toNat =
      (BitVec.ofNat 64 n+BitVec.ofNat 64 b.val).toNat := by
  rw [BitVec.add_assoc,BitVec.add_comm sp,BitVec.add_sub_cancel]

def prepareEvents (base sp payload : Val) (len : Nat) : List Event :=
  prepareTailEvents base sp payload len ++ suffixEvents base sp (len%64) ++ initialHashEvents base sp

structure PreparedState (base : Val) (s out : Cpu) (data : ByteArray) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x15c
  stack : out.regs.get .rsp = s.regs.get .rsp
  ptr : out.regs.get .rbp = s.regs.get .rbp
  constants : out.regs.get .rdi = base+0x390
  phase : phase out = 0
  count : blocksLeft out = BitVec.ofNat 64 (data.size/64)
  pads : paddingCount out = BitVec.ofNat 64 (paddingBlockCount data)
  hash : hashWords (project out) = Crypto.Reference.WordModel.H0_256
  padding : ∀ i : Fin (64*paddingBlockCount data), out.mem.read (padBase s+BitVec.ofNat 64 i.val) =
    ((implPaddedBytes data).get! (data.size/64*64+i.val)).toBitVec
  frame : ∀ p, prepKept (s.regs.get .rsp) p → out.mem.read p = s.mem.read p
  observations : ObservedExecution base s (prepareEvents base (s.regs.get .rsp) (s.regs.get .rbp) data.size) out

attribute [local irreducible] steps image hashWords EthLib.Cryptography.Hash.Sha256.Spec.initial

theorem preparation_loaded (base : Val) (s : Cpu) (data : ByteArray) (live : s.ms = none)
    (pc : s.rip = base+0x25) (loaded : ImageLoaded base s.mem)
    (sites : CopySites base) (suffixPC : canonical (base+0xf8) = true) (size : (s.regs.get .rcx).toNat = data.size)
    (codeSep : ∀ j, j < image.size → 512 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (inputSep : ∀ i : Fin data.size, 512 ≤ (s.regs.get .rbp+BitVec.ofNat 64 i.val-s.regs.get .rsp).toNat)
    (input : ∀ i : Fin data.size, s.mem.read (s.regs.get .rbp+BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec) :
    ∃ out, steps base (48+6*(data.size%64)+optionalMove (data.size%64)) s = some out ∧ PreparedState base s out data := by
  let r := data.size%64
  have small : r < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨a,copy,tail⟩ := prepare_tail_loaded base s data live pc loaded sites size codeSep inputSep input
  have kept j (hj : j < image.size) := prepKept_of_outside _ _ (codeSep j hj)
  have codeA : ImageLoaded base a.mem := fun j hj =>
    (tail.frame _ (kept j hj).2.1 (kept j hj).2.2.1).trans (loaded j hj)
  have padA : padBase a = padBase s := by simp only [padBase,tail.stack]
  obtain ⟨b,suffix,suf⟩ := padding_suffix_loaded base a r tail.live tail.pc codeA tail.rem small suffixPC
    (fun j hj => by rw [tail.stack]; exact Nat.le_trans (by decide : 448 ≤ 512) (codeSep j hj))
  have spB := suf.stack.trans tail.stack
  have bm (p : Val) (ph : 128 ≤ (p-padBase s).toNat) (ch : 8 ≤ (p-(s.regs.get .rsp+440)).toNat) :
      b.mem.read p = a.mem.read p := by
    rw [suf.mem,suffix_frame _ _ small _ (by rw [padA]; exact ph) (by rw [tail.stack]; exact ch)]
  have codeB : ImageLoaded base b.mem := fun j hj => (bm _ (kept j hj).2.1 (kept j hj).2.2.2.2).trans (codeA j hj)
  obtain ⟨out, init, post⟩ := initial_hash_loaded base b suf.live suf.pc codeB
    (fun j hj => by rw [spB]; exact Nat.le_trans (by decide : 440 ≤ 512) (codeSep j hj))
  have sp := post.stack.trans spB
  have frame (p : Val) (ph : 288 ≤ (p-s.regs.get .rsp).toNat) (mh : 8 ≤ (p-(s.regs.get .rsp+432)).toNat) :
      out.mem.read p = b.mem.read p := post.frame _ (by rw [spB]; exact ph) (by rw [spB]; exact mh)
  have slot (d : Nat) (h : ∀ j : Fin 8, 288 ≤ (BitVec.ofNat 64 d+BitVec.ofNat 64 j.val).toNat ∧
      8 ≤ ((BitVec.ofNat 64 d+BitVec.ofNat 64 j.val)-432).toNat) :
      out.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) = b.mem.readSize .q (s.regs.get .rsp+BitVec.ofNat 64 d) := by
    apply Mem.readN_congr _ _ _ 8
    intro j hj
    apply frame
    · rw [fixed_offset _ _ ⟨j,hj⟩]; exact (h ⟨j,hj⟩).1
    · rw [BitVec.add_assoc,stack_delta]; exact (h ⟨j,hj⟩).2
  have choice := suf.observations
  have iv := post.observations
  rw [tail.stack] at choice
  rw [spB] at iv
  have observe : ObservedExecution base s (prepareEvents base (s.regs.get .rsp) (s.regs.get .rbp) data.size) out :=
    by simpa only [prepareEvents,List.append_assoc] using tail.observations.append (choice.append iv)
  refine ⟨out,?_,⟨post.live,post.pc,sp,post.ptr.trans (suf.payload.trans tail.ptr),post.constants,post.phase,?_,?_,post.hash,?_,?_,observe⟩⟩
  · rw [show 48+6*(data.size%64)+optionalMove (data.size%64) = (28+6*(data.size%64))+((9+optionalMove r)+11) by dsimp [r]; omega]
    exact steps_append copy (steps_append suffix init)
  · unfold blocksLeft
    rw [sp]
    apply Eq.trans (slot 424 (by decide +kernel))
    apply Eq.trans _ tail.count
    unfold blocksLeft
    rw [tail.stack]
    apply Mem.readN_congr _ _ _ 8
    intro j hj
    apply bm
    · unfold padBase; rw [BitVec.add_assoc,stack_delta]
      exact (by decide +kernel : ∀ b : Fin 8, 128 ≤ (424+BitVec.ofNat 64 b.val-288).toNat) ⟨j,hj⟩
    · rw [BitVec.add_assoc,stack_delta]
      exact (by decide +kernel : ∀ b : Fin 8, 8 ≤ (424+BitVec.ofNat 64 b.val-440).toNat) ⟨j,hj⟩
  · unfold paddingCount
    rw [sp]
    apply Eq.trans (slot 440 (by decide +kernel))
    rw [suf.mem,← tail.stack]
    exact suffix_count a r
  · intro i
    have ib := Nat.lt_of_lt_of_eq i.isLt (Crypto.ARM64.Imported.paddingBlockCount_bytes data)
    have limits := Crypto.ARM64.Imported.lengthOffset_bounds r small
    let j : Fin 128 := ⟨i.val,by change i.val < lengthOffset r+8 at ib; omega⟩
    have off : padBase s+BitVec.ofNat 64 i.val = s.regs.get .rsp+BitVec.ofNat 64 (288+i.val) := by
      simp [padBase,BitVec.ofNat_add,BitVec.add_assoc]
    rw [frame]
    · rw [suf.mem,← padA,suffix_byte _ _ small j,padA,tail.bytes j]
      exact reference_tail data _ ((congrArg BitVec.toNat tail.size).trans size) _ ib
    · rw [off,Crypto.ARM64.Imported.address_delta,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have jj : i.val < 128 := j.isLt; omega)]
      omega
    · rw [off,stack_delta]
      exact (by decide +kernel : ∀ b : Fin 128, 8 ≤ (BitVec.ofNat 64 (288+b.val)-432).toNat) j
  · intro p hp
    exact (frame _ hp.1 hp.2.2.2.1).trans ((bm _ hp.2.1 hp.2.2.2.2).trans (tail.frame _ hp.2.1 hp.2.2.1))

end Crypto.X86_64
