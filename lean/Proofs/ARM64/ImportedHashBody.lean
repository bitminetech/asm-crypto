import Proofs.ARM64.ImportedOuterComplete
import Proofs.ARM64.ImportedExit

/-!
Composition of both recorded block phases and the final digest/return path.
The stored digest is the imported FIPS compression fold over the original full
blocks and the original private padding blocks. The proof retains the modeled
state/ABI frame, zero status, restored SP and original link-register return.
Entry/preparation, reference byte-array fold, fetched execution, access/trace
bounds and the full architecture equal baseline remain separate obligations.
-/
namespace Crypto.ARM64.Imported

theorem padding_word_outside (sp : BitVec 64) (i : Fin 2) (j : Fin 16) (b : Fin 4) :
    288 ≤ (sp + 288#64 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - sp).toNat := by
  have ih := i.isLt
  have jh := j.isLt
  have bh := b.isLt
  have bound : 288 + (64 * i.val + 4 * j.val) + b.val < 2 ^ 64 := by omega
  have address : sp + 288#64 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val =
      sp + BitVec.ofNat 64 (288 + (64 * i.val + 4 * j.val) + b.val) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  rw [address, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

theorem padding_block_of_frame (m before : Arm64.Memory) (sp : BitVec 64)
    (frame : ∀ p, 288 ≤ (p - sp).toNat → m.cells p = before.cells p) (i : Fin 2) :
    memoryBlock m (sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) =
      memoryBlock before (sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) := by
  apply Vector.ext
  intro j hj
  simp only [memoryBlock, Vector.getElem_ofFn]
  apply congrArg reverseWord
  apply read32_of_cells
  intro b
  apply frame
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using padding_word_outside sp i ⟨j, hj⟩ b

def hashPhasesCode (full padding : Nat) :=
  outerLoopCode full ++ (paddingPhaseCode ++ (outerLoopCode padding ++ digestGateCode))

theorem hash_phases (s : Arm64.State) (ready : BlockReady s)
    (full padding : Nat) (fullBound : full < 2 ^ 64) (paddingBound : padding ≤ 2)
    (count : s.readReg64 .x3 = BitVec.ofNat 64 full)
    (phase : s.readReg64 .x4 = 0#64) (padCount : s.readReg64 .x6 = BitVec.ofNat 64 padding)
    (hr : ∀ (i : Fin full) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin full) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (padRead : ∀ i : Fin 32, s.mem.canRead ((s.sp + 288#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ out, runWords (hashPhasesCode full padding) s = some out ∧
      nonMemory out = nonMemory s ∧ nonvolatile out = nonvolatile s ∧
      out.pc = s.pc + 360#64 ∧ out.readReg64 .x0 = s.readReg64 .x0 ∧
      out.readReg64 .x1 = s.readReg64 .x1 ∧ out.readReg64 .x4 = 1#64 ∧
      out.readReg64 .x6 = s.readReg64 .x6 ∧ BlockReady out ∧
      savedHash out = Fin.foldl padding
        (fun H (i : Fin padding) => SHS.SHA256.compress H
          (memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val))))
        (Fin.foldl full
          (fun H (i : Fin full) => SHS.SHA256.compress H
            (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)))) (savedHash s)) ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) := by
  obtain ⟨complete, hc, cf, cp, _, _, ch, readyComplete, cframe, cread⟩ :=
    outer_loop s ready full fullBound count hr sep
  obtain ⟨switched, hs, postSwitch⟩ := exists_of_map_some _ _ _
    (padding_phase complete (cf.x4.trans phase))
  simp only [blockControlView, Prod.mk.injEq] at postSwitch
  obtain ⟨sst, snv, spc, s0, s1, s2, s3, s4, _, s6⟩ := postSwitch
  have smem := congrArg Arm64.State.mem sst
  change switched.mem = complete.mem at smem
  have ssp := congrArg Arm64.State.sp sst
  change switched.sp = complete.sp at ssp
  have snm := congrArg nonMemory sst
  have stateSwitch : nonMemory switched = nonMemory complete := by
    simpa only [nonMemory_stable] using snm
  have stackSwitch : switched.sp = s.sp := ssp.trans cf.sp
  have pointerSwitch : switched.readReg64 .x2 = s.sp + 288#64 := by rw [s2, cf.sp]
  have countSwitch : switched.readReg64 .x3 = BitVec.ofNat 64 padding :=
    s3.trans (cf.x6.trans padCount)
  have reads (i : Fin padding) (j : Fin 16) : switched.mem.canRead
      (switched.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true := by
    have ih := i.isLt
    have jh := j.isLt
    have address : 64 * i.val + 4 * j.val = 4 * (16 * i.val + j.val) := by omega
    rw [pointerSwitch, smem, address]
    exact cread _ _ (padRead ⟨16 * i.val + j.val, by omega⟩)
  have padSep (i : Fin padding) (j : Fin 16) (b : Fin 4) :
      288 ≤ (switched.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) +
        BitVec.ofNat 64 b.val - switched.sp).toNat := by
    rw [pointerSwitch, stackSwitch]
    exact padding_word_outside s.sp ⟨i.val, by have := i.isLt; omega⟩ j b
  obtain ⟨padded, hp, pf, pp, _, _, ph, readyPadded, pframe, pread⟩ :=
    outer_loop switched (readyComplete.of_stable sst s0) padding (by omega) countSwitch reads padSep
  have nonzero : padded.readReg64 .x4 ≠ 0#64 := by rw [pf.x4, s4]; decide +kernel
  have gate := digest_gate padded nonzero
  let out := padded.setPC (padded.pc + 20#64)
  have tail := runWords_append_success hp gate
  have phases := runWords_append_success hs tail
  have whole := runWords_append_success hc phases
  have lastFrame := OuterFrame.setPC padded (padded.pc + 20#64)
  have finalState : nonMemory out = nonMemory s :=
    lastFrame.state.trans (pf.state.trans (stateSwitch.trans cf.state))
  have blocks :
      (fun H (i : Fin padding) => SHS.SHA256.compress H
        (memoryBlock switched.mem (switched.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)))) =
      (fun H (i : Fin padding) => SHS.SHA256.compress H
        (memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val)))) := by
    funext H i
    rw [pointerSwitch, smem]
    exact congrArg (SHS.SHA256.compress H)
      (padding_block_of_frame complete.mem s.mem s.sp cframe ⟨i.val, by have := i.isLt; omega⟩)
  have hashSwitch : savedHash switched = savedHash complete := by
    unfold savedHash
    rw [smem, ssp]
  rw [blocks, hashSwitch, ch] at ph
  refine ⟨out, whole, finalState,
    lastFrame.nv.trans (pf.nv.trans (snv.trans cf.nv)), ?_,
    lastFrame.x0.trans (pf.x0.trans (s0.trans cf.x0)),
    lastFrame.x1.trans (pf.x1.trans (s1.trans cf.x1)),
    lastFrame.x4.trans (pf.x4.trans s4),
    lastFrame.x6.trans (pf.x6.trans (s6.trans cf.x6)),
    readyPadded.transport rfl rfl lastFrame.x0, ph, ?_, ?_⟩
  · change padded.pc + 20#64 = _
    rw [pp, spc, cp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)
  · intro p h
    change padded.mem.cells p = _
    have dist : 288 ≤ (p - switched.sp).toNat := by rw [stackSwitch]; exact h
    have first := pframe p dist
    rw [smem] at first
    exact first.trans (cframe p h)
  · intro a n read
    change padded.mem.canRead a n = true
    exact pread a n (by rw [smem]; exact cread a n read)

def phasesHash (s : Arm64.State) (full padding : Nat) : Vector (BitVec 32) 8 :=
  Fin.foldl padding
    (fun H (i : Fin padding) => SHS.SHA256.compress H
      (memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val))))
    (Fin.foldl full
      (fun H (i : Fin full) => SHS.SHA256.compress H
        (memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)))) (savedHash s))

def hashBodyCode (full padding : Nat) := hashPhasesCode full padding ++ exitCode

theorem hash_body (s : Arm64.State) (ready : BlockReady s)
    (full padding : Nat) (fullBound : full < 2 ^ 64) (paddingBound : padding ≤ 2)
    (count : s.readReg64 .x3 = BitVec.ofNat 64 full)
    (phase : s.readReg64 .x4 = 0#64) (padCount : s.readReg64 .x6 = BitVec.ofNat 64 padding)
    (hr : ∀ (i : Fin full) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin full) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (padRead : ∀ i : Fin 32, s.mem.canRead ((s.sp + 288#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputWrite : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputOutside : ∀ (i : Fin 8) (b : Fin 4),
      288 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) :
    ∃ out, runWords (hashBodyCode full padding) s = some out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp + 416#64 ∧ out.pc = s.readReg64 .x30 ∧
      out.readReg64 .x0 = 0#64 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      memoryBytes32 out.mem (s.readReg64 .x1) = digestBytes (phasesHash s full padding) := by
  obtain ⟨hashed, he, nm, nv, _, _, x1, _, _, readyHash, hash, frame, _⟩ :=
    hash_phases s ready full padding fullBound paddingBound count phase padCount hr sep padRead
  have writes (i : Fin 8) : hashed.mem.canWrite (hashed.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [x1]
    exact (canWrite32_of_cells _ (fun b => frame _ (outputOutside i b))).trans (outputWrite i)
  obtain ⟨out, ho, post⟩ := exists_of_map_some _ _ _ (exit_stores_bytes hashed readyHash.hashRead writes)
  simp only [Prod.mk.injEq] at post
  obtain ⟨bytes, _, state, sp, pc, nvOut, status, x1Out⟩ := post
  have whole := runWords_append_success he ho
  have spHash := congrArg Arm64.State.sp nm
  change hashed.sp = s.sp at spHash
  have lr := congrFun nv ⟨12, by decide⟩
  change hashed.readReg64 .x30 = s.readReg64 .x30 at lr
  have erase := congrArg (fun st : Arm64.State => { st with sp := 0#64 }) nm
  change returnStable hashed = returnStable s at erase
  have output := x1Out.trans x1
  refine ⟨out, whole, state.trans erase, nvOut.trans nv, ?_, pc.trans lr, status, output, ?_⟩
  · rw [sp, spHash]
  · rw [← output]
    exact bytes.trans (congrArg digestBytes hash)

end Crypto.ARM64.Imported
