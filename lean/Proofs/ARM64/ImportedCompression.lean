import Proofs.ARM64.ImportedHashFrame
import Proofs.ARM64.ImportedScheduleCycle

/-!
Composition of hash-word loading, 64 recorded round cycles and feed-forward.
The stored hash is exactly the imported FIPS compression result for a block
whose schedule is already in the stack workspace. The conclusion also retains
the PC/counter and non-memory state frame, cells outside the 288-byte
schedule/hash workspace, read permissions and write permissions. Loading the message/schedule,
instruction fetching, whole-call bounds and `equal` remain separate obligations.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.SHA256.Foldl.Sequential

theorem initVars_eq (H : Vector (BitVec 32) 8) : initVars H = H := by
  apply Vector.ext
  intro i hi
  simp [initVars]

theorem compress_eq_rounds (H : Vector (BitVec 32) 8) (M : Vector (BitVec 32) 16) :
    addH H (Fin.foldl 64
      (fun work (i : Fin 64) => specRoundStep (SHS.SHA256.schedule M) i.val work) H) =
      SHS.SHA256.compress H M := by
  have result := spec_compress_eq_seq H M
  simp only [specCompressSeq, initVars_eq] at result
  exact result.symm

theorem runWords_append_success {xs ys : List (BitVec 32)} {s mid out : Arm64.State}
    (hx : runWords xs s = some mid) (hy : runWords ys mid = some out) :
    runWords (xs ++ ys) s = some out := by
  have bindEq := congrArg (fun r : Option Arm64.State => r.bind (runWords ys)) hx
  exact (runWords_append xs ys s).trans (bindEq.trans hy)

def compressionCode : List (BitVec 32) :=
  initialLoadCode ++ ((List.replicate 64 roundCycleCode).flatten ++ feedForwardCode)

theorem compression (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hW : wordVector 64 s.mem s.sp = SHS.SHA256.schedule M)
    (hhr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hhw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ out, runWords compressionCode s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 224#64 ∧ out.readReg64 .x5 = 64#64 ∧
      wordVector 8 out.mem (out.sp + 256#64) =
        SHS.SHA256.compress (wordVector 8 s.mem (s.sp + 256#64)) M ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ a n, out.mem.canWrite a n = s.mem.canWrite a n) := by
  obtain ⟨loaded, hl, postLoad⟩ := exists_of_map_some _ _ _ (initial_load s hhr)
  simp only [Prod.mk.injEq] at postLoad
  obtain ⟨loadWork, loadStable, loadPC, loadNV, l0, l1, l2, l3, l4, l5, l6⟩ := postLoad
  have fl : CoreFrame s loaded :=
    ⟨controlStable_of_stable loadStable, loadNV, l0, l1, l2, l3, l4, l6⟩
  have kr (i : Fin 64) : loaded.mem.canRead (loaded.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fl.mem, fl.x0]
    exact hkr i
  have wr (i : Fin 64) : loaded.mem.canRead (loaded.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fl.mem, fl.sp]
    exact hwr i
  have kv (i : Fin 64) : loaded.mem.read32 (loaded.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]! := by
    rw [fl.mem, fl.x0]
    exact hkv i
  have wv (i : Fin 64) : loaded.mem.read32 (loaded.sp + BitVec.ofNat 64 (4 * i.val)) = (SHS.SHA256.schedule M)[i.val]! := by
    rw [fl.mem, fl.sp]
    have words := congrArg (fun W : Vector (BitVec 32) 64 => W[i.val]!) hW
    simpa [wordVector, i.isLt] using words
  obtain ⟨rounded, hr, fr, roundPC, roundCount, roundWork⟩ := round_loop loaded
    (SHS.SHA256.schedule M) (by rw [fl.aligned]; exact hsp) l5 kr wr kv wv
  have allFrame := fl.trans fr
  have rr (i : Fin 8) : rounded.mem.canRead ((rounded.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [allFrame.mem, allFrame.sp]
    exact hhr i
  have ww (i : Fin 8) : rounded.mem.canWrite ((rounded.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [allFrame.mem, allFrame.sp]
    exact hhw i
  have sum : hashSum rounded = SHS.SHA256.compress (wordVector 8 s.mem (s.sp + 256#64)) M := by
    unfold hashSum
    rw [allFrame.mem, allFrame.sp, roundWork, loadWork]
    exact compress_eq_rounds _ M
  obtain ⟨out, ho, post⟩ := exists_of_map_some _ _ _ (feed_forward rounded rr ww)
  simp only [Prod.mk.injEq] at post
  obtain ⟨ram, _work, stableOut, pc, nv, f0, f1, f2, f3, f4, f5, f6⟩ := post
  have memOut := congrArg Arm64.State.mem stableOut
  change out.mem = storeHashWords rounded at memOut
  have eraseOut : nonMemory out = nonMemory rounded := by
    have result := congrArg nonMemory stableOut
    simpa only [nonMemory_stable, nonMemory_set_mem] using result
  have eraseRound : nonMemory rounded = nonMemory s := by
    have result := congrArg nonMemory allFrame.1
    simpa only [nonMemory_controlStable] using result
  have roundedSP := allFrame.sp
  have roundedMem := allFrame.mem
  obtain ⟨_cs, nvRound, r0, r1, r2, r3, r4, r6⟩ := allFrame
  have roundWords := (runCycles_words roundCycleCode 64 loaded).symm.trans hr
  refine ⟨out, ?_, ?_, ?_, f5.trans roundCount, ram.trans sum, ?_, ?_, ?_⟩
  · have tail := runWords_append_success roundWords ho
    have whole := runWords_append_success hl tail
    exact whole
  · exact ⟨eraseOut.trans eraseRound, nv.trans nvRound,
      f0.trans r0, f1.trans r1, f2.trans r2, f3.trans r3, f4.trans r4, f6.trans r6⟩
  · rw [pc, roundPC, loadPC]
    simp only [BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)

  · intro p hp
    rw [memOut]
    have dist : 288 ≤ (p - rounded.sp).toNat := by rw [roundedSP]; exact hp
    exact (storeHashWords_outside rounded p dist).trans (congrArg (fun m : Arm64.Memory => m.cells p) roundedMem)
  · intro a n read
    rw [memOut]
    exact storeHashWords_readable rounded a n (by rw [roundedMem]; exact read)
  · intro a n
    rw [memOut, storeHashWords_writable, roundedMem]

end Crypto.ARM64.Imported
