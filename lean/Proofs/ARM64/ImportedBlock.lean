import Proofs.ARM64.ImportedWordLoops
import Proofs.ARM64.ImportedCellFrame

/-!
Compose the recorded message-word loop, schedule loop, hash loading, round
loop and feed-forward. The final stack hash is exactly the imported FIPS
compression of the block decoded directly from the 64 source bytes.
The postcondition preserves cells outside the 288-byte schedule/hash area,
existing read permissions and the workspace/hash write permissions needed by
subsequent blocks. The closed length theorem counts the 3,095 recorded words in this path.
These are word-list execution proofs: whole-function padding/outer loops,
ByteList decoding, fetch binding, final output and the full baseline remain
separate obligations.
-/
namespace Crypto.ARM64.Imported

theorem DataFrame.x0 {a b : Arm64.State} (h : DataFrame a b) :
    b.readReg64 .x0 = a.readReg64 .x0 := h.2.2.1

def blockCode : List (BitVec 32) :=
  (List.replicate 16 wordCycleCode).flatten ++
    ((List.replicate 48 scheduleCycleCode).flatten ++ compressionCode)

theorem block_compression (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hww : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hM : ∀ i : Fin 16, reverseWord (s.mem.read32 (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!)
    (hOutside : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hKOutside : ∀ (i : Fin 64) (b : Fin 4),
      256 ≤ (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (hhr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hhw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ out, runWords blockCode s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 320#64 ∧ out.readReg64 .x5 = 64#64 ∧
      wordVector 8 out.mem (out.sp + 256#64) =
        SHS.SHA256.compress (wordVector 8 s.mem (s.sp + 256#64)) M ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 8, out.mem.canWrite ((out.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) := by
  obtain ⟨copied, hCopy, fw, pcCopy, countCopy, initialized,
    _sourceReads, writable, _sourceValues, outsideCopy, readableCopy⟩ :=
      word_loop s M hsp hc hr hww hM hOutside
  have workspaceRead (i : Fin 64) :
      copied.mem.canRead (copied.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fw.sp]
    exact readableCopy _ _ (hwr i)
  obtain ⟨scheduled, hSchedule, fs, pcSchedule, _countSchedule, scheduleWords,
    scheduleReads, scheduleWrites, outsideSchedule, readableSchedule⟩ :=
      schedule_loop_matches_spec copied M countCopy workspaceRead writable initialized
  have fws := fw.trans fs
  have outside (p : BitVec 64) (hp : 256 ≤ (p - s.sp).toNat) :
      scheduled.mem.cells p = s.mem.cells p := by
    have dist : 256 ≤ (p - copied.sp).toNat := by rw [fw.sp]; exact hp
    exact (outsideSchedule p dist).trans (outsideCopy p hp)
  have kr (i : Fin 64) : scheduled.mem.canRead
      (scheduled.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fws.x0]
    exact readableSchedule _ _ (readableCopy _ _ (hkr i))
  have kv (i : Fin 64) : scheduled.mem.read32
      (scheduled.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]! := by
    rw [fws.x0]
    have preserved := read32_of_cells (m := scheduled.mem) (before := s.mem)
      (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val))
      (fun b => outside _ (hKOutside i b))
    exact preserved.trans (hkv i)
  have hashRead (i : Fin 8) : scheduled.mem.canRead
      ((scheduled.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fws.sp]
    exact readableSchedule _ _ (readableCopy _ _ (hhr i))
  have hashWrite (i : Fin 8) : scheduled.mem.canWrite
      ((scheduled.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fws.sp]
    have preserved := canWrite32_of_cells (m := scheduled.mem) (before := s.mem)
      ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val))
      (fun b => outside _ (hash_byte_outside s.sp i b))
    exact preserved.trans (hhw i)
  have hashBefore : wordVector 8 scheduled.mem (scheduled.sp + 256#64) =
      wordVector 8 s.mem (s.sp + 256#64) := by
    rw [fws.sp]
    exact hash_snapshot_of_frame scheduled.mem s.mem s.sp outside
  obtain ⟨out, hCompression, fc, pcCompression, countCompression, hashCompression, outsideCompression, readableCompression, writableCompression⟩ :=
    compression scheduled M (by rw [fws.aligned]; exact hsp)
      kr scheduleReads kv scheduleWords hashRead hashWrite
  have copyWords := (runCycles_words wordCycleCode 16 s).symm.trans hCopy
  have schedulePath := (runCycles_words scheduleCycleCode 48 copied).symm.trans hSchedule
  have tail := runWords_append_success schedulePath hCompression
  have whole := runWords_append_success copyWords tail
  refine ⟨out, whole, fws.trans fc, ?_, countCompression, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pcCompression, pcSchedule, pcCopy]
    simp only [BitVec.add_assoc]
    exact congrArg (s.pc + ·) (by decide +kernel)
  · exact hashCompression.trans
      (congrArg (fun H : Vector (BitVec 32) 8 => SHS.SHA256.compress H M) hashBefore)

  · intro p hp
    have dist : 288 ≤ (p - scheduled.sp).toNat := by rw [fws.sp]; exact hp
    exact (outsideCompression p dist).trans (outside p (by omega))
  · intro a n read
    exact readableCompression a n (readableSchedule a n (readableCopy a n read))
  · intro i
    rw [fc.sp, writableCompression]
    exact scheduleWrites i
  · intro i
    rw [fc.sp, writableCompression]
    exact hashWrite i

def sourceBlock (s : Arm64.State) : Vector (BitVec 32) 16 :=
  Vector.ofFn (fun i => reverseWord (s.mem.read32 (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))))

theorem sourceBlock_bytes (s : Arm64.State) (i : Fin 16) :
    (sourceBlock s)[i.val]! =
      let base := s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)
      s.mem.read8 base ++ s.mem.read8 (base + 1#64) ++
        s.mem.read8 (base + 2#64) ++ s.mem.read8 (base + 3#64) := by
  rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ i.isLt]
  simp only [sourceBlock, Vector.getElem_ofFn, Arm64.Memory.read32,
    reverseWord_bytes, BitVec.add_zero]

theorem block_compression_source (s : Arm64.State)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hww : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hOutside : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hKOutside : ∀ (i : Fin 64) (b : Fin 4),
      256 ≤ (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (hhr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hhw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ out, runWords blockCode s = some out ∧ DataFrame s out ∧
      out.pc = s.pc + 320#64 ∧ out.readReg64 .x5 = 64#64 ∧
      wordVector 8 out.mem (out.sp + 256#64) =
        SHS.SHA256.compress (wordVector 8 s.mem (s.sp + 256#64)) (sourceBlock s) ∧
      (∀ p, 288 ≤ (p - s.sp).toNat → out.mem.cells p = s.mem.cells p) ∧
      (∀ a n, s.mem.canRead a n = true → out.mem.canRead a n = true) ∧
      (∀ i : Fin 64, out.mem.canWrite (out.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) ∧
      (∀ i : Fin 8, out.mem.canWrite ((out.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) := by
  apply block_compression s (sourceBlock s) hsp hc hr hwr hww
    _ hOutside hkr hkv hKOutside hhr hhw
  intro i
  simp [sourceBlock, i.isLt]

set_option maxRecDepth 16384 in
theorem block_code_length : blockCode.length = 3095 := by decide +kernel

end Crypto.ARM64.Imported
