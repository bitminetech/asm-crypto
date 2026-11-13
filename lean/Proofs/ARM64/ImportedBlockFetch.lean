import Proofs.ARM64.ImportedCycleFetch

/-!
Fetched control-flow certificates for the recorded SHA-256 compression path.
Each span uses the imported instruction model and its exact image offset;
loop PCs come from the existing instruction-execution invariants. Code-list
casts remain explicit to avoid reducing an entire concrete trace during type
checking. These certificates support whole-call path composition.
-/
namespace Crypto.ARM64.Imported

attribute [local irreducible] StaticPath runWords

theorem StaticPath.of_code_eq {base : BitVec 64} {s : Arm64.State} {left right : List (BitVec 32)}
    (codeEq : left = right) (path : StaticPath base right s) : StaticPath base left s := by
  subst right
  exact path


theorem runWords_code_cast (left right : List (BitVec 32)) (s out : Arm64.State)
    (codeEq : left = right) (executed : runWords left s = some out) : runWords right s = some out := by
  cases codeEq
  exact executed

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem compression_staticPath (base : BitVec 64) (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hW : wordVector 64 s.mem s.sp = SHS.SHA256.schedule M)
    (hhr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hhw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) (out : Arm64.State)
    (pc : s.pc = base + 268#64) (executed : runWords compressionCode s = some out)
    (running : out.status = .Running) : StaticPath base compressionCode s := by
  obtain ⟨loaded, hl, postLoad⟩ := exists_of_map_some _ _ _ (initial_load s hhr)
  simp only [Prod.mk.injEq] at postLoad
  obtain ⟨_loadWork, loadStable, loadPC, loadNV, l0, l1, l2, l3, l4, l5, l6⟩ := postLoad
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

  have expanded := runWords_code_cast compressionCode
    (initialLoadCode ++ ((List.replicate 64 roundCycleCode).flatten ++ feedForwardCode)) s out rfl executed
  obtain ⟨actualLoaded, actualLoad, restExec⟩ := runWords_append_split initialLoadCode
    ((List.replicate 64 roundCycleCode).flatten ++ feedForwardCode) s out expanded
  have sameLoad : actualLoaded = loaded := Option.some.inj (actualLoad.symm.trans hl)
  subst actualLoaded
  obtain ⟨rounded, roundsExec, feedExec⟩ := runWords_append_split
    (List.replicate 64 roundCycleCode).flatten feedForwardCode loaded out restExec
  have feedSequential : SequentialWords feedForwardCode := sequentialWords_of_all _ (by decide +kernel)
  have roundedRunning := runWords_running_before feedForwardCode rounded out feedSequential.permitted feedExec running
  have loadedRunning := runWords_running_before (List.replicate 64 roundCycleCode).flatten loaded rounded
    (round_cycle_permitted.repeated 64) roundsExec roundedRunning
  have roundCycles := (runCycles_words roundCycleCode 64 loaded).trans roundsExec
  obtain ⟨known, native, _, nativePC, _⟩ := round_loop_prefix loaded (SHS.SHA256.schedule M)
    (by rw [fl.aligned]; exact hsp) l5 kr wr kv wv 64 (by decide)
  have equal := Option.some.inj (roundCycles.symm.trans native)
  have roundedPC : rounded.pc = loaded.pc + 132#64 := by
    rw [equal, nativePC]
    rfl
  have loadedPC : loaded.pc = base + 292#64 := by
    rw [loadPC, pc, BitVec.add_assoc]
    rfl
  have initialSequential : SequentialWords initialLoadCode := sequentialWords_of_all _ (by decide +kernel)
  have initialImageExec : runWords (imageSlice 67 6) s = some loaded :=
    runWords_code_cast initialLoadCode (imageSlice 67 6) s loaded rfl hl
  have initialPath : StaticPath base initialLoadCode s := @StaticPath.of_code_eq base s initialLoadCode (imageSlice 67 6) rfl
    (sequential_slice_path base 67 6 s loaded (by decide) initialSequential pc initialImageExec loadedRunning).1
  have roundPath := round_loop_staticPath base loaded (SHS.SHA256.schedule M)
    (by rw [fl.aligned]; exact hsp) l5 kr wr kv wv rounded loadedPC roundCycles roundedRunning
  have feedPC : rounded.pc = base + 424#64 := by
    rw [roundedPC, loadedPC, BitVec.add_assoc]
    rfl
  have feedImageExec : runWords (imageSlice 106 17) rounded = some out :=
    runWords_code_cast feedForwardCode (imageSlice 106 17) rounded out rfl feedExec
  have feedPath : StaticPath base feedForwardCode rounded := @StaticPath.of_code_eq base rounded feedForwardCode (imageSlice 106 17) rfl
    (sequential_slice_path base 106 17 rounded out (by decide) feedSequential feedPC feedImageExec running).1
  have suffix := @StaticPath.append base (List.replicate 64 roundCycleCode).flatten
    feedForwardCode loaded rounded roundsExec roundPath feedPath
  have answer : StaticPath base compressionCode s := @StaticPath.of_code_eq base s compressionCode (initialLoadCode ++
    ((List.replicate 64 roundCycleCode).flatten ++ feedForwardCode)) rfl
    (@StaticPath.append base initialLoadCode
      ((List.replicate 64 roundCycleCode).flatten ++ feedForwardCode) s loaded hl initialPath suffix)
  exact answer



set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem block_staticPath (base : BitVec 64) (s : Arm64.State) (M : Vector (BitVec 32) 16)
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
    (hhw : ∀ i : Fin 8, s.mem.canWrite ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) (out : Arm64.State)
    (pc : s.pc = base + 172#64) (executed : runWords blockCode s = some out)
    (running : out.status = .Running) : StaticPath base blockCode s := by
  obtain ⟨copied, hCopy, fw, pcCopy, countCopy, initialized,
    _sourceReads, writable, _sourceValues, outsideCopy, readableCopy⟩ :=
      word_loop s M hsp hc hr hww hM hOutside
  have workspaceRead (i : Fin 64) :
      copied.mem.canRead (copied.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [fw.sp]
    exact readableCopy _ _ (hwr i)
  obtain ⟨scheduled, hSchedule, fs, pcSchedule, countSchedule, scheduleWords,
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

  have copyWords := (runCycles_words wordCycleCode 16 s).symm.trans hCopy
  have scheduleWordsExec := (runCycles_words scheduleCycleCode 48 copied).symm.trans hSchedule
  have expanded := runWords_code_cast blockCode ((List.replicate 16 wordCycleCode).flatten ++
    ((List.replicate 48 scheduleCycleCode).flatten ++ compressionCode)) s out rfl executed
  obtain ⟨actualCopied, actualCopy, restExec⟩ := runWords_append_split
    (List.replicate 16 wordCycleCode).flatten
    ((List.replicate 48 scheduleCycleCode).flatten ++ compressionCode) s out expanded
  have sameCopy : actualCopied = copied := Option.some.inj (actualCopy.symm.trans copyWords)
  subst actualCopied
  obtain ⟨actualScheduled, actualSchedule, compressExec⟩ := runWords_append_split
    (List.replicate 48 scheduleCycleCode).flatten compressionCode copied out restExec
  have sameSchedule : actualScheduled = scheduled := Option.some.inj (actualSchedule.symm.trans scheduleWordsExec)
  subst actualScheduled
  have initialSequential : SequentialWords initialLoadCode := sequentialWords_of_all _ (by decide +kernel)
  have feedSequential : SequentialWords feedForwardCode := sequentialWords_of_all _ (by decide +kernel)
  have compressionPermitted : PermittedWords compressionCode :=
    initialSequential.permitted.append ((round_cycle_permitted.repeated 64).append feedSequential.permitted)
  have scheduledRunning := runWords_running_before compressionCode scheduled out compressionPermitted compressExec running
  have copiedRunning := runWords_running_before _ copied scheduled (schedule_cycle_permitted.repeated 48)
    scheduleWordsExec scheduledRunning
  have copiedPC : copied.pc = base + 196#64 := by
    rw [pcCopy, pc, BitVec.add_assoc]; rfl
  have scheduledPC : scheduled.pc = base + 268#64 := by
    rw [pcSchedule, copiedPC, BitVec.add_assoc]; rfl
  have copyPath := word_loop_staticPath base s M hsp hc hr hww hM hOutside copied pc hCopy copiedRunning
  have schedulePath := schedule_loop_staticPath base copied M countCopy workspaceRead writable
    scheduled copiedPC hSchedule scheduledRunning
  have compressPath := compression_staticPath base scheduled M (by rw [fws.aligned]; exact hsp)
    kr scheduleReads kv scheduleWords hashRead hashWrite out scheduledPC compressExec running
  exact @StaticPath.of_code_eq base s blockCode ((List.replicate 16 wordCycleCode).flatten ++
    ((List.replicate 48 scheduleCycleCode).flatten ++ compressionCode)) rfl
    (@StaticPath.append base (List.replicate 16 wordCycleCode).flatten
      ((List.replicate 48 scheduleCycleCode).flatten ++ compressionCode) s copied copyWords copyPath
      (@StaticPath.append base (List.replicate 48 scheduleCycleCode).flatten compressionCode copied scheduled
        scheduleWordsExec schedulePath compressPath))


end Crypto.ARM64.Imported
