import Proofs.ARM64.ImportedBlockFetch
import Proofs.ARM64.ImportedCycleCompose
import Proofs.ARM64.ImportedHashBody

/-!
Fetched path certificates for the complete SHA-256 block phases and digest
return. The initial conditions match the existing native functional body
proof. Loop prefix invariants identify the actual intermediate states, source
permissions and PCs; no instruction is replaced by a cryptographic summary.
The complete architecture equal baseline is a separate obligation.
-/
namespace Crypto.ARM64.Imported

attribute [local irreducible] StaticPath runWords


theorem runWords_suffix_of_prefix (xs ys : List (BitVec 32)) (s mid out : Arm64.State)
    (prefixExec : runWords xs s = some mid) (wholeExec : runWords (xs ++ ys) s = some out) :
    runWords ys mid = some out := by
  obtain ⟨actualMid, actualPrefix, restExec⟩ := runWords_append_split xs ys s out wholeExec
  have same : actualMid = mid := Option.some.inj (actualPrefix.symm.trans prefixExec)
  subst actualMid
  exact restExec

set_option maxRecDepth 16384 in
theorem compression_path_permitted : PermittedWords compressionCode := by
  have initialSeq : SequentialWords initialLoadCode := sequentialWords_of_all _ (by decide +kernel)
  have feedSeq : SequentialWords feedForwardCode := sequentialWords_of_all _ (by decide +kernel)
  exact initialSeq.permitted.append ((round_cycle_permitted.repeated 64).append feedSeq.permitted)

theorem block_path_permitted : PermittedWords blockCode :=
  (word_cycle_permitted.repeated 16).append ((schedule_cycle_permitted.repeated 48).append compression_path_permitted)

set_option maxRecDepth 16384 in
theorem block_gate_path_permitted : PermittedWords blockGateCode := permittedWords_of_all _ (by decide +kernel)

set_option maxRecDepth 16384 in
theorem block_advance_path_permitted : PermittedWords blockAdvanceCode := permittedWords_of_all _ (by decide +kernel)

theorem iteration_path_permitted : PermittedWords blockIterationCode :=
  block_gate_path_permitted.append (block_path_permitted.append block_advance_path_permitted)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem block_iteration_staticPath (base : BitVec 64) (s : Arm64.State) (ready : BlockReady s)
    (hc : s.readReg64 .x3 ≠ 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outside : ∀ (i : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) (out : Arm64.State) (pc : s.pc = base + 164#64)
    (executed : runWords blockIterationCode s = some out) (running : out.status = .Running) :
    StaticPath base blockIterationCode s := by
  obtain ⟨gated, hg, postGate⟩ := exists_of_map_some _ _ _ (block_gate s hc)
  simp only [blockControlView, Prod.mk.injEq] at postGate
  obtain ⟨gs, gn, gp, g0, g1, g2, g3, g4, g5, g6⟩ := postGate
  have gf : CoreFrame s gated := ⟨controlStable_of_stable gs, gn, g0, g1, g2, g3, g4, g6⟩
  have reads (i : Fin 16) : gated.mem.canRead (gated.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [gf.mem, g2]; exact hr i
  have sep (i : Fin 16) (b : Fin 4) :
      288 ≤ (gated.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - gated.sp).toNat := by
    rw [g2, gf.sp]; exact outside i b
  obtain ⟨hashed, hh, hf, hp, _, hash, readyHash, frame, readable⟩ :=
    block_preserves_ready gated (ready.of_core gf) g5 reads sep
  have expanded := runWords_code_cast blockIterationCode (blockGateCode ++ (blockCode ++ blockAdvanceCode)) s out rfl executed
  have suffixExec := runWords_suffix_of_prefix blockGateCode (blockCode ++ blockAdvanceCode) s gated out hg expanded
  have advanceExec := runWords_suffix_of_prefix blockCode blockAdvanceCode gated hashed out hh suffixExec
  have hashedRunning := runWords_running_before blockAdvanceCode hashed out block_advance_path_permitted advanceExec running
  have gatedRunning := runWords_running_before blockCode gated hashed block_path_permitted hh hashedRunning
  have gatePath := block_gate_path base s gated pc gp hg gatedRunning
  have gatedPC : gated.pc = base + 172#64 := by rw [gp, pc, BitVec.add_assoc]; rfl
  have gatedReady := ready.of_core gf
  have blockPath := block_staticPath base gated (sourceBlock gated) gatedReady.aligned g5 reads
    gatedReady.workspaceRead gatedReady.workspaceWrite (by intro i; simp [sourceBlock, i.isLt])
    (by intro i b; have := sep i b; omega) gatedReady.constantsRead gatedReady.constantsValue
    (by intro i b; have := gatedReady.constantsOutside i b; omega)
    gatedReady.hashRead gatedReady.hashWrite hashed gatedPC hh hashedRunning
  have hashedPC : hashed.pc = base + 492#64 := by rw [hp, gatedPC, BitVec.add_assoc]; rfl
  have advancePath := block_advance_path base hashed out hashedPC advanceExec running
  exact @StaticPath.of_code_eq base s blockIterationCode (blockGateCode ++ (blockCode ++ blockAdvanceCode)) rfl
    (@StaticPath.append base blockGateCode (blockCode ++ blockAdvanceCode) s gated hg gatePath
      (@StaticPath.append base blockCode blockAdvanceCode gated hashed hh blockPath advancePath))


set_option maxRecDepth 16384 in
theorem block_skip_path_permitted : PermittedWords blockSkipCode := permittedWords_of_all _ (by decide +kernel)

theorem outer_path_permitted (n : Nat) : PermittedWords (outerLoopCode n) :=
  (iteration_path_permitted.repeated n).append block_skip_path_permitted

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem outer_loop_staticPath (base : BitVec 64) (s : Arm64.State) (ready : BlockReady s)
    (n : Nat) (bound : n < 2 ^ 64) (hc : s.readReg64 .x3 = BitVec.ofNat 64 n)
    (hr : ∀ (i : Fin n) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin n) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat) (out : Arm64.State) (pc : s.pc = base + 164#64)
    (executed : runWords (outerLoopCode n) s = some out) (running : out.status = .Running) :
    StaticPath base (outerLoopCode n) s := by
  obtain ⟨mid, he, _, nativePC, _, _, _⟩ := outer_loop_prefix s ready n bound hc hr sep n (by omega)
  have cyclesExec := (runCycles_words blockIterationCode n s).symm.trans he
  have expanded := runWords_code_cast (outerLoopCode n)
    ((List.replicate n blockIterationCode).flatten ++ blockSkipCode) s out rfl executed
  have skipExec := runWords_suffix_of_prefix (List.replicate n blockIterationCode).flatten blockSkipCode s mid out cyclesExec expanded
  have midRunning := runWords_running_before blockSkipCode mid out block_skip_path_permitted skipExec running
  have cyclePath (i : Nat) (hi : i < n) (before after : Arm64.State)
      (prefixExec : runCycles blockIterationCode i s = some before)
      (bodyExec : runWords blockIterationCode before = some after)
      (afterRunning : after.status = .Running) : StaticPath base blockIterationCode before := by
    obtain ⟨known, native, ff, knownPC, ptr, count, _, readyKnown, _, readable⟩ :=
      outer_loop_prefix s ready n bound hc hr sep i (by omega)
    have same : before = known := Option.some.inj (prefixExec.symm.trans native)
    subst before
    have positive : known.readReg64 .x3 ≠ 0#64 := by
      intro hz
      have hn := congrArg BitVec.toNat (count.symm.trans hz)
      have subBound : n - i < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt subBound] at hn
      omega
    let t : Fin n := ⟨i, hi⟩
    have reads (j : Fin 16) : known.mem.canRead
        (known.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val)) 4 = true := by
      rw [ptr]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using readable _ _ (hr t j)
    have outside (j : Fin 16) (b : Fin 4) :
        288 ≤ (known.readReg64 .x2 + BitVec.ofNat 64 (4 * j.val) + BitVec.ofNat 64 b.val - known.sp).toNat := by
      rw [ptr, ff.sp]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using sep t j b
    exact block_iteration_staticPath base known readyKnown positive reads outside after
      (knownPC.trans pc) bodyExec afterRunning
  have repeatedPath := cycles_path_of_prefixes base blockIterationCode s mid n iteration_path_permitted
    cyclePath he midRunning
  have skipPath := block_skip_path base mid out (nativePC.trans pc) skipExec running
  exact @StaticPath.of_code_eq base s (outerLoopCode n) ((List.replicate n blockIterationCode).flatten ++ blockSkipCode) rfl
    (@StaticPath.append base (List.replicate n blockIterationCode).flatten blockSkipCode s mid
      cyclesExec repeatedPath skipPath)


set_option maxRecDepth 16384 in
theorem padding_phase_path_permitted : PermittedWords paddingPhaseCode := permittedWords_of_all _ (by decide +kernel)
set_option maxRecDepth 16384 in
theorem digest_gate_path_permitted : PermittedWords digestGateCode := permittedWords_of_all _ (by decide +kernel)
set_option maxRecDepth 16384 in
theorem exit_path_permitted : PermittedWords exitCode := permittedWords_of_all _ (by decide +kernel)

theorem phases_path_permitted (full padding : Nat) : PermittedWords (hashPhasesCode full padding) :=
  (outer_path_permitted full).append
    (padding_phase_path_permitted.append ((outer_path_permitted padding).append digest_gate_path_permitted))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem hash_phases_staticPath (base : BitVec 64) (s : Arm64.State) (ready : BlockReady s)
    (full padding : Nat) (fullBound : full < 2 ^ 64) (paddingBound : padding ≤ 2)
    (count : s.readReg64 .x3 = BitVec.ofNat 64 full)
    (phase : s.readReg64 .x4 = 0#64) (padCount : s.readReg64 .x6 = BitVec.ofNat 64 padding)
    (hr : ∀ (i : Fin full) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin full) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (padRead : ∀ i : Fin 32, s.mem.canRead ((s.sp + 288#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true) (out : Arm64.State) (pc : s.pc = base + 164#64)
    (executed : runWords (hashPhasesCode full padding) s = some out) (running : out.status = .Running) :
    StaticPath base (hashPhasesCode full padding) s := by
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

  have expanded := runWords_code_cast (hashPhasesCode full padding)
    (outerLoopCode full ++ (paddingPhaseCode ++ (outerLoopCode padding ++ digestGateCode))) s out rfl executed
  have fullSuffix := runWords_suffix_of_prefix (outerLoopCode full)
    (paddingPhaseCode ++ (outerLoopCode padding ++ digestGateCode)) s complete out hc expanded
  have switchedSuffix := runWords_suffix_of_prefix paddingPhaseCode
    (outerLoopCode padding ++ digestGateCode) complete switched out hs fullSuffix
  have gateExec := runWords_suffix_of_prefix (outerLoopCode padding) digestGateCode switched padded out hp switchedSuffix
  have paddedRunning := runWords_running_before digestGateCode padded out digest_gate_path_permitted gateExec running
  have switchedRunning := runWords_running_before (outerLoopCode padding) switched padded
    (outer_path_permitted padding) hp paddedRunning
  have completeRunning := runWords_running_before paddingPhaseCode complete switched
    padding_phase_path_permitted hs switchedRunning
  have completePath := outer_loop_staticPath base s ready full fullBound count hr sep
    complete pc hc completeRunning
  have completePC : complete.pc = base + 504#64 := by rw [cp, pc, BitVec.add_assoc]; rfl
  have switchPath := padding_phase_path base complete switched completePC spc hs switchedRunning
  have switchedPC : switched.pc = base + 164#64 := by
    rw [spc, completePC]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have paddingPath := outer_loop_staticPath base switched (readyComplete.of_stable sst s0)
    padding (by omega) countSwitch reads padSep padded switchedPC hp paddedRunning
  have paddedPC : padded.pc = base + 504#64 := by rw [pp, switchedPC, BitVec.add_assoc]; rfl
  have gatePath := digest_gate_path base padded out paddedPC gateExec running
  exact @StaticPath.of_code_eq base s (hashPhasesCode full padding) (outerLoopCode full ++
    (paddingPhaseCode ++ (outerLoopCode padding ++ digestGateCode))) rfl
    (@StaticPath.append base (outerLoopCode full) (paddingPhaseCode ++ (outerLoopCode padding ++ digestGateCode)) s complete
      hc completePath (@StaticPath.append base paddingPhaseCode (outerLoopCode padding ++ digestGateCode) complete switched
        hs switchPath (@StaticPath.append base (outerLoopCode padding) digestGateCode switched padded hp paddingPath gatePath)))


set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem hash_body_staticPath (base : BitVec 64) (s : Arm64.State) (ready : BlockReady s)
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
      288 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) (out : Arm64.State) (pc : s.pc = base + 164#64)
    (executed : runWords (hashBodyCode full padding) s = some out) (running : out.status = .Running) :
    StaticPath base (hashBodyCode full padding) s := by
  obtain ⟨hashed, he, _, _, nativePC, _⟩ :=
    hash_phases s ready full padding fullBound paddingBound count phase padCount hr sep padRead
  have expanded := runWords_code_cast (hashBodyCode full padding) (hashPhasesCode full padding ++ exitCode) s out rfl executed
  have exitExec := runWords_suffix_of_prefix (hashPhasesCode full padding) exitCode s hashed out he expanded
  have hashedRunning := runWords_running_before exitCode hashed out exit_path_permitted exitExec running
  have phasesPath := hash_phases_staticPath base s ready full padding fullBound paddingBound count phase padCount
    hr sep padRead hashed pc he hashedRunning
  have hashedPC : hashed.pc = base + 524#64 := by rw [nativePC, pc, BitVec.add_assoc]; rfl
  have exitPath := exit_path base hashed out hashedPC exitExec running
  exact @StaticPath.of_code_eq base s (hashBodyCode full padding) (hashPhasesCode full padding ++ exitCode) rfl
    (@StaticPath.append base (hashPhasesCode full padding) exitCode s hashed he phasesPath exitPath)

end Crypto.ARM64.Imported
