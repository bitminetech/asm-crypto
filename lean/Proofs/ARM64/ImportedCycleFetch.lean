import Proofs.ARM64.ImportedMiddleFetch

/-!
Recorded SHA-256 cycle/control path certificates and the complete message-load,
schedule and round loop paths. The certificates use native execution PC
invariants and checked image/decoder facts.
-/
namespace Crypto.ARM64.Imported

theorem permittedWords_of_all (words : List (BitVec 32))
    (all : (words.all fun word => ((Arm64.decode word).map permittedInstruction).getD false) = true) :
    PermittedWords words := by
  intro word member instruction decoded
  have good := List.all_eq_true.mp all word member
  simpa only [decoded, Option.map_some, Option.getD_some] using good

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem word_cycle_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 172#64) (executed : runWords wordCycleCode s = some out)
    (running : out.status = .Running) : StaticPath base wordCycleCode s := by
  have shape : wordCycleCode = imageChunk 43 5 := by decide +kernel
  have sequential : SequentialWords (imageSlice 43 5) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 43 5 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem schedule_cycle_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 196#64) (executed : runWords scheduleCycleCode s = some out)
    (running : out.status = .Running) : StaticPath base scheduleCycleCode s := by
  have shape : scheduleCycleCode = imageChunk 49 17 := by decide +kernel
  have sequential : SequentialWords (imageSlice 49 17) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 49 17 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem round_cycle_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 292#64) (executed : runWords roundCycleCode s = some out)
    (running : out.status = .Running) : StaticPath base roundCycleCode s := by
  have shape : roundCycleCode = imageChunk 73 32 := by decide +kernel
  have sequential : SequentialWords (imageSlice 73 32) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 73 32 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_advance_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 492#64) (executed : runWords blockAdvanceCode s = some out)
    (running : out.status = .Running) : StaticPath base blockAdvanceCode s := by
  have shape : blockAdvanceCode = imageChunk 123 2 := by decide +kernel
  have sequential : SequentialWords (imageSlice 123 2) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 123 2 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem tail_copy_end_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 68#64) (executed : runWords tailCopyEndCode s = some out)
    (running : out.status = .Running) : StaticPath base tailCopyEndCode s := by
  have shape : tailCopyEndCode = imageChunk 17 1 := by decide +kernel
  have sequential : SequentialWords (imageSlice 17 1) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 17 1 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem digest_gate_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 504#64) (executed : runWords digestGateCode s = some out)
    (running : out.status = .Running) : StaticPath base digestGateCode s := by
  have shape : digestGateCode = imageChunk 126 0 := by decide +kernel
  have sequential : SequentialWords (imageSlice 126 0) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 126 0 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_skip_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 164#64) (executed : runWords blockSkipCode s = some out)
    (running : out.status = .Running) : StaticPath base blockSkipCode s := by
  have shape : blockSkipCode = imageChunk 41 0 := by decide +kernel
  have sequential : SequentialWords (imageSlice 41 0) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 41 0 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem exit_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 524#64) (executed : runWords exitCode s = some out)
    (running : out.status = .Running) : StaticPath base exitCode s := by
  have shape : exitCode = imageChunk 131 19 := by decide +kernel
  have sequential : SequentialWords (imageSlice 131 19) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 131 19 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem padding_count_small_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 100#64) (executed : runWords (paddingCountCode true) s = some out)
    (running : out.status = .Running) : StaticPath base (paddingCountCode true) s := by
  have shape : (paddingCountCode true) = imageChunk 25 2 := by decide +kernel
  have sequential : SequentialWords (imageSlice 25 2) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact image_chunk_path base 25 2 s out (by decide) sequential pc executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem block_gate_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 164#64) (endPC : out.pc = s.pc + 8#64)
    (executed : runWords blockGateCode s = some out) (running : out.status = .Running) :
    StaticPath base blockGateCode s := by
  have shape : blockGateCode = middleChunk 41 0 1 := by decide +kernel
  have beforeSequential : SequentialWords (imageSlice 41 0) := sequentialWords_of_all _ (by decide +kernel)
  have afterSequential : SequentialWords (imageSlice 42 1) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact middle_linear_path base 41 0 1 s out (by decide) beforeSequential afterSequential pc endPC executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem padding_count_large_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 100#64) (endPC : out.pc = s.pc + 16#64)
    (executed : runWords (paddingCountCode false) s = some out) (running : out.status = .Running) :
    StaticPath base (paddingCountCode false) s := by
  have shape : (paddingCountCode false) = middleChunk 25 2 1 := by decide +kernel
  have beforeSequential : SequentialWords (imageSlice 25 2) := sequentialWords_of_all _ (by decide +kernel)
  have afterSequential : SequentialWords (imageSlice 28 1) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  exact middle_linear_path base 25 2 1 s out (by decide) beforeSequential afterSequential pc endPC executed running

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem tail_copy_cycle_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 68#64) (endPC : out.pc = s.pc)
    (executed : runWords tailCopyCycleCode s = some out) (running : out.status = .Running) :
    StaticPath base tailCopyCycleCode s := by
  have shape : tailCopyCycleCode = middleTrailingB 17 1 3 := by decide +kernel
  have beforeSequential : SequentialWords (imageSlice 17 1) := sequentialWords_of_all _ (by decide +kernel)
  have afterSequential : SequentialWords (imageSlice 19 3) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  apply middle_trailing_b_path base 17 1 3 18446744073709551596#64 s out (by decide)
    beforeSequential afterSequential (by decide +kernel) pc ?_ executed running
  · change out.pc = (s.pc + 20#64) + 18446744073709551596#64
    simpa only [BitVec.add_assoc, show 20#64 + 0xffffffffffffffec#64 = 0#64 by decide +kernel, BitVec.add_zero] using endPC

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem padding_phase_path (base : BitVec 64) (s out : Arm64.State)
    (pc : s.pc = base + 504#64) (endPC : out.pc = s.pc - 340#64)
    (executed : runWords paddingPhaseCode s = some out) (running : out.status = .Running) :
    StaticPath base paddingPhaseCode s := by
  have shape : paddingPhaseCode = middleTrailingB 126 0 3 := by decide +kernel
  have beforeSequential : SequentialWords (imageSlice 126 0) := sequentialWords_of_all _ (by decide +kernel)
  have afterSequential : SequentialWords (imageSlice 127 3) := sequentialWords_of_all _ (by decide +kernel)
  rw [shape] at executed ⊢
  apply middle_trailing_b_path base 126 0 3 18446744073709551260#64 s out (by decide)
    beforeSequential afterSequential (by decide +kernel) pc ?_ executed running
  · change out.pc = (s.pc + 16#64) + 18446744073709551260#64
    rw [BitVec.add_assoc, show 16#64 + 0xfffffffffffffe9c#64 = -340#64 by decide +kernel]
    simpa only [BitVec.sub_eq_add_neg] using endPC

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem word_cycle_permitted : PermittedWords wordCycleCode := permittedWords_of_all _ (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem schedule_cycle_permitted : PermittedWords scheduleCycleCode := permittedWords_of_all _ (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem round_cycle_permitted : PermittedWords roundCycleCode := permittedWords_of_all _ (by decide +kernel)

theorem word_loop_staticPath (base : BitVec 64) (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hr : ∀ i : Fin 16, s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hM : ∀ i : Fin 16, reverseWord (s.mem.read32 (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val))) = M[i.val]!)
    (hOutside : ∀ (i : Fin 16) (b : Fin 4),
      256 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (out : Arm64.State) (pc : s.pc = base + 172#64)
    (executed : runCycles wordCycleCode 16 s = some out) (running : out.status = .Running) :
    StaticPath base (List.replicate 16 wordCycleCode).flatten s := by
  apply cycles_staticPath base wordCycleCode s.pc s out 16 word_cycle_permitted ?_ ?_ executed running
  · intro before after beforePC bodyExec bodyRunning
    exact word_cycle_path base before after (beforePC.trans pc) bodyExec bodyRunning
  · intro i hi mid prefixExec
    obtain ⟨known, native, _, knownPC, _⟩ := word_loop_prefix s M hsp hc hr hw hM hOutside i (by omega)
    have equal := Option.some.inj (prefixExec.symm.trans native)
    have cond : i < 16 := by omega
    rw [equal, knownPC, if_pos cond]

theorem schedule_loop_staticPath (base : BitVec 64) (s : Arm64.State) (M : Vector (BitVec 32) 16)
    (hc : s.readReg64 .x5 = 16#64)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (out : Arm64.State) (pc : s.pc = base + 196#64)
    (executed : runCycles scheduleCycleCode 48 s = some out) (running : out.status = .Running) :
    StaticPath base (List.replicate 48 scheduleCycleCode).flatten s := by
  apply cycles_staticPath base scheduleCycleCode s.pc s out 48 schedule_cycle_permitted ?_ ?_ executed running
  · intro before after beforePC bodyExec bodyRunning
    exact schedule_cycle_path base before after (beforePC.trans pc) bodyExec bodyRunning
  · intro i hi mid prefixExec
    obtain ⟨known, native, _, knownPC, _⟩ := schedule_loop_prefix s M hc hr hw i (by omega)
    have equal := Option.some.inj (prefixExec.symm.trans native)
    have cond : 16 + i < 64 := by omega
    rw [equal, knownPC, if_pos cond]

theorem round_loop_staticPath (base : BitVec 64) (s : Arm64.State) (W : Vector (BitVec 32) 64)
    (hsp : s.spAligned = true) (hc : s.readReg64 .x5 = 0#64)
    (hkr : ∀ i : Fin 64, s.mem.canRead (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hwr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hkv : ∀ i : Fin 64, s.mem.read32 (s.readReg64 .x0 + BitVec.ofNat 64 (4 * i.val)) = SHS.SHA256.K[i.val]!)
    (hwv : ∀ i : Fin 64, s.mem.read32 (s.sp + BitVec.ofNat 64 (4 * i.val)) = W[i.val]!)
    (out : Arm64.State) (pc : s.pc = base + 292#64)
    (executed : runCycles roundCycleCode 64 s = some out) (running : out.status = .Running) :
    StaticPath base (List.replicate 64 roundCycleCode).flatten s := by
  apply cycles_staticPath base roundCycleCode s.pc s out 64 round_cycle_permitted ?_ ?_ executed running
  · intro before after beforePC bodyExec bodyRunning
    exact round_cycle_path base before after (beforePC.trans pc) bodyExec bodyRunning
  · intro i hi mid prefixExec
    obtain ⟨known, native, _, knownPC, _⟩ := round_loop_prefix s W hsp hc hkr hwr hkv hwv i (by omega)
    have equal := Option.some.inj (prefixExec.symm.trans native)
    have cond : i < 64 := by omega
    rw [equal, knownPC, if_pos cond]

end Crypto.ARM64.Imported
