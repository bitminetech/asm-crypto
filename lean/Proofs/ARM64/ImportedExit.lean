import Proofs.ARM64.ImportedWordLoad

/-!
The final 20 recorded words load the saved hash, serialize all 32 digest bytes
in big-endian order, return status zero, restore SP by 416 bytes and return
through the original X30. The theorem records the exact output stores and the
modeled nonvolatile/state frame under the actual read/write guards.
-/
namespace Crypto.ARM64.Imported

theorem bv_sub_add_left {n : Nat} (base y : BitVec n) :
    base - (base + y) = 0#n - y := by
  have result := bv_add_sub_add_left base 0#n y
  simpa only [BitVec.add_zero] using result

def exitCode : List (BitVec 32) := (imageWords.toList.drop 131).take 20
private theorem exit_decoded : exitCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x16 .sp 256#12 false,
  .ldp .W32 false .x7 .x8 (.Offset .x16 0#64),
  .ldp .W32 false .x9 .x10 (.Offset .x16 8#64),
  .ldp .W32 false .x11 .x12 (.Offset .x16 16#64),
  .ldp .W32 false .x13 .x14 (.Offset .x16 24#64),
  .dataProc1 .W32 .REV .x7 .x7,
  .dataProc1 .W32 .REV .x8 .x8,
  .dataProc1 .W32 .REV .x9 .x9,
  .dataProc1 .W32 .REV .x10 .x10,
  .dataProc1 .W32 .REV .x11 .x11,
  .dataProc1 .W32 .REV .x12 .x12,
  .dataProc1 .W32 .REV .x13 .x13,
  .dataProc1 .W32 .REV .x14 .x14,
  .stp .W32 .x7 .x8 (.Offset .x1 0#64),
  .stp .W32 .x9 .x10 (.Offset .x1 8#64),
  .stp .W32 .x11 .x12 (.Offset .x1 16#64),
  .stp .W32 .x13 .x14 (.Offset .x1 24#64),
  .moveWide .W64 .MOVZ .x0 0#16 0,
  .addSubImm .W64 .ADD .sp .sp 416#12 false,
  .ret .x30] := by decide +kernel

def returnStable (s : Arm64.State) : Arm64.State := { nonMemory s with sp := 0 }
@[simp] theorem retStable_advance (s : Arm64.State) : returnStable s.advancePC = returnStable s := by cases s; rfl
@[simp] theorem retStable_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) : returnStable (s.writeReg64 (.gpr i) v) = returnStable s := by cases s; rfl
@[simp] theorem retStable_sp (s : Arm64.State) (v : BitVec 64) : returnStable (s.writeReg64 .sp v) = returnStable s := by cases s; rfl
@[simp] theorem retStable_mem (s : Arm64.State) (m : Arm64.Memory) : returnStable (s.setMem m) = returnStable s := by cases s; rfl
@[simp] theorem retStable_pc (s : Arm64.State) (v : BitVec 64) : returnStable (s.setPC v) = returnStable s := by cases s; rfl
@[simp] theorem mem_set_pc (s : Arm64.State) (v : BitVec 64) : (s.setPC v).mem = s.mem := by cases s; rfl
@[simp] theorem sp_set_pc (s : Arm64.State) (v : BitVec 64) : (s.setPC v).sp = s.sp := by cases s; rfl
@[simp] theorem mem_write_sp (s : Arm64.State) (v : BitVec 64) : (s.writeReg64 .sp v).mem = s.mem := by cases s; rfl
@[simp] theorem sp_write_sp (s : Arm64.State) (v : BitVec 64) : (s.writeReg64 .sp v).sp = v := by cases s; rfl
@[simp] theorem reg_write_sp (s : Arm64.State) (v : BitVec 64) (i : BitVec 5) : (s.writeReg64 .sp v).readReg64 (.gpr i) = s.readReg64 (.gpr i) := by cases s; rfl
@[simp] theorem nv_write_sp (s : Arm64.State) (v : BitVec 64) : nonvolatile (s.writeReg64 .sp v) = nonvolatile s := by funext i; exact reg_write_sp s v _

def digestWords (s : Arm64.State) : Vector (BitVec 32) 8 :=
  (wordVector 8 s.mem (s.sp + 256#64)).map reverseWord

theorem digestWords_eight (s : Arm64.State) :
    digestWords s = #v[reverseWord (s.mem.read32 (s.sp + 256#64)), reverseWord (s.mem.read32 (s.sp + 260#64)), reverseWord (s.mem.read32 (s.sp + 264#64)), reverseWord (s.mem.read32 (s.sp + 268#64)), reverseWord (s.mem.read32 (s.sp + 272#64)), reverseWord (s.mem.read32 (s.sp + 276#64)), reverseWord (s.mem.read32 (s.sp + 280#64)), reverseWord (s.mem.read32 (s.sp + 284#64))] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [digestWords, wordVector, BitVec.add_assoc]
  all_goals rfl

def storeDigestWords (s : Arm64.State) : Arm64.Memory :=
  (List.range 8).foldl (fun m i =>
    m.write32 (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i)) (digestWords s)[i]!) s.mem

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem exit_stores (s : Arm64.State)
    (hr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    (runWords exitCode s).map (fun out =>
      (wordVector 8 out.mem (out.readReg64 .x1), out.mem, returnStable out,
        out.sp, out.pc, nonvolatile out, out.readReg64 .x0, out.readReg64 .x1)) =
      some (digestWords s, storeDigestWords s, returnStable s,
        s.sp + 416#64, s.readReg64 .x30, nonvolatile s, 0#64, s.readReg64 .x1) := by
  have r0 := hr ⟨0, by decide⟩
  simp only [BitVec.add_assoc] at r0
  change s.mem.canRead (s.sp + 256#64) 4 = true at r0
  have w0 : s.mem.canWrite (s.readReg64 .x1 + 0#64) 4 = true := hw ⟨0, by decide⟩
  have r1 := hr ⟨1, by decide⟩
  simp only [BitVec.add_assoc] at r1
  change s.mem.canRead (s.sp + 260#64) 4 = true at r1
  have w1 : s.mem.canWrite (s.readReg64 .x1 + 4#64) 4 = true := hw ⟨1, by decide⟩
  have r2 := hr ⟨2, by decide⟩
  simp only [BitVec.add_assoc] at r2
  change s.mem.canRead (s.sp + 264#64) 4 = true at r2
  have w2 : s.mem.canWrite (s.readReg64 .x1 + 8#64) 4 = true := hw ⟨2, by decide⟩
  have r3 := hr ⟨3, by decide⟩
  simp only [BitVec.add_assoc] at r3
  change s.mem.canRead (s.sp + 268#64) 4 = true at r3
  have w3 : s.mem.canWrite (s.readReg64 .x1 + 12#64) 4 = true := hw ⟨3, by decide⟩
  have r4 := hr ⟨4, by decide⟩
  simp only [BitVec.add_assoc] at r4
  change s.mem.canRead (s.sp + 272#64) 4 = true at r4
  have w4 : s.mem.canWrite (s.readReg64 .x1 + 16#64) 4 = true := hw ⟨4, by decide⟩
  have r5 := hr ⟨5, by decide⟩
  simp only [BitVec.add_assoc] at r5
  change s.mem.canRead (s.sp + 276#64) 4 = true at r5
  have w5 : s.mem.canWrite (s.readReg64 .x1 + 20#64) 4 = true := hw ⟨5, by decide⟩
  have r6 := hr ⟨6, by decide⟩
  simp only [BitVec.add_assoc] at r6
  change s.mem.canRead (s.sp + 280#64) 4 = true at r6
  have w6 : s.mem.canWrite (s.readReg64 .x1 + 24#64) 4 = true := hw ⟨6, by decide⟩
  have r7 := hr ⟨7, by decide⟩
  simp only [BitVec.add_assoc] at r7
  change s.mem.canRead (s.sp + 284#64) 4 = true at r7
  have w7 : s.mem.canWrite (s.readReg64 .x1 + 28#64) 4 = true := hw ⟨7, by decide⟩
  simp only [BitVec.add_zero] at w0
  rw [runWords_decode, exit_decoded]
  simp (config := { decide := true, maxDischargeDepth := 32 }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execAddSubImm, Arm64.execLdp, Arm64.execStp, Arm64.execDataProc1, Arm64.execMoveWide,
    Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg32,
    Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
    Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
    addWithCarry64_add, BitVec.truncate_eq_setWidth,
    r0, r1, r2, r3, r4, r5, r6, r7, w0, w1, w2, w3, w4, w5, w6, w7,
    read32_write32, read32_write32_disjoint, bv_add_sub_add_left, bv_sub_add_left, BitVec.add_assoc,
    digestWords_eight, wordVector_eight, storeDigestWords, reverseWord, List.range_succ]

theorem read32_byte (m : Arm64.Memory) (p : BitVec 64) (k : Fin 4) :
    (m.read32 p).extractLsb' (8 * k.val) 8 = m.read8 (p + BitVec.ofNat 64 k.val) := by
  rcases k with ⟨k, hk⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases k <;> interval_cases i <;>
    simp only [Arm64.Memory.read32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  all_goals simp (config := { decide := true })

theorem reverseWord_byte (w : BitVec 32) (k : Fin 4) :
    (reverseWord w).extractLsb' (8 * k.val) 8 = w.extractLsb' (8 * (3 - k.val)) 8 := by
  rcases k with ⟨k, hk⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases k <;> interval_cases i <;>
    simp only [reverseWord, Arm64.rev32_64, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  all_goals simp (config := { decide := true })

def memoryBytes32 (m : Arm64.Memory) (base : BitVec 64) : Vector (BitVec 8) 32 :=
  Vector.ofFn (fun i => m.read8 (base + BitVec.ofNat 64 i.val))

def digestBytes (H : Vector (BitVec 32) 8) : Vector (BitVec 8) 32 :=
  Vector.ofFn (fun i => (H[i.val / 4]!).extractLsb' (8 * (3 - i.val % 4)) 8)

theorem bytes_of_reversed_words (m : Arm64.Memory) (base : BitVec 64)
    (H : Vector (BitVec 32) 8) (h : wordVector 8 m base = H.map reverseWord) :
    memoryBytes32 m base = digestBytes H := by
  apply Vector.ext
  intro i hi
  simp only [memoryBytes32, digestBytes, Vector.getElem_ofFn]
  let j : Fin 8 := ⟨i / 4, by omega⟩
  let k : Fin 4 := ⟨i % 4, by omega⟩
  have hn : i = 4 * j.val + k.val := by dsimp [j, k]; omega
  have address : base + BitVec.ofNat 64 i =
      (base + BitVec.ofNat 64 (4 * j.val)) + BitVec.ofNat 64 k.val := by
    rw [hn, BitVec.ofNat_add, BitVec.add_assoc]
  have word : m.read32 (base + BitVec.ofNat 64 (4 * j.val)) = reverseWord (H[j.val]!) := by
    have point := congrArg (fun W : Vector (BitVec 32) 8 => W[j.val]!) h
    simpa [wordVector, j.isLt] using point
  rw [address, ← read32_byte m (base + BitVec.ofNat 64 (4 * j.val)) k, word, reverseWord_byte]

theorem exit_stores_bytes (s : Arm64.State)
    (hr : ∀ i : Fin 8, s.mem.canRead ((s.sp + 256#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    (runWords exitCode s).map (fun out =>
      (memoryBytes32 out.mem (out.readReg64 .x1), out.mem, returnStable out,
        out.sp, out.pc, nonvolatile out, out.readReg64 .x0, out.readReg64 .x1)) =
      some (digestBytes (wordVector 8 s.mem (s.sp + 256#64)), storeDigestWords s, returnStable s,
        s.sp + 416#64, s.readReg64 .x30, nonvolatile s, 0#64, s.readReg64 .x1) := by
  obtain ⟨out, he, post⟩ := exists_of_map_some _ _ _ (exit_stores s hr hw)
  simp only [Prod.mk.injEq] at post
  obtain ⟨words, mem, frame, sp, pc, nv, ret, x1⟩ := post
  have bytes := bytes_of_reversed_words out.mem (out.readReg64 .x1)
    (wordVector 8 s.mem (s.sp + 256#64)) words
  rw [he]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  exact ⟨bytes, mem, frame, sp, pc, nv, ret, x1⟩

end Crypto.ARM64.Imported
