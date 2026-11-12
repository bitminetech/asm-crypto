import Proofs.ARM64.ImportedInitialLoad
import Proofs.ARM64.ImportedCompression
import Proofs.ARM64.ImportedMemoryRange
import Proofs.ARM64.ImportedScheduleCycle
import Proofs.ARM64.ImportedScheduleLoops

/-!
The recorded LDR/REV/STR message-word body and its ADD/CMP/B.LO control.
Byte-order lemmas identify the result with the four input bytes in big-endian
order. The cycle preserves the stated state frame and updates exactly one
workspace word. Complete loop execution, ByteList decoding and fetching remain
separate obligations.
-/
namespace Crypto.ARM64.Imported

def wordLoadCode : List (BitVec 32) := (imageWords.toList.drop 43).take 3
private theorem word_load_decoded : wordLoadCode.mapM Arm64.decode = some [
  .ldr .W32 .W32 false .x15 (.RegOffset .x2 .x5 .UXTX 2),
  .dataProc1 .W32 .REV .x15 .x15,
  .str .W32 .x15 (.RegOffset .sp .x5 .UXTX 2)] := by decide +kernel

def reverseWord (w : BitVec 32) : BitVec 32 :=
  (Arm64.rev32_64 (w.setWidth 64)).setWidth 32

def loadedWord (s : Arm64.State) : BitVec 32 :=
  reverseWord (s.mem.read32 (s.readReg64 .x2 + (s.readReg64 .x5 <<< 2)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem word_load (s : Arm64.State) (hsp : s.spAligned = true)
    (hr : s.mem.canRead (s.readReg64 .x2 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canWrite (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true) :
    (runWords wordLoadCode s).map (fun out =>
      (stable out, out.pc, nonvolatile out, working out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
      some ({ stable s with mem := s.mem.write32 (s.sp + (s.readReg64 .x5 <<< 2)) (loadedWord s) },
        s.pc + 12#64, nonvolatile s, working s,
        s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
        s.readReg64 .x3, s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6) := by
  rw [runWords_decode, word_load_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execStr,
    Arm64.execDataProc1, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.State.readReg32, Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned,
    Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.extendVal, Arm64.MemWidth.bytes,
    Arm64.Memory.readSized, Arm64.Memory.writeSized, BitVec.truncate_eq_setWidth,
    hsp, hr, hw, loadedWord, reverseWord, working, BitVec.add_assoc]

theorem reverseWord_bytes (b0 b1 b2 b3 : BitVec 8) :
    reverseWord (b3 ++ b2 ++ b1 ++ b0) = b0 ++ b1 ++ b2 ++ b3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [reverseWord, Arm64.rev32_64, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  all_goals simp (config := { decide := true })

theorem loadedWord_bytes (s : Arm64.State) :
    loadedWord s =
      let base := s.readReg64 .x2 + (s.readReg64 .x5 <<< 2)
      s.mem.read8 base ++ s.mem.read8 (base + 1#64) ++
        s.mem.read8 (base + 2#64) ++ s.mem.read8 (base + 3#64) := by
  simp only [loadedWord, Arm64.Memory.read32, reverseWord_bytes, BitVec.add_zero]

def wordControlCode : List (BitVec 32) := (imageWords.toList.drop 46).take 3
private theorem word_control_decoded : wordControlCode.mapM Arm64.decode = some [
  .addSubImm .W64 .ADD .x5 .x5 1#12 false,
  .addSubImm .W64 .SUBS .xzr .x5 16#12 false,
  .bCond .CC 0xffffffffffffffec#64] := by decide +kernel

set_option maxRecDepth 4096 in
theorem counter16_carry (t : Fin 16) :
    (Arm64.AddWithCarry64 (BitVec.ofNat 64 t.val + 1#64) 0xffffffffffffffef#64 true).2.c =
      decide (16 ≤ t.val + 1) := by
  rcases t with ⟨t, ht⟩
  change (Arm64.AddWithCarry64 (BitVec.ofNat 64 t + 1#64) 0xffffffffffffffef#64 true).2.c = decide (16 ≤ t + 1)
  interval_cases t <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem word_control_step (s : Arm64.State) (t : Fin 16)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    (runWords wordControlCode s).map (fun out =>
      (controlStable out, out.pc, nonvolatile out, working out,
        out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
        out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
    some (controlStable s, (if t.val + 1 < 16 then s.pc - 12#64 else s.pc + 12#64),
      nonvolatile s, working s,
      s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
      s.readReg64 .x4, BitVec.ofNat 64 (t.val + 1), s.readReg64 .x6) := by
  rw [runWords_decode, word_control_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.evalAddSub,
    Arm64.State.readReg, Arm64.State.writeReg, addWithCarry64_add, hc,
    Arm64.ConditionHolds, counter16_carry, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    apply_ite, ite_apply]
  all_goals simp (config := { decide := true }) [BitVec.ofNat_add]
  all_goals split <;> omega


def wordCycleCode : List (BitVec 32) := wordLoadCode ++ wordControlCode

theorem word_cycle (s : Arm64.State) (t : Fin 16) (hsp : s.spAligned = true)
    (hr : s.mem.canRead (s.readReg64 .x2 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canWrite (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    ∃ after, runWords wordCycleCode s = some after ∧ DataFrame s after ∧
      after.pc = (if t.val + 1 < 16 then s.pc else s.pc + 24#64) ∧
      after.readReg64 .x5 = BitVec.ofNat 64 (t.val + 1) ∧
      after.mem = s.mem.write32 (s.sp + (s.readReg64 .x5 <<< 2)) (loadedWord s) ∧
      wordVector 64 after.mem after.sp =
        (wordVector 64 s.mem s.sp).set! t.val (loadedWord s) := by
  obtain ⟨body, hb, frame⟩ := exists_of_map_some _ _ _ (word_load s hsp hr hw)
  simp only [Prod.mk.injEq] at frame
  obtain ⟨hst, hpc, hnv, _work, h0, h1, h2, h3, h4, h5, h6⟩ := frame
  obtain ⟨after, ha, post⟩ := exists_of_map_some _ _ _ (word_control_step body t (h5.trans hc))
  simp only [Prod.mk.injEq] at post
  obtain ⟨hst', hpc', hnv', _work', h0', h1', h2', h3', h4', h5', h6'⟩ := post
  have eraseBody : nonMemory body = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem] using congrArg nonMemory hst
  have eraseAfter : nonMemory after = nonMemory body := by
    simpa only [nonMemory_controlStable] using congrArg nonMemory hst'
  have memBody : body.mem = s.mem.write32 (s.sp + (s.readReg64 .x5 <<< 2)) (loadedWord s) := by
    have result := congrArg Arm64.State.mem hst
    exact result
  have memAfter : after.mem = body.mem := by
    have result := congrArg Arm64.State.mem hst'
    exact result
  have df : DataFrame s after :=
    ⟨eraseAfter.trans eraseBody, hnv'.trans hnv,
      h0'.trans h0, h1'.trans h1, h2'.trans h2, h3'.trans h3, h4'.trans h4, h6'.trans h6⟩
  refine ⟨after, ?_, df, ?_, h5', memAfter.trans memBody, ?_⟩
  · exact runWords_append_success hb ha
  · rw [hpc', hpc]
    split <;> simp_all [BitVec.add_assoc, BitVec.add_sub_cancel]
  · have address : s.sp + (s.readReg64 .x5 <<< 2) = s.sp + BitVec.ofNat 64 (4 * t.val) := by
      rw [hc]
      exact congrArg (s.sp + ·) (index_shift_two (t.castLE (by decide : 16 ≤ 64)))
    rw [memAfter, memBody, df.sp, address]
    exact wordVector_store64 s.mem s.sp (t.castLE (by decide : 16 ≤ 64)) (loadedWord s)

end Crypto.ARM64.Imported
