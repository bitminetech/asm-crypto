import Proofs.HMACSHA256.ARM64Setup
import Proofs.HMACSHA256.Pad

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

private theorem opad_setup_decoded :
    decodeRange finish 0x44 4 = some [
      .moveWide .W64 .MOVZ .x11 92#16 0,
      .logicalImm .W64 .ORR .x9 .xzr 0x0101010101010101#64,
      .dataProc3 .W64 .MADD .x11 .x11 .x9 .xzr,
      .addSubImm .W64 .ADD .x8 .sp 120#12 false] := by decide +kernel

def opadStart (s : Arm64.State) : Arm64.State :=
  let st := s.writeReg64 .x9 0x0101010101010101#64
  let st := st.writeReg64 .x11 0x5c5c5c5c5c5c5c5c#64
  (st.writeReg64 .x8 (s.sp + 120#64)).setPC (s.pc + 16#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem opad_setup (s : Arm64.State) :
    runRange finish 0x44 4 s = some (opadStart s) := by
  unfold runRange
  rw [opad_setup_decoded]
  simp (config := { decide := true }) [runDecoded, Arm64.execInstWithSvc,
    Arm64.execMoveWide, Arm64.execLogicalImm, Arm64.evalLogical, Arm64.execDataProc3,
    Arm64.execAddSubImm, Arm64.evalAddSub, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x11, opadStart, addWithCarry64_add,
    BitVec.add_assoc]
  simp (config := { decide := true }) [Arm64.State.writeReg64, Arm64.State.advancePC,
    Arm64.State.setPC, Arm64.RegFile.write, Arm64.RegFile.read, BitVec.add_assoc]
  funext i
  by_cases h8 : i = 8#5 <;> by_cases h9 : i = 9#5 <;> by_cases h11 : i = 11#5 <;>
    simp [h8, h9, h11]

private def padPair (source : Arm64.Reg) (disp : Addr) : List Arm64.Instr := [
  .ldp .W64 false .x9 .x10 (.Offset source disp),
  .logicalShift .W64 .EOR .x9 .x9 .x11 .LSL 0,
  .logicalShift .W64 .EOR .x10 .x10 .x11 .LSL 0,
  .stp .W64 .x9 .x10 (.Offset .x8 disp)]

private theorem finish_pad_decoded :
    decodeRange finish 0x54 16 = some (padPair .x19 0#64 ++ padPair .x19 16#64 ++
      padPair .x19 32#64 ++ padPair .x19 48#64) := by decide +kernel

private theorem entry_pad_decoded :
    decodeRange entry 0x88 16 = some (padPair .x12 0#64 ++ padPair .x12 16#64 ++
      padPair .x12 32#64 ++ padPair .x12 48#64) := by decide +kernel

def pairMemory (s : Arm64.State) (source : Arm64.Reg) (disp : Addr) : Arm64.Memory :=
  let k0 := s.readReg64 source + disp
  let dst := s.readReg64 .x8 + disp
  let mask := s.readReg64 .x11
  (s.mem.write64 dst (s.mem.read64 k0 ^^^ mask)).write64 (dst + 8#64)
    (s.mem.read64 (k0 + 8#64) ^^^ mask)

def pairState (s : Arm64.State) (source : Arm64.Reg) (disp : Addr) : Arm64.State :=
  let k0 := s.readReg64 source + disp
  let mask := s.readReg64 .x11
  let updated := (s.setMem (pairMemory s source disp)).writeReg64 .x9 (s.mem.read64 k0 ^^^ mask)
  (updated.writeReg64 .x10 (s.mem.read64 (k0 + 8#64) ^^^ mask)).setPC (s.pc + 16#64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
private theorem run_pair (s : Arm64.State) (source : Arm64.Reg) (disp : Addr)
    (which : source = .x12 ∨ source = .x19)
    (r0 : s.mem.canRead (s.readReg64 source + disp) 8 = true)
    (r1 : s.mem.canRead (s.readReg64 source + disp + 8#64) 8 = true)
    (w0 : s.mem.canWrite (s.readReg64 .x8 + disp) 8 = true)
    (w1 : s.mem.canWrite (s.readReg64 .x8 + disp + 8#64) 8 = true) :
    runDecoded (padPair source disp) s = pairState s source disp := by
  rcases which with rfl | rfl <;>
    simp (config := { decide := true }) [padPair, runDecoded, Arm64.execInstWithSvc,
      Arm64.execLdp, Arm64.execStp, Arm64.execLogicalShift, Arm64.evalLogical,
      Arm64.State.readReg, Arm64.State.writeReg, Arm64.shiftVal, Arm64.shift64,
      Arm64.checkAddrSPAligned, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode,
      Arm64.MemWidth.bytes, Arm64.Memory.readSized, Arm64.Memory.writeSized,
      r0, r1, w0, w1, pairState, pairMemory, Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x10,
      Arm64.Reg.x11, Arm64.Reg.x12, Arm64.Reg.x19]
  all_goals simp [Arm64.State.setPC, Arm64.State.advancePC, Arm64.State.setMem,
    Arm64.State.writeReg64, Arm64.RegFile.write, BitVec.add_assoc]
  all_goals funext i
  all_goals by_cases eq9 : i = 9#5 <;> by_cases eq10 : i = 10#5 <;> simp [eq9, eq10]

private theorem run_append (a b : List Arm64.Instr) (s : Arm64.State) :
    runDecoded (a ++ b) s = runDecoded b (runDecoded a s) := by
  induction a generalizing s <;> simp_all [runDecoded]

private theorem pair_reg (s : Arm64.State) (source : Arm64.Reg) (disp : Addr) (r : BitVec 5)
    (keep9 : r ≠ 9#5) (keep10 : r ≠ 10#5) :
    (pairState s source disp).readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
  by_cases zero : r = 31#5
  · subst r
    rfl
  · simp [pairState, Arm64.Reg.x9, Arm64.Reg.x10, zero, keep9, keep10]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem padSteps (s : Arm64.State) (source : Arm64.Reg)
    (which : source = .x12 ∨ source = .x19)
    (read : ∀ i : Fin 8, s.mem.canRead (s.readReg64 source + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (write : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    let s1 := pairState s source 0#64
    let s2 := pairState s1 source 16#64
    let s3 := pairState s2 source 32#64
    let s4 := pairState s3 source 48#64
    (if source = .x12 then runRange entry 0x88 16 s else runRange finish 0x54 16 s) = some s4 := by
  dsimp only
  obtain ⟨sreg, definition, gt9, gt10⟩ : ∃ r : BitVec 5, source = .gpr r ∧ r ≠ 9#5 ∧ r ≠ 10#5 := by
    rcases which with eq | eq
    · exact ⟨12#5, eq, by decide, by decide⟩
    · exact ⟨19#5, eq, by decide, by decide⟩
  have srcKeep (st : Arm64.State) (d : Addr) :
      (pairState st source d).readReg64 source = st.readReg64 source := by
    rw [definition]; exact pair_reg _ _ _ _ gt9 gt10
  have dstKeep (st : Arm64.State) (d : Addr) :
      (pairState st source d).readReg64 .x8 = st.readReg64 .x8 :=
    pair_reg _ _ _ 8#5 (by decide) (by decide)
  have readable (st : Arm64.State) (d p : Addr) (h : st.mem.canRead p 8 = true) :
      (pairState st source d).mem.canRead p 8 = true :=
    canRead_write64 _ _ _ _ _ (canRead_write64 _ _ _ _ _ h)
  have writable (st : Arm64.State) (d p : Addr) :
      (pairState st source d).mem.canWrite p 8 = st.mem.canWrite p 8 := by
    change (pairMemory st source d).canWrite p 8 = _
    simp [pairMemory]
  have sameFragments :
      (if source = .x12 then decodeRange entry 0x88 16 else decodeRange finish 0x54 16) =
        some (padPair source 0#64 ++ padPair source 16#64 ++ padPair source 32#64 ++
          padPair source 48#64) := by
    rcases which with rfl | rfl
    · rw [if_pos rfl]
      exact entry_pad_decoded
    · rw [if_neg (by decide : Arm64.Reg.x19 ≠ Arm64.Reg.x12)]
      exact finish_pad_decoded
  have execEq :
      (if source = .x12 then runRange entry 0x88 16 s else runRange finish 0x54 16 s) =
        (if source = .x12 then decodeRange entry 0x88 16 else decodeRange finish 0x54 16).map
          (fun ops => runDecoded ops s) := by split <;> rfl
  rw [execEq, sameFragments]
  simp only [Option.map_some, run_append]
  have r0 := read ⟨0, by decide⟩
  have r1 := read ⟨1, by decide⟩
  have r2 := read ⟨2, by decide⟩
  have r3 := read ⟨3, by decide⟩
  have r4 := read ⟨4, by decide⟩
  have r5 := read ⟨5, by decide⟩
  have r6 := read ⟨6, by decide⟩
  have r7 := read ⟨7, by decide⟩
  have w0 := write ⟨0, by decide⟩
  have w1 := write ⟨1, by decide⟩
  have w2 := write ⟨2, by decide⟩
  have w3 := write ⟨3, by decide⟩
  have w4 := write ⟨4, by decide⟩
  have w5 := write ⟨5, by decide⟩
  have w6 := write ⟨6, by decide⟩
  have w7 := write ⟨7, by decide⟩
  rw [run_pair s source 0#64 which r0 (by simpa using r1) w0 (by simpa using w1)]
  let a := pairState s source 0#64
  have ar2 : a.mem.canRead (a.readReg64 source + 16#64) 8 = true := by
    rw [show a.readReg64 source = _ from srcKeep s 0#64]
    exact readable s 0#64 _ r2
  have ar3 : a.mem.canRead (a.readReg64 source + 16#64 + 8#64) 8 = true := by
    rw [show a.readReg64 source = _ from srcKeep s 0#64, BitVec.add_assoc]
    exact readable s 0#64 _ r3
  rw [run_pair a source 16#64 which ar2 ar3
    (by simpa [a, dstKeep, writable] using w2)
    (by simpa [a, dstKeep, writable, BitVec.add_assoc] using w3)]
  let b := pairState a source 16#64
  have br4 : b.mem.canRead (b.readReg64 source + 32#64) 8 = true := by
    rw [show b.readReg64 source = _ from srcKeep a 16#64, show a.readReg64 source = _ from srcKeep s 0#64]
    exact readable a 16#64 _ (readable s 0#64 _ r4)
  have br5 : b.mem.canRead (b.readReg64 source + 32#64 + 8#64) 8 = true := by
    rw [show b.readReg64 source = _ from srcKeep a 16#64, show a.readReg64 source = _ from srcKeep s 0#64,
      BitVec.add_assoc]
    exact readable a 16#64 _ (readable s 0#64 _ r5)
  rw [run_pair b source 32#64 which br4 br5
    (by simpa [b, a, dstKeep, writable] using w4)
    (by simpa [b, a, dstKeep, writable, BitVec.add_assoc] using w5)]
  let c := pairState b source 32#64
  have cr6 : c.mem.canRead (c.readReg64 source + 48#64) 8 = true := by
    rw [show c.readReg64 source = _ from srcKeep b 32#64, show b.readReg64 source = _ from srcKeep a 16#64,
      show a.readReg64 source = _ from srcKeep s 0#64]
    exact readable b 32#64 _ (readable a 16#64 _ (readable s 0#64 _ r6))
  have cr7 : c.mem.canRead (c.readReg64 source + 48#64 + 8#64) 8 = true := by
    rw [show c.readReg64 source = _ from srcKeep b 32#64, show b.readReg64 source = _ from srcKeep a 16#64,
      show a.readReg64 source = _ from srcKeep s 0#64, BitVec.add_assoc]
    exact readable b 32#64 _ (readable a 16#64 _ (readable s 0#64 _ r7))
  rw [run_pair c source 48#64 which cr6 cr7
    (by simpa [c, b, a, dstKeep, writable] using w6)
    (by simpa [c, b, a, dstKeep, writable, BitVec.add_assoc] using w7)]

private theorem pad_pair_memory (s current : Arm64.State) (source : Arm64.Reg)
    (n : Nat) (bound : n + 2 ≤ 8)
    (sourceEq : current.readReg64 source = s.readReg64 source)
    (destEq : current.readReg64 .x8 = s.readReg64 .x8)
    (maskEq : current.readReg64 .x11 = s.readReg64 .x11)
    (separation : ∀ i : Fin 64, 64 ≤
      (s.readReg64 source + BitVec.ofNat 64 i.val - s.readReg64 .x8).toNat)
    (memoryEq : current.mem =
      writeWords s.mem (s.readReg64 .x8)
        (fun j => s.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) ^^^
          s.readReg64 .x11) n) :
    (pairState current source (BitVec.ofNat 64 (8 * n))).mem =
      writeWords s.mem (s.readReg64 .x8)
        (fun j => s.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) ^^^
          s.readReg64 .x11) (n + 2) := by
  have sourceWord (j : Nat) (below : j < 8) :
      current.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) =
        s.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) := by
    apply read64_eq_of_cells
    intro i
    rw [memoryEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    apply writeWords_outside
    have near := separation ⟨8 * j + i.val, by have := i.isLt; omega⟩
    exact Nat.le_trans (by omega) near
  change pairMemory current source (BitVec.ofNat 64 (8 * n)) = _
  unfold pairMemory
  simp only [sourceEq, destEq, maskEq, BitVec.add_assoc, ← BitVec.ofNat_add]
  have following : 8 * n + 8 = 8 * (n + 1) := by omega
  change Arm64.Memory.write64
    (current.mem.write64 (s.readReg64 .x8 + BitVec.ofNat 64 (8 * n))
      (current.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * n)) ^^^ s.readReg64 .x11))
    (s.readReg64 .x8 + BitVec.ofNat 64 (8 * n + 8))
    (current.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * n + 8)) ^^^ s.readReg64 .x11) = _
  rw [following, sourceWord n (by omega), sourceWord (n + 1) (by omega), memoryEq]
  rfl

set_option maxRecDepth 8192 in
theorem pad_memory (s : Arm64.State) (source : Arm64.Reg)
    (which : source = .x12 ∨ source = .x19)
    (read : ∀ i : Fin 8, s.mem.canRead (s.readReg64 source + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (write : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (separation : ∀ i : Fin 64, 64 ≤
      (s.readReg64 source + BitVec.ofNat 64 i.val - s.readReg64 .x8).toNat) :
    ∃ out, (if source = .x12 then runRange entry 0x88 16 s else runRange finish 0x54 16 s) = some out ∧
      out.mem =
        writeWords s.mem (s.readReg64 .x8)
          (fun j => s.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) ^^^
            s.readReg64 .x11) 8 := by
  let a := pairState s source 0#64
  let b := pairState a source 16#64
  let c := pairState b source 32#64
  let d := pairState c source 48#64
  refine ⟨d, padSteps s source which read write, ?_⟩
  have src (st : Arm64.State) (n : Addr) :
      (pairState st source n).readReg64 source = st.readReg64 source := by
    rcases which with rfl | rfl
    · exact pair_reg _ _ _ 12#5 (by decide) (by decide)
    · exact pair_reg _ _ _ 19#5 (by decide) (by decide)
  have dest (st : Arm64.State) (n : Addr) :
      (pairState st source n).readReg64 .x8 = st.readReg64 .x8 :=
    pair_reg _ _ _ 8#5 (by decide) (by decide)
  have mask (st : Arm64.State) (n : Addr) :
      (pairState st source n).readReg64 .x11 = st.readReg64 .x11 :=
    pair_reg _ _ _ 11#5 (by decide) (by decide)
  have first := pad_pair_memory s s source 0 (by decide) rfl rfl rfl separation rfl
  have second := pad_pair_memory s a source 2 (by decide)
    (src _ _) (dest _ _) (mask _ _) separation first
  have third := pad_pair_memory s b source 4 (by decide)
    ((src _ _).trans (src _ _)) ((dest _ _).trans (dest _ _)) ((mask _ _).trans (mask _ _))
    separation second
  exact pad_pair_memory s c source 6 (by decide)
    ((src _ _).trans ((src _ _).trans (src _ _))) ((dest _ _).trans ((dest _ _).trans (dest _ _)))
    ((mask _ _).trans ((mask _ _).trans (mask _ _))) separation third

/-- AArch64 pad writes each XORed byte, with a frame for all addresses outside
the pad. The other code establishes which of EthLib's masks is in X11. -/
theorem pad_bytes (s : Arm64.State) (source : Arm64.Reg)
    (which : source = .x12 ∨ source = .x19)
    (read : ∀ i : Fin 8, s.mem.canRead (s.readReg64 source + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (write : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (separation : ∀ i : Fin 64, 64 ≤
      (s.readReg64 source + BitVec.ofNat 64 i.val - s.readReg64 .x8).toNat) :
    ∃ out, (if source = .x12 then runRange entry 0x88 16 s else runRange finish 0x54 16 s) = some out ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x8 + BitVec.ofNat 64 i.val) =
        s.mem.read8 (s.readReg64 source + BitVec.ofNat 64 i.val) ^^^
          (s.readReg64 .x11).extractLsb' (8 * (i.val % 8)) 8) ∧
      (∀ p, 64 ≤ (p - s.readReg64 .x8).toNat → out.mem.cells p = s.mem.cells p) ∧
      out.sp = s.sp ∧ out.status = s.status ∧ out.pc = s.pc + 64#64 ∧
      out.readReg64 .x20 = s.readReg64 .x20 := by
  obtain ⟨out, exec, memory⟩ := pad_memory s source which read write separation
  have executed := padSteps s source which read write
  have outEq := Option.some.inj (exec.symm.trans executed)
  have state : out.sp = s.sp ∧ out.status = s.status ∧ out.pc = s.pc + 64#64 ∧
      out.readReg64 .x20 = s.readReg64 .x20 := by
    rw [outEq]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [pairState, Arm64.State.setPC, Arm64.State.setMem, Arm64.State.writeReg64, BitVec.add_assoc]
      rfl
    · repeat' rw [pair_reg _ _ _ 20#5 (by decide) (by decide)]
  refine ⟨out, exec, ?_, ?_, state⟩
  · intro i
    let byte : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
    have lt : i.val / 8 < 8 := by have := i.isLt; omega
    have addr : 8 * (i.val / 8) + byte.val = i.val := by dsimp [byte]; omega
    rw [memory]
    have result := writeWords_byte s.mem (s.readReg64 .x8)
      (fun j => s.mem.read64 (s.readReg64 source + BitVec.ofNat 64 (8 * j)) ^^^
        s.readReg64 .x11) 8 (i.val / 8) byte lt (by decide)
    rw [maskedByte] at result
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, addr] using result
  · intro p h
    rw [memory]
    exact writeWords_outside _ _ _ 8 p h

theorem pad_preserves_gpr {s out : Arm64.State} {source : Arm64.Reg}
    (which : source = .x12 ∨ source = .x19)
    (read : ∀ i : Fin 8, s.mem.canRead (s.readReg64 source + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (write : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x8 + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (exec : (if source = .x12 then runRange entry 0x88 16 s else runRange finish 0x54 16 s) = some out)
    (r : BitVec 5) (keep9 : r ≠ 9#5) (keep10 : r ≠ 10#5) :
    out.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
  rw [Option.some.inj (exec.symm.trans (padSteps s source which read write))]
  repeat' rw [pair_reg _ _ _ r keep9 keep10]

end Crypto.HMACSHA256.ARM64
