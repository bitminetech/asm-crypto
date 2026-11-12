import Models.ARM64
import Proofs.ARM64.Round
import equiv.SHA256.Foldl.Sequential

/-!
Compression-round proofs over the pinned upstream AArch64 instruction semantics.
`round_computes` and `round_matches_spec` cover the 30 words at 0x124–0x198.
The imported memory permissions and SP alignment checks remain active.

`round_frame` preserves all state other than general registers and PC, preserves
X0–X6 and X18–X30, and advances PC by 120. X7–X17 are the fragment's working and
scratch registers. Instruction fetching, loop control, whole-call safety,
confidentiality and the complete `equal` baseline are separate obligations.

The closed decoder table below is proof support: Lean's kernel checks it against
both the recorded words and the unchanged imported decoder. It is not an assumed
instruction interpretation. The state projection proof pattern follows the
upstream `ProofLib/CoreLemmas.lean` (Apache-2.0); the upstream proof package is not
imported because its toolchain is newer than this repository's pinned Lean.
-/

namespace Crypto.ARM64.Imported

theorem addWithCarry32_add (x y : BitVec 32) :
    (Arm64.AddWithCarry32 x y false).1 = x + y := by
  simp [Arm64.AddWithCarry32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_add, BitVec.add_comm]

@[simp] theorem reg_advance (s : Arm64.State) (r : Arm64.Reg) :
    s.advancePC.readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] theorem mem_advance (s : Arm64.State) : s.advancePC.mem = s.mem := by cases s; rfl
@[simp] theorem sp_advance (s : Arm64.State) : s.advancePC.sp = s.sp := by cases s; rfl
@[simp] theorem aligned_advance (s : Arm64.State) : s.advancePC.spAligned = s.spAligned := by cases s; rfl
@[simp] theorem mem_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).mem = s.mem := by cases s; rfl
@[simp] theorem sp_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).sp = s.sp := by cases s; rfl
@[simp] theorem aligned_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).spAligned = s.spAligned := by cases s; rfl
@[simp] theorem reg_write_gpr (s : Arm64.State) (i j : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).readReg64 (.gpr j) =
      if j = 31#5 then 0 else if i = 31#5 then s.readReg64 (.gpr j)
        else if j = i then v else s.readReg64 (.gpr j) := by
  cases s
  by_cases hj : j = 31#5 <;> by_cases hi : i = 31#5 <;> by_cases hij : j = i <;>
    simp_all [Arm64.State.writeReg64, Arm64.State.readReg64, Arm64.RegFile.read,
      Arm64.RegFile.write]
@[simp] theorem read_sp (s : Arm64.State) : s.readReg64 .sp = s.sp := by cases s; rfl
@[simp] theorem read_zero (s : Arm64.State) : s.readReg64 .xzr = 0 := by cases s; rfl

@[simp] theorem pc_advance (s : Arm64.State) : s.advancePC.pc = s.pc + 4 := by cases s; rfl
@[simp] theorem pc_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).pc = s.pc := by cases s; rfl
@[simp] theorem status_advance (s : Arm64.State) : s.advancePC.status = s.status := by cases s; rfl
@[simp] theorem status_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).status = s.status := by cases s; rfl

/-- All state except the general registers and PC. -/
def stable (s : Arm64.State) : Arm64.State := { s with regs := Arm64.RegFile.empty, pc := 0 }
@[simp] theorem stable_advance (s : Arm64.State) : stable s.advancePC = stable s := by cases s; rfl
@[simp] theorem stable_write_gpr (s : Arm64.State) (i : BitVec 5) (v : BitVec 64) :
    stable (s.writeReg64 (.gpr i) v) = stable s := by cases s; rfl

def nonvolatile (s : Arm64.State) : Fin 13 → BitVec 64 :=
  fun i => s.readReg64 (.gpr (BitVec.ofNat 5 (18 + i.val)))
@[simp] theorem nv_advance (s : Arm64.State) : nonvolatile s.advancePC = nonvolatile s := by
  funext i; exact reg_advance s _
@[simp] theorem nv_write_gpr (s : Arm64.State) (index : BitVec 5) (value : BitVec 64)
    (hindex : index.toNat < 18) : nonvolatile (s.writeReg64 (.gpr index) value) = nonvolatile s := by
  funext i
  have hi := i.isLt
  have small : 18 + i.val < 32 := by omega
  have hneq : BitVec.ofNat 5 (18 + i.val) ≠ index := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at hn
    omega
  have h31 : BitVec.ofNat 5 (18 + i.val) ≠ 31#5 := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at hn
    change 18 + i.val = 31 at hn
    omega
  simp [nonvolatile, hneq, h31]

def working (s : Arm64.State) : Vector (BitVec 32) 8 :=
  #v[s.readReg32 .x7, s.readReg32 .x8, s.readReg32 .x9, s.readReg32 .x10,
     s.readReg32 .x11, s.readReg32 .x12, s.readReg32 .x13, s.readReg32 .x14]

def runWords : List (BitVec 32) → Arm64.State → Option Arm64.State
  | [], s => some s
  | word :: rest, s => (Arm64.decode word).bind fun instruction =>
      runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

def runDecoded : List Arm64.Instr → Arm64.State → Arm64.State
  | [], s => s
  | instruction :: rest, s => runDecoded rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s)

theorem runWords_decode (words : List (BitVec 32)) (s : Arm64.State) :
    runWords words s = (words.mapM Arm64.decode).map (fun decoded => runDecoded decoded s) := by
  induction words generalizing s with
  | nil => rfl
  | cons word rest ih =>
    cases hd : Arm64.decode word with
    | none => simp [runWords, hd, List.mapM_cons]
    | some instruction =>
      simp only [runWords, hd, List.mapM_cons, Bind.bind, Option.bind]
      rw [ih]
      cases rest.mapM Arm64.decode <;> simp [runDecoded]

private theorem round_decoded : Round.code.mapM Arm64.decode = some [
    .extr .W32 .x15 .x11 .x11 6,
    .logicalShift .W32 .EOR .x15 .x15 .x11 .ROR 11,
    .logicalShift .W32 .EOR .x15 .x15 .x11 .ROR 25,
    .addSubShift .W32 .ADD .x14 .x14 .x15 .LSL 0,
    .logicalShift .W32 .AND .x16 .x11 .x12 .LSL 0,
    .logicalShift .W32 .BIC .x17 .x13 .x11 .LSL 0,
    .logicalShift .W32 .ORR .x16 .x16 .x17 .LSL 0,
    .addSubShift .W32 .ADD .x14 .x14 .x16 .LSL 0,
    .ldr .W32 .W32 false .x16 (.RegOffset .x0 .x5 .UXTX 2),
    .ldr .W32 .W32 false .x17 (.RegOffset .sp .x5 .UXTX 2),
    .addSubShift .W32 .ADD .x14 .x14 .x16 .LSL 0,
    .addSubShift .W32 .ADD .x14 .x14 .x17 .LSL 0,
    .addSubShift .W32 .ADD .x10 .x10 .x14 .LSL 0,
    .extr .W32 .x15 .x7 .x7 2,
    .logicalShift .W32 .EOR .x15 .x15 .x7 .ROR 13,
    .logicalShift .W32 .EOR .x15 .x15 .x7 .ROR 22,
    .addSubShift .W32 .ADD .x14 .x14 .x15 .LSL 0,
    .logicalShift .W32 .ORR .x16 .x7 .x8 .LSL 0,
    .logicalShift .W32 .AND .x16 .x16 .x9 .LSL 0,
    .logicalShift .W32 .AND .x17 .x7 .x8 .LSL 0,
    .logicalShift .W32 .ORR .x16 .x16 .x17 .LSL 0,
    .addSubShift .W32 .ADD .x15 .x14 .x16 .LSL 0,
    .logicalShift .W32 .ORR .x14 .xzr .x13 .LSL 0,
    .logicalShift .W32 .ORR .x13 .xzr .x12 .LSL 0,
    .logicalShift .W32 .ORR .x12 .xzr .x11 .LSL 0,
    .logicalShift .W32 .ORR .x11 .xzr .x10 .LSL 0,
    .logicalShift .W32 .ORR .x10 .xzr .x9 .LSL 0,
    .logicalShift .W32 .ORR .x9 .xzr .x8 .LSL 0,
    .logicalShift .W32 .ORR .x8 .xzr .x7 .LSL 0,
    .logicalShift .W32 .ORR .x7 .xzr .x15 .LSL 0] := by decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem round_computes (s : Arm64.State)
    (hsp : s.spAligned = true)
    (hk : s.mem.canRead (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canRead (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true) :
    (runWords Round.code s).map working =
      some (Round.fipsRound (working s)
        (s.mem.read32 (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)))
        (s.mem.read32 (s.sp + (s.readReg64 .x5 <<< 2)))) := by
  rw [runWords_decode, round_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execLdr, Arm64.evalAddSub, Arm64.evalLogical,
    Arm64.shiftVal, Arm64.shift32, Arm64.extendVal, Arm64.evalAddrMode,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg32,
    Arm64.checkAddrSPAligned,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.MemWidth.bytes, Arm64.Memory.readSized, working,
    addWithCarry32_add, Round.extr_same, BitVec.truncate_eq_setWidth, hk, hw, hsp]
  simp (config := { decide := true }) [Round.fipsRound,
    SHS.SHA256.bigSigma0, SHS.SHA256.bigSigma1, SHS.SHA256.Ch, SHS.SHA256.Maj,
    SHS.ROTR, Round.ch_or_eq_xor, Round.maj_factored, BitVec.add_assoc,
    BitVec.rotateRight_def, BitVec.xor_assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem round_frame (s : Arm64.State)
    (hsp : s.spAligned = true)
    (hk : s.mem.canRead (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canRead (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true) :
    (runWords Round.code s).map (fun out =>
      (stable out, out.pc, nonvolatile out,
       out.readReg64 .x0, out.readReg64 .x1, out.readReg64 .x2,
       out.readReg64 .x3, out.readReg64 .x4, out.readReg64 .x5, out.readReg64 .x6)) =
      some (stable s, s.pc + 120, nonvolatile s,
       s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2,
       s.readReg64 .x3, s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6) := by
  rw [runWords_decode, round_decoded]
  simp [runDecoded, Arm64.execInstWithSvc, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execLdr, Arm64.evalAddSub, Arm64.evalLogical,
    Arm64.shiftVal, Arm64.shift32, Arm64.extendVal, Arm64.evalAddrMode,
    Arm64.State.readReg, Arm64.State.writeReg, Arm64.State.readReg32,
    Arm64.checkAddrSPAligned,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg,
    Arm64.MemWidth.bytes, Arm64.Memory.readSized,
    addWithCarry32_add, Round.extr_same, BitVec.truncate_eq_setWidth, hk, hw, hsp, BitVec.add_assoc]

/-- Exact bridge to the imported spec's sequential compression-loop step. -/
theorem round_matches_spec (s : Arm64.State) (W : Vector (BitVec 32) 64) (t : Nat)
    (hsp : s.spAligned = true)
    (hk : s.mem.canRead (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hw : s.mem.canRead (s.sp + (s.readReg64 .x5 <<< 2)) 4 = true)
    (hK : s.mem.read32 (s.readReg64 .x0 + (s.readReg64 .x5 <<< 2)) = SHS.SHA256.K[t]!)
    (hW : s.mem.read32 (s.sp + (s.readReg64 .x5 <<< 2)) = W[t]!) :
    (runWords Round.code s).map working =
      some (SHS.Equiv.SHA256.Foldl.Sequential.specRoundStep W t (working s)) := by
  rw [round_computes s hsp hk hw, hK, hW]
  rfl

end Crypto.ARM64.Imported
