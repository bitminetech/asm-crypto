import Proofs.RISCV64.BlockAccess
import Proofs.RISCV64.CallTrace
import Proofs.RISCV64.CheckedCall
import Proofs.RISCV64.PaddingAccess

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (memoryBytes32 paddingBlockCount)

private def Coverage (footprint : Access → Prop) (code : List Instruction) (s : CPU) : Prop :=
  ∀ a ∈ dataTrace code s, footprint a

private theorem Coverage.append {f : Access → Prop} {a b : List Instruction} {s : CPU}
    (left : Coverage f a s) (right : Coverage f b (run a s)) : Coverage f (a ++ b) s := by
  intro access found
  rw [dataTrace_append] at found
  exact (List.mem_append.mp found).elim (left access) (right access)

private theorem Coverage.follow {base : Addr} {f : Access → Prop} {a b : List Instruction} {s t : CPU}
    (step : ImageExecution base s a t) (left : Coverage f a s) (right : Coverage f b t) : Coverage f (a ++ b) s :=
  left.append (step.result ▸ right)

private theorem Coverage.empty {f : Access → Prop} {code : List Instruction}
    (noAccess : checkedFixedAccess code [] = true) (s : CPU) : Coverage f code s := by
  intro a found
  rw [empty_dataTrace noAccess] at found
  exact (List.not_mem_nil found).elim

private theorem block_data_call {base : Addr} {s t : CPU} {size blocks : Nat} {a : Access}
    (stack : t.reg 2 = entryStack s) (constants : t.reg 10 = base + BitVec.ofNat 64 constantsOffset)
    (payload : ∀ p w, InRegion (t.reg 12) (64*blocks) p w → CallData base s size (.read p w))
    (within : BlockLoopData (t.reg 2) (t.reg 12) (t.reg 10) blocks a) : CallData base s size a := by
  cases a with
  | fetch => exact within.elim
  | read p w =>
    rcases within with scratch | input | k
    · rw [stack] at scratch
      obtain ⟨off, fits, align, addr⟩ := scratch
      exact .inl ⟨off, Nat.le_trans fits (by decide : 288 ≤ 480), align, addr⟩
    · exact payload p w input
    · rw [constants] at k
      exact .inr (.inr (.inr (k.enclose (by decide +kernel) (by cases w <;> decide))))
  | write =>
    rw [stack] at within
    obtain ⟨off, fits, align, addr⟩ := within
    exact .inl ⟨off, Nat.le_trans fits (by decide : 288 ≤ 480), align, addr⟩

private def phaseChecks : List Instruction := [blockGuard, phaseGuard]
private def selectPadding : List Instruction := phaseChecks ++ paddingPhase

private theorem padding_pointer (s : CPU) : (run selectPadding s).reg 12 = s.reg 2 + 288 := by
  rw [selectPadding, run_append]
  have oldStack : (run phaseChecks s).reg 2 = s.reg 2 := run_reg_unchanged s _ _ (by decide)
  have newSource (t : CPU) : (run paddingPhase t).reg 12 = t.reg 2 + 288 := by
    simp (config := { decide := true }) [run, paddingPhase, Instruction.step, CPU.reg, CPU.put, CPU.advance]
  rw [newSource, oldStack]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4500000 in
private theorem hashing_coverage (base : Addr) (s t : CPU) (data : ByteArray)
    (h : BodyPrepared base s t data) :
    Coverage (CallData base s data.size)
      (blockLoop (data.size / 64) ++ (selectPadding ++
        (blockLoop (paddingBlockCount data) ++ (phaseChecks ++ (digestCode ++ returnCode))))) t := by
  let msg := run (blockLoop (data.size / 64)) t
  let pad := run selectPadding msg
  let last := run (blockLoop (paddingBlockCount data)) pad
  let emit := run phaseChecks last
  let restore := run digestCode emit
  obtain ⟨msgSp, msgK, msgDst, _, msgTrace⟩ := block_loop_accesses t (data.size / 64)
  have message : Coverage (CallData base s data.size) (blockLoop (data.size / 64)) t := by
    intro a observed
    apply block_data_call h.sp h.constants _ (msgTrace a observed)
    intro p w inside
    rw [h.input] at inside
    obtain ⟨off, fit, aligned, addr⟩ := inside
    exact .inr (.inr (.inl ⟨off, by have := Nat.div_add_mod data.size 64; omega, aligned, addr⟩))
  have padSp : pad.reg 2 = entryStack s :=
    (run_reg_unchanged msg selectPadding 2 (by decide)).trans (msgSp.trans h.sp)
  have padK : pad.reg 10 = base + BitVec.ofNat 64 constantsOffset :=
    (run_reg_unchanged msg selectPadding 10 (by decide)).trans (msgK.trans h.constants)
  have padDst : pad.reg 11 = s.reg 11 :=
    (run_reg_unchanged msg selectPadding 11 (by decide)).trans (msgDst.trans h.output)
  have padSrc : pad.reg 12 = entryStack s + 288 :=
    (padding_pointer msg).trans (congrArg (· + 288) (msgSp.trans h.sp))
  obtain ⟨lastSp, _, lastDst, _, padTrace⟩ := block_loop_accesses pad (paddingBlockCount data)
  have padding : Coverage (CallData base s data.size) (blockLoop (paddingBlockCount data)) pad := by
    intro a observed
    apply block_data_call padSp padK _ (padTrace a observed)
    intro p w inside
    rw [padSrc] at inside
    have fits : 288 + 64 * paddingBlockCount data ≤ 480 := by unfold paddingBlockCount; split <;> decide
    exact .inl (inside.enclose fits (by cases w <;> decide))
  have emitSp : emit.reg 2 = entryStack s :=
    (run_reg_unchanged last phaseChecks 2 (by decide)).trans (lastSp.trans padSp)
  have emitDst : emit.reg 11 = s.reg 11 :=
    (run_reg_unchanged last phaseChecks 11 (by decide)).trans (lastDst.trans padDst)
  have retSp : restore.reg 2 = entryStack s :=
    (run_reg_unchanged emit digestCode 2 (by decide)).trans emitSp
  have result : Coverage (CallData base s data.size) digestCode emit :=
    digest_accesses base s emit _ emitSp emitDst
  have returned : Coverage (CallData base s data.size) returnCode restore :=
    return_accesses base s restore _ retSp
  exact message.append ((Coverage.empty (by decide) msg).append
    (padding.append ((Coverage.empty (by decide) last).append (result.append returned))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
/-- Access ranges for the complete decoded call. The message header, used
payload, mapped image, 480-byte frame and 32-byte digest are the only regions. -/
theorem call_data_footprint (base : Addr) (s : CPU) (data : ByteArray) (entry : CallEntry base s data)
    (a : Access) (found : a ∈ dataTrace (callCode data.size) s) : CallData base s data.size a := by
  obtain ⟨frame, head, clear, start, save, header, zero, length, args⟩ := input_prepared base s data entry
  obtain ⟨copied, marked, padded, body, copy, marker, suffix, iv, h, pad⟩ := prepare_body base s start data entry args
  have frameSp : frame.reg 2 = entryStack s := by
    rw [save.result]
    exact (frame_entered base s entry.pc).2.2.1
  have headSp : head.reg 2 = entryStack s := (header.register_checked 2 (by decide)).trans frameSp
  have frameInput : frame.reg 10 = s.reg 10 := save.register_checked 10 (by decide)
  have rem : copied.reg 7 = BitVec.ofNat 64 (data.size % 64) :=
    (copy.register_checked 7 (tail_keeps _ 7 (by decide))).trans args.rem
  have padPtr : copied.reg 29 = entryStack s + 288 :=
    (copy.register_checked 29 (tail_keeps _ 29 (by decide))).trans args.pad
  have padSp : padded.reg 2 = entryStack s := (pad.kept 2 (by decide)).trans args.sp
  have rest := hashing_coverage base s body data h
  let f := CallData base s data.size
  have withIv : Coverage f _ padded := Coverage.follow iv (iv_accesses base s padded _ pad.pc padSp) rest
  have withLen : Coverage f _ marked := Coverage.follow suffix
    (length_accesses base s marked data pad.markerBase pad.markerCount) withIv
  have withMarker : Coverage f _ copied := Coverage.follow marker
    (marker_accesses base s copied _ rem padPtr) withLen
  have withCopy : Coverage f _ start := Coverage.follow copy (copy_accesses base s start data args) withMarker
  have withLengths : Coverage f _ clear := Coverage.follow length (Coverage.empty (by decide) clear) withCopy
  have withZero : Coverage f _ head := Coverage.follow zero (zero_accesses base s head _ headSp) withLengths
  have withHeader : Coverage f _ frame := Coverage.follow header (header_accesses base s frame _ frameInput) withZero
  have complete : Coverage f _ s := Coverage.follow save (save_accesses base s _) withHeader
  apply complete a
  simpa only [callCode, callBeforeReturn, selectPadding, phaseChecks, paddingBlockCount, List.append_assoc] using found

theorem call_initial_data_permitted (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data) (grants : CallRegionPermissions base s data.size) :
    ((accessTrace (callCode data.size) s).filter Access.isData).all (Access.permitted s.mem) = true := by
  rw [← dataTrace_eq]
  exact List.all_eq_true.mpr (fun a ha => grants.permits (call_data_footprint base s data entry a ha))

/-- Execute the callable routine using the permissions of the caller's
regions, with its exact instruction budget. -/
theorem run_sha256_from_regions (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data) (grants : CallRegionPermissions base s data.size)
    (outputOutside : ∀ i : Fin 32, 480 ≤ (s.reg 11 + BitVec.ofNat 64 i.val - entryStack s).toNat)
    (executable : s.mem.canExec base codeEnd = true) (readOnly : ImageReadOnly base s.mem) :
    ∃ out, runUntilReturn base s (callSteps data.size) = some out ∧
      out.pc = s.reg 1 &&& ~~~(1 : Addr) ∧ out.reg 10 = 0 ∧ out.reg 2 = s.reg 2 ∧
      savedRegisters out = savedRegisters s ∧
      memoryBytes32 out.mem (s.reg 11) = (Crypto.Reference.digest data).map UInt8.toBitVec ∧
      (∀ p, 480 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.reg 11).toNat →
        out.mem.cells p = s.mem.cells p) :=
  run_sha256 base s data entry outputOutside (by have := grants.imageAligned; omega) executable readOnly
    (call_initial_data_permitted base s data entry grants)

end Crypto.RISCV64
