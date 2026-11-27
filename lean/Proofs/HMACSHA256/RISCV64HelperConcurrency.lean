import Proofs.HMACSHA256.RISCV64EntryConcurrency

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (BorrowScope Region CallAccess DataRace)
open Crypto.ARM64.Imported (caller_region_contains_offset memoryBytes32)

def keyBorrow (base : Addr) (s : CPU) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (keyInputRegion s extent).Contains p
  exclusive p := (keyWorkspace s).Contains p ∨ (keyBlockRegion s).Contains p

def finishBorrow (base : Addr) (s : CPU) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (finishInput s extent).Contains p ∨ (finishKey s).Contains p
  exclusive p := (stackRegion (s.reg 2#5) 720).Contains p ∨ (finishOutput s).Contains p

structure KeyCall (base : Addr) (s : CPU) (input : ByteList) (extent : Nat) : Prop where
  pc : s.pc = routineAddress base key
  layout : input.WellFormed
  accessible : input.size ≤ extent
  sizeBound : input.size < 2 ^ 64
  lengthBound : input.bytes.size < 2 ^ 61
  encoded : EncodedByteList s.mem (s.reg 10#5) input
  resources : KeyResources base s extent
  sha : ShaCode (shaAddress base) s.mem
  code : RoutineGrant base key s.mem
  returnAligned : (s.reg 1#5).toNat % 2 = 0

structure FinishCall (base : Addr) (s : CPU) (inner : ByteList) (k0 : HmacKeyBlock) (extent : Nat) : Prop where
  pc : s.pc = routineAddress base finish
  layout : inner.WellFormed
  accessible : inner.size ≤ extent
  sizeBound : inner.size < 2 ^ 64
  lengthBound : inner.bytes.size < 2 ^ 61
  encoded : EncodedByteList s.mem (s.reg 10#5) inner
  keyAt : ∀ i : Fin 64, s.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec
  resources : FinishResources base (s.put 2#5 (s.reg 2#5 - 240#64)) extent
  sha : ShaCode (shaAddress base) s.mem
  code : RoutineGrant base finish s.mem
  stackAvailable : 720 ≤ (s.reg 2#5).toNat
  stackRead : s.mem.canRead (s.reg 2#5 - 240#64) 240 = true
  stackWrite : s.mem.canWrite (s.reg 2#5 - 240#64) 240 = true
  keyAligned : (s.reg 11#5).toNat % 8 = 0
  keyRead : s.mem.canRead (s.reg 11#5) 64 = true
  returnAligned : (s.reg 1#5).toNat % 2 = 0

def AllowedTrace (scope : BorrowScope) {s : CPU} (environment : NativeEnvironment scope s)
    (events : List (List Access)) : Prop :=
  ∀ event ∈ events, ∀ access ∈ event, CallAccess scope (memoryEvent access) ∧
    ∀ tick machine, ¬ DataRace (memoryEvent access) (environment.effect tick machine)

private theorem allowed_trace {base : Addr} {s out : CPU} {events : List (List Access)}
    (run : ProgramExecution base s events out) {scope : BorrowScope}
    (env : NativeEnvironment scope s) : AllowedTrace scope env events := by
  intro event happened a observed
  exact ⟨run.borrowed_accesses scope env.permissions event happened a observed,
    fun tick cpu => run.no_data_race scope env.permissions _ (env.allowed tick cpu) event happened a observed⟩

private theorem borrowed_register {scope : Addr → Prop} {serial actual : CPU}
    (same : BorrowAgreement scope serial actual) (r : Reg) : actual.reg r = serial.reg r := by
  unfold CPU.reg
  rw [← same.registers]

theorem key_execution_concurrent {base : Addr} {s : CPU} {input : ByteList} {extent : Nat}
    (caller : KeyCall base s input extent) (environment : NativeEnvironment (keyBorrow base s extent) s) :
    ∃ actual events, ScheduledExecution base environment.schedule 0 s events actual ∧
      events.length ≤ keyStepBound input.bytes.size ∧ KeyTrace base s input events ∧
      actual.pc = s.reg 1#5 ∧ actual.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, actual.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, actual.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec) ∧
      (∀ p, (keyBorrow base s extent).protected p → ¬ (keyWorkspace s).Contains p →
        ¬ (keyBlockRegion s).Contains p → actual.mem.cells p = s.mem.cells p) ∧
      AllowedTrace (keyBorrow base s extent) environment events := by
  let scope := keyBorrow base s extent
  obtain ⟨serial, events, run, bound, pc, sp, saved, bytes, frame, trace⟩ := key_execution_from_caller
    base s input extent caller.pc caller.layout caller.accessible caller.sizeBound caller.lengthBound
    caller.encoded caller.resources caller.sha caller.code.loaded caller.code.aligned caller.code.executable caller.returnAligned
  obtain ⟨actual, schedule, same⟩ := run.scheduled_borrowed scope environment.permissions
    caller.sha.executable environment.schedule 0
  refine ⟨actual, events, schedule, bound, trace, same.pc.symm.trans pc, (borrowed_register same _).trans sp,
    fun i => (borrowed_register same _).trans (saved i), ?_, ?_, allowed_trace run environment⟩
  · intro i
    have owned : scope.protected (s.reg 11#5 + BitVec.ofNat 64 i.val) :=
      .inr (.inr (caller_region_contains_offset (keyBlockRegion s) caller.resources.blockValid i.val i.isLt))
    exact (read8_same _ (same.memory _ owned).symm).trans (bytes i)
  · intro p owned offStack offOutput
    exact (same.memory p owned).symm.trans (frame p offStack offOutput)

theorem finish_execution_concurrent {base : Addr} {s : CPU} {inner : ByteList}
    {k0 : HmacKeyBlock} {extent : Nat}
    (caller : FinishCall base s inner k0 extent) (environment : NativeEnvironment (finishBorrow base s extent) s) :
    ∃ actual events, ScheduledExecution base environment.schedule 0 s events actual ∧
      events.length ≤ 75 + callSteps inner.bytes.size + callSteps 96 ∧
      FinishTrace base s inner k0 events ∧ actual.pc = s.reg 1#5 ∧ actual.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, actual.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      memoryBytes32 actual.mem (s.reg 12#5) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, (finishBorrow base s extent).protected p → ¬ (stackRegion (s.reg 2#5) 720).Contains p →
        ¬ (finishOutput s).Contains p → actual.mem.cells p = s.mem.cells p) ∧
      AllowedTrace (finishBorrow base s extent) environment events := by
  let scope := finishBorrow base s extent
  obtain ⟨serial, events, run, bound, sp, pc, saved, digest, frame, trace⟩ := finish_execution_from_caller
    base s inner k0 extent caller.pc caller.layout caller.accessible caller.sizeBound caller.lengthBound
    caller.encoded caller.keyAt caller.resources caller.sha caller.code.loaded caller.code.aligned caller.code.executable
    caller.stackAvailable caller.stackRead caller.stackWrite caller.keyAligned caller.keyRead caller.returnAligned
  obtain ⟨actual, schedule, same⟩ := run.scheduled_borrowed scope environment.permissions
    caller.sha.executable environment.schedule 0
  refine ⟨actual, events, schedule, bound, trace, same.pc.symm.trans pc, (borrowed_register same _).trans sp,
    fun i => (borrowed_register same _).trans (saved i), ?_, ?_, allowed_trace run environment⟩
  · have valid : (finishOutput s).Valid := by
      have sameOutput : finishOutput (s.put 2#5 (s.reg 2#5 - 240#64)) = finishOutput s := by
        simp (config := {decide := true}) only [finishOutput, reg_put, if_false]
      exact sameOutput ▸ caller.resources.outputValid
    rw [← digest]
    apply Vector.ext
    intro i hi
    simp only [memoryBytes32, Vector.getElem_ofFn]
    have owned : scope.protected (s.reg 12#5 + BitVec.ofNat 64 i) :=
      .inr (.inr (caller_region_contains_offset (finishOutput s) valid i hi))
    exact read8_same _ (same.memory _ owned).symm
  · intro p owned offStack offOutput
    exact (same.memory p owned).symm.trans (frame p offStack offOutput)

end Crypto.HMACSHA256.RISCV64
