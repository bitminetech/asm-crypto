import Proofs.RISCV64.ABI
import Proofs.RISCV64.Borrowing
import Proofs.StatelessBaseline

namespace Crypto.RISCV64

open Crypto.Baseline (AccessEvent CallAccess EnvironmentAccess DataRace borrow_accesses_race_free)
open Crypto.ARM64.Imported (memoryBytes32 caller_region_contains_offset)

structure CallResult (before out : CPU) (message : Crypto.Reference.ByteList) : Prop where
  pc : out.pc = before.reg 1
  status : out.reg 10 = BitVec.ofNat 64 (Crypto.Reference.sha256 message).1
  sp : out.reg 2 = before.reg 2
  restored : savedRegisters out = savedRegisters before
  untouched : ∀ r ∈ untouchedABIRegs, out.reg r = before.reg r
  digest : memoryBytes32 out.mem (before.reg 11) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec

def FrameResult (before out : CPU) : Prop :=
  ∀ p, ¬ (callerStack before).Contains p → ¬ (callerOutput before).Contains p →
    out.mem.cells p = before.mem.cells p

theorem caller_result (base : Addr) (s : CPU) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) :
    ∃ out, runUntilReturn base s (callSteps message.bytes.size) = some out ∧
      CallResult s out message ∧ FrameResult s out := by
  obtain ⟨out, run, pc, status, sp, saved, digest, frame⟩ := caller_sha256 base s message extent entry
  obtain ⟨inputs, grants⟩ := entry.decoded_layout
  obtain ⟨target, call, _⟩ := serial_sha256 base s message.bytes inputs entry.output_outside
  have decoded := call.decoded
  have data := call_initial_data_permitted base s message.bytes inputs grants
  have allowed := decoded.initial_permitted s.mem (by have := entry.imageAligned; omega) entry.textExecute data
  have path := permittedPath_of_accesses base s _ entry.loaded entry.imageReadOnly allowed
  have executed := decoded.to_first_return path (call_has_return message.bytes.size)
  have budget : (callCode message.bytes.size).length = callSteps message.bytes.size := call_instruction_count _
  rw [budget, run] at executed
  obtain rfl := Option.some.inj executed
  exact ⟨out, run, ⟨pc, status, sp, saved, call.untouched_regs, digest⟩, frame⟩

private theorem agrees_on_result {base : Addr} {s serial actual : CPU}
    {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) (result : CallResult s serial message)
    (agree : BorrowAgreement (callBorrow base s extent).protected serial actual) : CallResult s actual message := by
  have regs (r : Reg) : actual.reg r = serial.reg r := by unfold CPU.reg; rw [← agree.registers]
  have save : savedRegisters actual = savedRegisters serial := by simp only [savedRegisters, regs]
  have digest : memoryBytes32 actual.mem (s.reg 11) = memoryBytes32 serial.mem (s.reg 11) := by
    apply Vector.ext
    intro i hi
    simp only [memoryBytes32, Vector.getElem_ofFn]
    apply read8_same
    exact (agree.memory _ (.inr (.inr
      (caller_region_contains_offset (callerOutput s) entry.outputValid i hi)))).symm
  exact ⟨agree.pc.symm.trans result.pc, (regs 10).trans result.status, (regs 2).trans result.sp,
    save.trans result.restored, fun r hr => (regs r).trans (result.untouched r hr), digest.trans result.digest⟩

structure BorrowedEnvironment (base : Addr) (s : CPU) (extent : Nat) where
  schedule : MemorySchedule (callBorrow base s extent).protected
  events : Nat → CPU → AccessEvent
  allowed : ∀ tick state, EnvironmentAccess (callBorrow base s extent) (events tick state)

theorem caller_interleaved (base : Addr) (s : CPU) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) (env : BorrowedEnvironment base s extent) (timing : TimingProfile) :
    ∃ out,
      runScheduledUntilReturn base env.schedule 0 s (callSteps message.bytes.size) =
        some (out, accessTrace (callCode message.bytes.size) s) ∧
      runScheduledCosted base env.schedule timing 0 s (callSteps message.bytes.size) =
        some (out, timing.runCost (callCode message.bytes.size) s) ∧
      CallResult s out message ∧
      ∀ a ∈ accessTrace (callCode message.bytes.size) s,
        CallAccess (callBorrow base s extent) (memoryEvent a) ∧
          ∀ tick state, ¬DataRace (memoryEvent a) (env.events tick state) := by
  obtain ⟨out, serial, executed, serialExecuted, timed, agreement, accesses⟩ :=
    caller_scheduled_path base s message extent entry env.schedule timing
  obtain ⟨target, returned, result, _⟩ := caller_result base s message extent entry
  rw [serialExecuted] at returned
  obtain rfl := Option.some.inj returned
  refine ⟨out, executed, timed, agrees_on_result entry result agreement, ?_⟩
  intro a observed
  have grant := accesses a observed
  exact ⟨grant, fun tick state => borrow_accesses_race_free _ _ _ grant (env.allowed tick state)⟩

structure SamePublicCall (s t : CPU) (a b : Crypto.Reference.ByteList) : Prop where
  regs : PublicAgreement (publicRegs entryPublicRegs) s t
  count : a.bytes.size = b.bytes.size
  payload : inputPayload s = inputPayload t

theorem caller_public_trace (base : Addr) (s t : CPU) (a b : Crypto.Reference.ByteList) (n m : Nat)
    (left : CallerEntry base s a n) (right : CallerEntry base t b m) (publicData : SamePublicCall s t a b) :
    accessTrace (callCode a.bytes.size) s = accessTrace (callCode b.bytes.size) t :=
  call_public_accesses base s t a.bytes b.bytes left.decoded_layout.1 right.decoded_layout.1
    publicData.regs publicData.count publicData.payload

theorem caller_public_timing (base : Addr) (s t : CPU) (a b : Crypto.Reference.ByteList) (n m : Nat)
    (left : CallerEntry base s a n) (right : CallerEntry base t b m) (publicData : SamePublicCall s t a b)
    (envS : BorrowedEnvironment base s n) (envT : BorrowedEnvironment base t m) (timing : TimingProfile) :
    ∃ u v cost,
      runScheduledCosted base envS.schedule timing 0 s (callSteps a.bytes.size) = some (u, cost) ∧
      runScheduledCosted base envT.schedule timing 0 t (callSteps b.bytes.size) = some (v, cost) := by
  have same := call_public_cost timing base s t a.bytes b.bytes left.decoded_layout.1 right.decoded_layout.1
    publicData.regs publicData.count publicData.payload
  obtain ⟨u, _, runs, _⟩ := caller_interleaved base s a n left envS timing
  obtain ⟨v, _, other, _⟩ := caller_interleaved base t b m right envT timing
  exact ⟨u, v, _, runs, by rw [same]; exact other⟩

def FunctionalSafety : Prop :=
  ∀ base s message extent, CallerEntry base s message extent →
    ∃ out, runUntilReturn base s (callSteps message.bytes.size) = some out ∧
      CallResult s out message ∧ FrameResult s out

private def instructionUnits : TimingProfile where
  cost _ _ := 1
  observedCost _ _ _ := 1
  observationLaw _ _ := rfl

def ConcurrentSafety : Prop :=
  ∀ base s message extent, CallerEntry base s message extent →
    ∀ (env : BorrowedEnvironment base s extent), ∃ out,
      runScheduledUntilReturn base env.schedule 0 s (callSteps message.bytes.size) =
        some (out, accessTrace (callCode message.bytes.size) s) ∧
      CallResult s out message ∧
      ∀ a ∈ accessTrace (callCode message.bytes.size) s,
        ∀ tick state, ¬DataRace (memoryEvent a) (env.events tick state)

def PublicControl : Prop :=
  ∀ base s t a b n m, CallerEntry base s a n → CallerEntry base t b m → SamePublicCall s t a b →
    accessTrace (callCode a.bytes.size) s = accessTrace (callCode b.bytes.size) t

def Disclosures : Prop :=
  ∀ base s message extent, CallerEntry base s message extent →
    ∀ out, runUntilReturn base s (callSteps message.bytes.size) = some out →
      memoryBytes32 out.mem (s.reg 11) = (Crypto.Reference.sha256 message).2.map UInt8.toBitVec ∧ FrameResult s out

def ModeledTiming : Prop :=
  ∀ base s t a b n m, CallerEntry base s a n → CallerEntry base t b m → SamePublicCall s t a b →
    ∀ (envS : BorrowedEnvironment base s n) (envT : BorrowedEnvironment base t m) (timing : TimingProfile),
      ∃ u v cost,
        runScheduledCosted base envS.schedule timing 0 s (callSteps a.bytes.size) = some (u, cost) ∧
        runScheduledCosted base envT.schedule timing 0 t (callSteps b.bytes.size) = some (v, cost)

def LeafEffects : Prop :=
  ∀ base s message extent, CallerEntry base s message extent →
    ∀ a ∈ accessTrace (callCode message.bytes.size) s, CallAccess (callBorrow base s extent) (memoryEvent a)

def modeledRequirements : Crypto.Baseline.Stateless.Requirements where
  referenceAndSafety := FunctionalSafety
  concurrentExecution := ConcurrentSafety
  publicControlAndAddresses := PublicControl
  permittedDisclosures := Disclosures
  instructionTiming := ModeledTiming
  leafAndEffects := LeafEffects

/-- The shared stateless baseline specialized to the checked scalar RV64GC
model and its explicit loader, borrow and timing assumptions. -/
theorem modeled_baseline : Crypto.Baseline.Stateless.Equal modeledRequirements := by
  refine ⟨caller_result, ?_, caller_public_trace, ?_, caller_public_timing, ?_⟩
  · intro base s message extent entry env
    obtain ⟨out, run, _, result, safe⟩ := caller_interleaved base s message extent entry env instructionUnits
    exact ⟨out, run, result, fun a ha => (safe a ha).2⟩
  · intro base s message extent entry out executed
    obtain ⟨expected, returned, result, frame⟩ := caller_result base s message extent entry
    rw [executed] at returned
    obtain rfl := Option.some.inj returned
    exact ⟨result.digest, frame⟩
  · intro base s message extent entry a observed
    obtain ⟨out, path, _⟩ := serial_sha256 base s message.bytes entry.decoded_layout.1 entry.output_outside
    exact borrowed_access_safe entry path.decoded a observed

end Crypto.RISCV64
