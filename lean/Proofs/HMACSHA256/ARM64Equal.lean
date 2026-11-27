import Proofs.HMACSHA256.ARM64Bounds
import Proofs.HMACSHA256.ARM64Timing
import Proofs.HMACSHA256.BorrowedNative

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.Baseline Crypto.ARM64.Imported

structure EntryInvocation (base : Addr) where
  state : Arm64.State
  key : ByteList
  message : ByteList
  keyExtent : Nat
  messageExtent : Nat
  capacity : Nat
  caller : EntryCall base state key message keyExtent messageExtent capacity

structure KeyInvocation (base : Addr) where
  state : Arm64.State
  input : ByteList
  extent : Nat
  caller : KeyCall base state input extent

structure FinishInvocation (base : Addr) where
  state : Arm64.State
  inner : ByteList
  keyBlock : HmacKeyBlock
  extent : Nat
  caller : FinishCall base state inner keyBlock extent

def keyResult (base : Addr) (call : KeyInvocation base) (out : Arm64.State) : Prop :=
  let s := call.state
  let scope := keyBorrow base s call.extent
  out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
  (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
  (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = (hmacKey call.input)[i.val].toBitVec) ∧
  ∀ p, scope.protected p → ¬ (keyWorkspace s).Contains p → ¬ (keyOutput s).Contains p → out.mem.cells p = s.mem.cells p

def finishResult (base : Addr) (call : FinishInvocation base) (out : Arm64.State) : Prop :=
  let s := call.state
  let scope := finishBorrow base s call.extent
  out.sp = s.sp ∧ out.pc = s.readReg64 .lr ∧ out.status = .Running ∧
  (∀ i : Fin 12, out.readReg64 (savedRegister i.val) = s.readReg64 (savedRegister i.val)) ∧
  memoryBytes32 out.mem (s.readReg64 .x2) = (hmacFinish call.inner call.keyBlock).map UInt8.toBitVec ∧
  ∀ p, scope.protected p → ¬ (finishWorkspace s).Contains p → ¬ (finishMac s).Contains p → out.mem.cells p = s.mem.cells p

def entrySpecification : BorrowedNative where
  State := Arm64.State
  Event := InstructionObservation
  Call := EntryInvocation
  Environment := fun {base} c => NativeEnvironment (entryBorrow base c.state c.keyExtent c.messageExtent c.capacity) c.state
  Profile := fun _ => LinkedTimingProfile
  scope := fun {base} c => entryBorrow base c.state c.keyExtent c.messageExtent c.capacity
  accesses e := [observedAccessEvent e]
  environmentAccess env := env.schedule.event
  permittedEnvironment env tick state := env.schedule.accesses tick state trivial
  result := fun {base} c out => ProtectedEntryResult c.state out c.key c.message c.capacity
    (entryBorrow base c.state c.keyExtent c.messageExtent c.capacity)
  stepBound c := entryStepBound c.key.bytes.size c.message.bytes.size
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed := fun {base} c env profile events out cost => CostedScheduledExecution base profile env.schedule 0 c.state events out cost
  samePublic a b := a.capacity = b.capacity ∧ EntryPublic a.state b.state a.key b.key a.message b.message

def keySpecification : BorrowedNative where
  State := Arm64.State
  Event := InstructionObservation
  Call := KeyInvocation
  Environment := fun {base} c => NativeEnvironment (keyBorrow base c.state c.extent) c.state
  Profile := fun _ => LinkedTimingProfile
  scope := fun {base} c => keyBorrow base c.state c.extent
  accesses e := [observedAccessEvent e]
  environmentAccess env := env.schedule.event
  permittedEnvironment env tick state := env.schedule.accesses tick state trivial
  result := fun {base} c out => keyResult base c out
  stepBound c := keyStepBound c.input.bytes.size
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed := fun {base} c env profile events out cost => CostedScheduledExecution base profile env.schedule 0 c.state events out cost
  samePublic a b := KeyPublic a.state b.state a.input b.input

def finishSpecification : BorrowedNative where
  State := Arm64.State
  Event := InstructionObservation
  Call := FinishInvocation
  Environment := fun {base} c => NativeEnvironment (finishBorrow base c.state c.extent) c.state
  Profile := fun _ => LinkedTimingProfile
  scope := fun {base} c => finishBorrow base c.state c.extent
  accesses e := [observedAccessEvent e]
  environmentAccess env := env.schedule.event
  permittedEnvironment env tick state := env.schedule.accesses tick state trivial
  result := fun {base} c out => finishResult base c out
  stepBound c := finishStepBound c.inner.bytes.size
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed := fun {base} c env profile events out cost => CostedScheduledExecution base profile env.schedule 0 c.state events out cost
  samePublic a b := FinishPublic a.state b.state a.inner b.inner

namespace hmac_sha256

def requirements : Stateless.Requirements := entrySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine entrySpecification.equal ?_ ?_ (fun _ => instructionUnits) ?_
  · intro base c env
    obtain ⟨out, obs, run, result, accesses, trace⟩ := entry_execution_concurrent c.caller env
    refine ⟨out, obs, run, entry_trace_step_bound trace, result, ?_⟩
    intro e member access seen
    obtain rfl : access = observedAccessEvent e := List.mem_singleton.mp seen
    exact accesses e member
  · intro base l r envL envR same profile
    obtain ⟨s, keyS, msgS, nkS, nmS, capacity, left⟩ := l
    obtain ⟨t, keyT, msgT, nkT, nmT, capacityT, right⟩ := r
    obtain ⟨cap, publicData⟩ := same
    change capacity = capacityT at cap
    subst capacityT
    obtain ⟨u, v, events, a, b, _, _⟩ := entry_scheduled_public left right publicData envL envR
    exact ⟨u, v, events, _, a.costed profile, b.costed profile⟩
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_sha256

namespace hmac_key

def requirements : Stateless.Requirements := keySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine keySpecification.equal ?_ ?_ (fun _ => instructionUnits) ?_
  · intro base c env
    obtain ⟨out, obs, run, sp, link, live, regs, key, frame, accesses, trace⟩ := key_execution_concurrent c.caller env
    refine ⟨out, obs, run, key_trace_step_bound trace, ⟨sp, link, live, regs, key, frame⟩, ?_⟩
    intro e member access seen
    obtain rfl : access = observedAccessEvent e := List.mem_singleton.mp seen
    exact accesses e member
  · intro base l r envL envR same profile
    obtain ⟨u, v, events, a, b, _, _⟩ := key_scheduled_public l.caller r.caller same envL envR
    exact ⟨u, v, events, _, a.costed profile, b.costed profile⟩
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_key

namespace hmac_finish

def requirements : Stateless.Requirements := finishSpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine finishSpecification.equal ?_ ?_ (fun _ => instructionUnits) ?_
  · intro base c env
    obtain ⟨out, obs, run, sp, link, live, regs, digest, frame, accesses, _, body, trace⟩ :=
      finish_execution_concurrent c.caller env
    refine ⟨out, obs, run, ?_, ⟨sp, link, live, regs, digest, frame⟩, ?_⟩
    · rw [trace]
      exact finish_body_step_bound body
    · intro e member access seen
      obtain rfl : access = observedAccessEvent e := List.mem_singleton.mp seen
      exact accesses e member
  · intro base l r envL envR same profile
    obtain ⟨u, v, events, a, b, _, _⟩ := finish_scheduled_public l.caller r.caller same envL envR
    exact ⟨u, v, events, _, a.costed profile, b.costed profile⟩
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_finish
end Crypto.HMACSHA256.ARM64
