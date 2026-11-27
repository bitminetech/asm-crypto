import Proofs.HMACSHA256.RISCV64Public
import Proofs.HMACSHA256.BorrowedNative

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference Crypto.Baseline
open Crypto.ARM64.Imported (memoryBytes32)

structure EntryInvocation (base : Addr) where
  state : CPU
  key : ByteList
  message : ByteList
  keyExtent : Nat
  messageExtent : Nat
  capacity : Nat
  caller : EntryCall base state key message keyExtent messageExtent capacity

structure KeyInvocation (base : Addr) where
  state : CPU
  input : ByteList
  extent : Nat
  caller : KeyCall base state input extent

structure FinishInvocation (base : Addr) where
  state : CPU
  inner : ByteList
  keyBlock : HmacKeyBlock
  extent : Nat
  caller : FinishCall base state inner keyBlock extent

def keyResult (base : Addr) (call : KeyInvocation base) (out : CPU) : Prop :=
  let s := call.state
  let scope := keyBorrow base s call.extent
  out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
  (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
  (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = (hmacKey call.input)[i.val].toBitVec) ∧
  ∀ p, scope.protected p → ¬ (keyWorkspace s).Contains p → ¬ (keyBlockRegion s).Contains p →
    out.mem.cells p = s.mem.cells p

def finishResult (base : Addr) (call : FinishInvocation base) (out : CPU) : Prop :=
  let s := call.state
  let scope := finishBorrow base s call.extent
  out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
  (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
  memoryBytes32 out.mem (s.reg 12#5) = (hmacFinish call.inner call.keyBlock).map UInt8.toBitVec ∧
  ∀ p, scope.protected p → ¬ (stackRegion (s.reg 2#5) 720).Contains p →
    ¬ (finishOutput s).Contains p → out.mem.cells p = s.mem.cells p

def entrySpecification : BorrowedNative where
  State := CPU
  Event := List Access
  Call := EntryInvocation
  Environment := fun {base} c => EntryEnvironment base c.state c.keyExtent c.messageExtent c.capacity
  Profile := LinkedTimingProfile
  scope := fun {base} c => entryBorrow base c.state c.keyExtent c.messageExtent c.capacity
  accesses e := e.map memoryEvent
  environmentAccess env := env.effect
  permittedEnvironment env := env.allowed
  result := fun {base} c out => ProtectedEntryResult c.state out
    (entryBorrow base c.state c.keyExtent c.messageExtent c.capacity) c.capacity (hmacSha256 c.key c.message c.capacity)
  stepBound c := entryStepBound c.key.bytes.size c.message.bytes.size c.capacity
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed c env profile events out cost := CostedScheduledExecution profile env.schedule 0 c.state events out cost
  samePublic a b := a.capacity = b.capacity ∧ EntryPublic a.state b.state a.key b.key a.message b.message

def keySpecification : BorrowedNative where
  State := CPU
  Event := List Access
  Call := KeyInvocation
  Environment := fun {base} c => NativeEnvironment (keyBorrow base c.state c.extent) c.state
  Profile := LinkedTimingProfile
  scope := fun {base} c => keyBorrow base c.state c.extent
  accesses e := e.map memoryEvent
  environmentAccess env := env.effect
  permittedEnvironment env := env.allowed
  result := fun {base} c out => keyResult base c out
  stepBound c := keyStepBound c.input.bytes.size
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed c env profile events out cost := CostedScheduledExecution profile env.schedule 0 c.state events out cost
  samePublic a b :=
    a.state.reg 2#5 = b.state.reg 2#5 ∧ a.state.reg 1#5 = b.state.reg 1#5 ∧
    a.state.reg 10#5 = b.state.reg 10#5 ∧ a.state.reg 11#5 = b.state.reg 11#5 ∧
    a.input.offset = b.input.offset ∧ a.input.bytes.size = b.input.bytes.size

def finishSpecification : BorrowedNative where
  State := CPU
  Event := List Access
  Call := FinishInvocation
  Environment := fun {base} c => NativeEnvironment (finishBorrow base c.state c.extent) c.state
  Profile := LinkedTimingProfile
  scope := fun {base} c => finishBorrow base c.state c.extent
  accesses e := e.map memoryEvent
  environmentAccess env := env.effect
  permittedEnvironment env := env.allowed
  result := fun {base} c out => finishResult base c out
  stepBound c := 75 + callSteps c.inner.bytes.size + callSteps 96
  scheduled := fun {base} c env events out => ScheduledExecution base env.schedule 0 c.state events out
  costed c env profile events out cost := CostedScheduledExecution profile env.schedule 0 c.state events out cost
  samePublic a b :=
    a.state.reg 2#5 = b.state.reg 2#5 ∧ a.state.reg 1#5 = b.state.reg 1#5 ∧
    a.state.reg 10#5 = b.state.reg 10#5 ∧ a.state.reg 11#5 = b.state.reg 11#5 ∧
    a.state.reg 12#5 = b.state.reg 12#5 ∧ a.inner.offset = b.inner.offset ∧ a.inner.bytes.size = b.inner.bytes.size

namespace hmac_sha256

def requirements : Stateless.Requirements := entrySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine entrySpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, events, ran, bound, _, result, safety⟩ := entry_execution_concurrent c.caller env
    refine ⟨out, events, ran, bound, result, ?_⟩
    intro event seen report member
    obtain ⟨access, observed, rfl⟩ := List.mem_map.mp member
    exact (safety event seen access observed).1
  · intro base l r envL envR same profile
    obtain ⟨s, keyS, msgS, nkS, nmS, capacity, left⟩ := l
    obtain ⟨t, keyT, msgT, nkT, nmT, capT, right⟩ := r
    obtain ⟨sameCap, sameData⟩ := same
    change capacity = capT at sameCap
    subst capT
    exact entry_public_execution left right envL envR sameData profile
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_sha256

namespace hmac_key

def requirements : Stateless.Requirements := keySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine keySpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, events, ran, bound, _, link, stack, regs, bytes, frame, safety⟩ := key_execution_concurrent c.caller env
    refine ⟨out, events, ran, bound, ⟨link, stack, regs, bytes, frame⟩, ?_⟩
    intro event seen report member
    obtain ⟨access, observed, rfl⟩ := List.mem_map.mp member
    exact (safety event seen access observed).1
  · intro base l r envL envR same profile
    obtain ⟨sp, link, input, output, offset, count⟩ := same
    exact key_public_execution l.caller r.caller envL envR sp link input output offset count profile
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_key

namespace hmac_finish

def requirements : Stateless.Requirements := finishSpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine finishSpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, events, ran, bound, _, link, stack, regs, digest, frame, safety⟩ :=
      finish_execution_concurrent c.caller env
    refine ⟨out, events, ran, bound, ⟨link, stack, regs, digest, frame⟩, ?_⟩
    intro event seen report member
    obtain ⟨access, observed, rfl⟩ := List.mem_map.mp member
    exact (safety event seen access observed).1
  · intro base l r envL envR same profile
    obtain ⟨sp, link, input, key, output, offset, count⟩ := same
    exact finish_public_execution l.caller r.caller envL envR sp link input key output offset count profile
  · intro base c env profile events out cost run
    exact CostedScheduledExecution.erase run

end hmac_finish
end Crypto.HMACSHA256.RISCV64
