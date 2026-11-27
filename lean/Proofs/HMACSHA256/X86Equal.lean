import Proofs.HMACSHA256.X86Bounds
import Proofs.HMACSHA256.X86Public
import Proofs.HMACSHA256.BorrowedNative

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference Crypto.Baseline
open Crypto.ARM64.Imported (memoryBytes32)

structure EntryInvocation (base : Val) where
  state : Cpu
  key : ByteList
  message : ByteList
  keyExtent : Nat
  messageExtent : Nat
  capacity : Nat
  authority : Authority
  caller : EntryCall base state key message keyExtent messageExtent capacity authority
  rights : ScopedAuthority (entryBorrow base state keyExtent messageExtent capacity) authority

structure KeyInvocation (base : Val) where
  state : Cpu
  input : ByteList
  extent : Nat
  authority : Authority
  caller : KeyCall base state input extent authority
  rights : ScopedAuthority (keyBorrow base state extent) authority

structure FinishInvocation (base : Val) where
  state : Cpu
  inner : ByteList
  keyBlock : HmacKeyBlock
  extent : Nat
  authority : Authority
  caller : FinishCall base state inner keyBlock extent authority
  rights : ScopedAuthority (finishBorrow base state extent) authority

def keyResult (base : Val) (call : KeyInvocation base) (out : Cpu) : Prop :=
  let s := call.state
  let scope := keyBorrow base s call.extent
  out.ms = none ∧ out.flags.df = s.flags.df ∧
  out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧ out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
  (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧
  (∀ i : Fin 64, out.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = (hmacKey call.input)[i.val].toBitVec) ∧
  (∀ p, scope.protected p → ¬ (keyWorkspace s).Contains p → ¬ (keyOutput s).Contains p → out.mem.read p = s.mem.read p) ∧
  platformState out = platformState s

def finishResult (base : Val) (call : FinishInvocation base) (out : Cpu) : Prop :=
  let s := call.state
  let scope := finishBorrow base s call.extent
  out.ms = none ∧ out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧ out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
  (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧
  memoryBytes32 (byteView out.mem) (s.regs.get .rdx) = (hmacFinish call.inner call.keyBlock).map UInt8.toBitVec ∧
  (∀ p, scope.protected p → ¬ (finishWorkspace s).Contains p → ¬ (finishMac s).Contains p → out.mem.read p = s.mem.read p) ∧
  platformState out = platformState s

def entrySpecification : BorrowedNative where
  State := Cpu
  Event := Event
  Call := EntryInvocation
  Environment := fun {base} c => Environment (entryBorrow base c.state c.keyExtent c.messageExtent c.capacity)
  Profile := LinkedTimingProfile
  scope := fun {base} c => entryBorrow base c.state c.keyExtent c.messageExtent c.capacity
  accesses e := [ReportedAccess e.1 e.2.1 e.2.2]
  environmentAccess env := env.event
  permittedEnvironment env := env.permitted
  result := fun {base} c out => ScheduledEntryResult (entryBorrow base c.state c.keyExtent c.messageExtent c.capacity)
    c.state out c.key c.message c.capacity ∧ platformState out = platformState c.state
  stepBound c := entryStepBound c.key.bytes.size c.message.bytes.size
  scheduled := fun {base} c env events out => LinkedSchedule base c.authority env 0 c.state events out
  costed c env profile events out cost := CostedLinkedSchedule profile c.authority env 0 c.state events out cost
  samePublic a b := a.capacity = b.capacity ∧ EntryPublic a.state b.state a.key b.key a.message b.message ∧
    a.state.mem.readSize .q (a.state.regs.get .rsp) = b.state.mem.readSize .q (b.state.regs.get .rsp)

def keySpecification : BorrowedNative where
  State := Cpu
  Event := Event
  Call := KeyInvocation
  Environment := fun {base} c => Environment (keyBorrow base c.state c.extent)
  Profile := LinkedTimingProfile
  scope := fun {base} c => keyBorrow base c.state c.extent
  accesses e := [ReportedAccess e.1 e.2.1 e.2.2]
  environmentAccess env := env.event
  permittedEnvironment env := env.permitted
  result := fun {base} c out => keyResult base c out
  stepBound c := keyStepBound c.input.bytes.size
  scheduled := fun {base} c env events out => LinkedSchedule base c.authority env 0 c.state events out
  costed c env profile events out cost := CostedLinkedSchedule profile c.authority env 0 c.state events out cost
  samePublic a b := KeyPublic a.state b.state a.input b.input ∧
    a.state.mem.readSize .q (a.state.regs.get .rsp) = b.state.mem.readSize .q (b.state.regs.get .rsp)

def finishSpecification : BorrowedNative where
  State := Cpu
  Event := Event
  Call := FinishInvocation
  Environment := fun {base} c => Environment (finishBorrow base c.state c.extent)
  Profile := LinkedTimingProfile
  scope := fun {base} c => finishBorrow base c.state c.extent
  accesses e := [ReportedAccess e.1 e.2.1 e.2.2]
  environmentAccess env := env.event
  permittedEnvironment env := env.permitted
  result := fun {base} c out => finishResult base c out
  stepBound c := finishStepBound c.inner.bytes.size
  scheduled := fun {base} c env events out => LinkedSchedule base c.authority env 0 c.state events out
  costed c env profile events out cost := CostedLinkedSchedule profile c.authority env 0 c.state events out cost
  samePublic a b := FinishPublic a.state b.state a.inner b.inner ∧
    a.state.mem.readSize .q (a.state.regs.get .rsp) = b.state.mem.readSize .q (b.state.regs.get .rsp)

namespace hmac_sha256

def requirements : Stateless.Requirements := entrySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine entrySpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, ran, result, access, platform⟩ := entry_execution_concurrent c.caller c.rights env
    refine ⟨out, _, ran, entry_native_step_bound base c.state c.key c.message c.capacity, ⟨result, platform⟩, ?_⟩
    intro event present report member
    obtain rfl : report = ReportedAccess event.1 event.2.1 event.2.2 := List.mem_singleton.mp member
    exact access event present
  · intro base l r envL envR same profile
    obtain ⟨s, keyS, msgS, nkS, nmS, capacity, authS, left, rightsS⟩ := l
    obtain ⟨t, keyT, msgT, nkT, nmT, capT, authT, right, rightsT⟩ := r
    obtain ⟨capacities, sameData, link⟩ := same
    change capacity = capT at capacities
    subst capT
    exact entry_public_execution left right rightsS rightsT envL envR sameData link profile
  · intro base c env profile events out cost run
    exact CostedLinkedSchedule.erase run

end hmac_sha256

namespace hmac_key

def requirements : Stateless.Requirements := keySpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine keySpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, ran, live, direction, stack, link, regs, bytes, frame, access, platform⟩ :=
      key_execution_concurrent c.caller c.rights env
    refine ⟨out, _, ran, key_native_step_bound base c.state c.input,
      ⟨live, direction, stack, link, regs, bytes, frame, platform⟩, ?_⟩
    intro event present report member
    obtain rfl : report = ReportedAccess event.1 event.2.1 event.2.2 := List.mem_singleton.mp member
    exact access event present
  · intro base l r envL envR same profile
    exact key_public_execution l.caller r.caller l.rights r.rights envL envR same.1 same.2 profile
  · intro base c env profile events out cost run
    exact CostedLinkedSchedule.erase run

end hmac_key

namespace hmac_finish

def requirements : Stateless.Requirements := finishSpecification.requirements

theorem equal : Stateless.Equal requirements := by
  refine finishSpecification.equal ?_ ?_ instructionUnits ?_
  · intro base c env
    obtain ⟨out, ran, live, stack, link, regs, digest, frame, access, platform⟩ :=
      finish_execution_concurrent c.caller c.rights env
    refine ⟨out, _, ran, finish_native_step_bound base c.state c.inner c.keyBlock,
      ⟨live, stack, link, regs, digest, frame, platform⟩, ?_⟩
    intro event present report member
    obtain rfl : report = ReportedAccess event.1 event.2.1 event.2.2 := List.mem_singleton.mp member
    exact access event present
  · intro base l r envL envR same profile
    exact finish_public_execution l.caller r.caller l.rights r.rights envL envR same.1 same.2 profile
  · intro base c env profile events out cost run
    exact CostedLinkedSchedule.erase run

end hmac_finish
end Crypto.HMACSHA256.X86_64
