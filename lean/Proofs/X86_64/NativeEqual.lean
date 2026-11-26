import Proofs.X86_64.NativePlatform
import Proofs.Reference
import Proofs.StatelessBaseline

namespace Crypto.X86_64.NativeRequirements
open X86 Crypto.Baseline
open Crypto.ARM64.PlatformProfile (EnvironmentBackingEvent)

def ReferenceConformance : Prop :=
  ∀ (message : Crypto.Reference.ByteList) (bound : message.bytes.size < 2^61),
    Crypto.Reference.MatchesFIPS message (Crypto.Reference.sha256 message).2 bound ∧
    (Crypto.Reference.sha256 message).1 = 0

def Serial : Prop :=
  ∀ base s message extent authority, PermissionEntry base s message extent authority →
    ∃ out events, NativeSerial base s out message extent authority events

def Reentry : Prop :=
  ∀ (outer other : BorrowScope), CompatibleBorrows outer other →
    ∀ i s operands, ScalarLeaf i → dataAccesses i s = some operands →
      CallAccess other (ReportedAccess s.rip i operands) →
      KeepsBorrowed outer s.mem.read (X86.step i s).mem.read ∧
        EnvironmentAccess outer (ReportedAccess s.rip i operands)

def Concurrent : Prop :=
  ∀ base s message extent authority, PermissionEntry base s message extent authority →
    ∀ env : Environment (callBorrow base s extent),
      ∃ out events, ScheduledResult base s out message extent authority env events

def BackingProtection : Prop :=
  ∀ (Lease : Type) (scope : BorrowScope) (map : BackingMap Lease scope)
    (env : Environment scope) (schedule : BackedSchedule map env) (tick : Nat) (s : Cpu)
    (event : EnvironmentBackingEvent Lease), event ∈ schedule.events tick s →
    ∀ p, map.resolve p = some event.location →
      (scope.protected p → event.kind ≠ .release ∧ event.kind ≠ .protectionChange) ∧
      ∀ localEvent : AccessEvent, CallAccess scope localEvent →
        (localEvent.reads p → event.kind ≠ .write) ∧
        (localEvent.writes p → event.kind ≠ .write ∧ event.kind ≠ .read)

def PlatformCorrespondence : Prop :=
  ∀ (Hardware Opaque : Type) base s message extent authority,
    PermissionEntry base s message extent authority →
    ∀ (env : Environment (callBorrow base s extent)) (platform : PlatformModel Hardware Opaque base env)
      (hardware : Hardware), platform.project hardware = s →
      ∃ out physical, ScheduledResult base s out message extent authority env (callEvents base s message) ∧
        NativeExecution platform 0 hardware (callEvents base s message) physical ∧
        platform.project physical = out ∧ platform.abi physical = platform.abi hardware

def PublicTrace : Prop :=
  ∀ base left right l r le re la ra a b x y,
    SameContext left right l r →
    NativeSerial base left a l le la x → NativeSerial base right b r re ra y →
    x = y ∧ a.rip = b.rip ∧ a.regs.get .rsp = b.regs.get .rsp

def Disclosures : Prop :=
  ∀ base left right l r le re la ra a b x y,
    PermissionEntry base left l le la → PermissionEntry base right r re ra →
    SameContext left right l r →
    (∀ p, publicByte left l p → ¬(outputRegion left).Contains p → left.mem.read p = right.mem.read p) →
    (Crypto.Reference.sha256 l).2 = (Crypto.Reference.sha256 r).2 →
    NativeSerial base left a l le la x → NativeSerial base right b r re ra y →
    ReturnedAgreement left right a b l r

def Timing : Prop :=
  ∀ (profile : TimingProfile) base left right l r le re la ra a b x y,
    SameContext left right l r →
    ∀ (lenv : Environment (callBorrow base left le)) (renv : Environment (callBorrow base right re)),
      ScheduledResult base left a l le la lenv x → ScheduledResult base right b r re ra renv y →
      (∀ e ∈ x, profile.admits e.2.1) →
      ∃ cost, ScheduledCost base profile lenv 0 left x a cost ∧ ScheduledCost base profile renv 0 right y b cost

def LeafEffects : Prop :=
  ∀ base s out events, ObservedExecution base s events out →
    (∀ e ∈ events, ScalarLeaf e.2.1 ∧
      ∀ p, ¬(ReportedAccess e.1 e.2.1 e.2.2).releases p ∧
        ¬(ReportedAccess e.1 e.2.1 e.2.2).changesProtection p) ∧
    platformState out = platformState s

def requirements : Stateless.Requirements where
  referenceAndSafety := ReferenceConformance ∧ Serial
  concurrentExecution := Concurrent ∧ Reentry ∧ BackingProtection ∧ PlatformCorrespondence
  publicControlAndAddresses := PublicTrace
  permittedDisclosures := Disclosures
  instructionTiming := Timing
  leafAndEffects := LeafEffects

theorem referenceConformance : ReferenceConformance :=
  fun message bound => ⟨Crypto.Reference.sha256_matches_fips message bound,Crypto.Reference.sha256_status message⟩

theorem serial : Serial := by
  intro base s message extent authority entry
  obtain ⟨out,run⟩ := sha256_native_serial entry
  exact ⟨out,_,run⟩

theorem concurrent : Concurrent := by
  intro base s message extent authority entry env
  obtain ⟨out,run⟩ := sha256_scheduled entry env
  exact ⟨out,_,run⟩

theorem reentry : Reentry := by
  intro outer other compatible instruction cpu operands admitted observed allowed
  exact compatible_call_step compatible admitted observed allowed

theorem backingProtection : BackingProtection := by
  intro Lease scope map env schedule tick s event present p resolved
  exact ⟨fun owned => schedule.preserves_lifetime tick s event present p owned resolved,
    schedule.no_backing_race tick s event present p resolved⟩

theorem platformCorrespondence : PlatformCorrespondence := by
  intro Hardware Opaque base s message extent authority entry env platform hardware start
  exact sha256_native_platform entry env platform hardware start

theorem publicTrace : PublicTrace := by
  intro base left right l r le re la ra a b x y ctx one two
  exact ⟨one.publicTrace.trans ((same_call_events ctx).trans two.publicTrace.symm),
    one.result.pc.trans (ctx.link.trans two.result.pc.symm),by rw [one.result.stack,two.result.stack,ctx.stack]⟩

theorem disclosures : Disclosures := by
  intro base left right l r le re la ra a b x y leftEntry rightEntry ctx publicBytes digestEqual one two
  obtain ⟨a',b',first,second,result⟩ := sha256_disclosures leftEntry.toCallerEntry rightEntry.toCallerEntry ctx publicBytes digestEqual
  obtain rfl := Option.some.inj (one.returned.symm.trans first)
  obtain rfl := Option.some.inj (two.returned.symm.trans second)
  exact result

theorem timing : Timing := by
  intro profile base left right l r le re la ra a b x y ctx lenv renv one two covered
  have same : x = y := one.publicTrace.trans ((same_call_events ctx).trans two.publicTrace.symm)
  subst y
  exact scheduled_cost_equal one.execution two.execution (one.pc.trans (ctx.link.trans two.pc.symm)) covered

theorem leafEffects : LeafEffects := by
  intro base s out events execution
  refine ⟨?_,execution.erase.platform⟩
  intro e member
  exact ⟨execution.erase.scalar _ (List.mem_map_of_mem member),fun _ => ⟨id,id⟩⟩

end Crypto.X86_64.NativeRequirements

namespace Crypto.X86_64.sha256

/-- Scalar x86-64 SHA-256 satisfies the stateless baseline under the native
permission, loading, interference and timing profile assumptions. -/
theorem equal : Crypto.Baseline.Stateless.Equal NativeRequirements.requirements :=
  ⟨⟨NativeRequirements.referenceConformance, NativeRequirements.serial⟩, ⟨NativeRequirements.concurrent,NativeRequirements.reentry,NativeRequirements.backingProtection,
      NativeRequirements.platformCorrespondence⟩,
    NativeRequirements.publicTrace, NativeRequirements.disclosures, NativeRequirements.timing, NativeRequirements.leafEffects⟩

end Crypto.X86_64.sha256
