import Proofs.X86_64.TraceSafety
import Proofs.X86_64.TraceLength
import Proofs.X86_64.SerialContract
import Proofs.X86_64.Timing
import Proofs.X86_64.Disclosure
import Proofs.ARM64.ImportedPlatformProfile

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.PlatformProfile (EnvironmentBackingEvent EventReported)
open Crypto.ARM64.Imported (DataAccess digestBytes memoryBytes32)

def fetchByte (trace : List Event) (p : Val) : Prop :=
  ∃ e ∈ trace, DataByte ⟨false,e.1,e.2.1.len⟩ p

/-- Permissions come from the caller's independent extents, not from the
ByteList's embedded size. The return slot has a shared read grant. -/
structure PermissionEntry (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) : Prop extends CallerEntry base s message extent where
  canonicalData : ∀ p, (callBorrow base s extent).protected p → canonical p = true
  readable : ∀ p, callRead base s message extent p → authority.readable p
  writable : ∀ p, (callBorrow base s extent).exclusive p → authority.writable p
  executable : ∀ j < codeEnd, authority.executable (base+BitVec.ofNat 64 j)

/-- A byte alias is checked at backing storage identity. Code and input may share
read-only backing bytes. Every independent writable byte must have a distinct
identity from every other borrowed byte. -/
structure BackingMap (Lease : Type) (scope : BorrowScope) where
  resolve : Val → Option (Crypto.ARM64.OwnedView.LeaseByte Lease)
  mapped : ∀ p, scope.protected p → ∃ physical, resolve p = some physical
  isolated : ∀ p q physical, scope.exclusive p → scope.protected q → resolve p = some physical →
    resolve q = some physical → p = q

/-- Report physical environment actions at every borrowed alias. The actual
OS/other-thread boundary provides this correspondence and keeps the leases
and grants live as well as the contents required by the logical schedule. -/
def BackingMap.reports {Lease : Type} {scope : BorrowScope} (map : BackingMap Lease scope)
    (events : List (EnvironmentBackingEvent Lease)) (report : AccessEvent) : Prop :=
  ∀ event ∈ events, ∀ p, scope.protected p → map.resolve p = some event.location →
    EventReported report event.kind p

theorem protected_backing_lifetime {Lease : Type} {scope : BorrowScope} (map : BackingMap Lease scope)
    {events : List (EnvironmentBackingEvent Lease)} {report : AccessEvent}
    (reported : map.reports events report) (allowed : EnvironmentAccess scope report)
    (event : EnvironmentBackingEvent Lease) (present : event ∈ events)
    (p : Val) (inside : scope.protected p) (resolved : map.resolve p = some event.location) :
    event.kind ≠ .release ∧ event.kind ≠ .protectionChange := by
  have sound := reported event present p inside resolved
  constructor
  · intro eq
    rw [eq] at sound
    exact allowed.2.2.1 p inside sound
  · intro eq
    rw [eq] at sound
    exact allowed.2.2.2 p inside sound

theorem exclusive_backing_no_read {Lease : Type} {scope : BorrowScope} (map : BackingMap Lease scope)
    {events : List (EnvironmentBackingEvent Lease)} {report : AccessEvent}
    (reported : map.reports events report) (allowed : EnvironmentAccess scope report)
    (event : EnvironmentBackingEvent Lease) (present : event ∈ events)
    (p : Val) (inside : scope.exclusive p) (resolved : map.resolve p = some event.location) :
    event.kind ≠ .read := by
  intro kind
  have sound := reported event present p (Or.inr inside) resolved
  rw [kind] at sound
  exact allowed.1 p inside sound

/-- Physical scheduler events are projected to every borrowed alias. At each
environment boundary the projection uses the same backing identities and
permissions through the end of the call. -/
structure BackedSchedule {Lease : Type} {scope : BorrowScope}
    (map : BackingMap Lease scope) (env : Environment scope) where
  events : Nat → Cpu → List (EnvironmentBackingEvent Lease)
  sound : ∀ tick s, map.reports (events tick s) (env.event tick s)

theorem BackedSchedule.preserves_lifetime {Lease : Type} {scope : BorrowScope}
    {map : BackingMap Lease scope} {env : Environment scope} (schedule : BackedSchedule map env)
    (tick : Nat) (s : Cpu) (e : EnvironmentBackingEvent Lease) (member : e ∈ schedule.events tick s)
    (p : Val) (borrowed : scope.protected p) (resolve : map.resolve p = some e.location) :
    e.kind ≠ .release ∧ e.kind ≠ .protectionChange :=
  protected_backing_lifetime map (schedule.sound tick s) (env.permitted tick s) e member p borrowed resolve

theorem BackedSchedule.no_backing_race {Lease : Type} {scope : BorrowScope}
    {map : BackingMap Lease scope} {env : Environment scope} (schedule : BackedSchedule map env)
    (tick : Nat) (s : Cpu) (e : EnvironmentBackingEvent Lease) (member : e ∈ schedule.events tick s)
    (p : Val) (resolve : map.resolve p = some e.location) (localEvent : AccessEvent)
    (allowed : CallAccess scope localEvent) :
    (localEvent.reads p → e.kind ≠ .write) ∧
      (localEvent.writes p → e.kind ≠ .write ∧ e.kind ≠ .read) := by
  have external := env.permitted tick s
  have noWrite (owned : scope.protected p) (kind : e.kind = .write) : False := by
    have hit := schedule.sound tick s e member p owned resolve
    rw [kind] at hit
    exact external.2.1 p owned hit
  exact ⟨fun reads => noWrite (allowed.1 p reads),
    fun writes => ⟨noWrite (Or.inr (allowed.2.1 p writes)),
      exclusive_backing_no_read map (schedule.sound tick s) external e member p (allowed.2.1 p writes) resolve⟩⟩

theorem ObservedExecution.erase {base s trace out} (run : ObservedExecution base s trace out) :
    Execution base s (trace.map (fun e => (e.1,e.2.1))) out := by
  induction run with
  | nil => exact .nil _
  | cons fetch steps obs rest ih => exact .cons fetch steps ih

theorem ObservedExecution.unique {base s x y a b}
    (left : ObservedExecution base s x a) (right : ObservedExecution base s y b)
    (length : x.length = y.length) : x = y ∧ a = b := by
  induction left generalizing y b with
  | nil =>
    cases right with
    | nil => exact ⟨rfl,rfl⟩
    | cons => simp at length
  | cons fetched executed observed rest ih =>
    cases right with
    | nil => simp at length
    | cons f e o next =>
      obtain rfl := Option.some.inj (fetched.symm.trans f)
      obtain rfl := Option.some.inj (executed.symm.trans e)
      obtain rfl := Option.some.inj (observed.symm.trans o)
      obtain ⟨rfl,rfl⟩ := ih next (by simpa using length)
      exact ⟨rfl,rfl⟩

private theorem dropLast_map {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).dropLast = xs.dropLast.map f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y ys =>
      change f x :: ((y::ys).map f).dropLast = f x :: (y::ys).dropLast.map f
      rw [ih]

structure NativeSerial (base : Val) (s out : Cpu) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (events : List Event) : Prop where
  result : CallResult s out message
  execution : ObservedExecution base s events out
  returned : returnAt base (callSteps message.bytes.size) s = some out
  publicTrace : events = callEvents base s message
  steps : events.length = callSteps message.bytes.size
  last : events.getLast?.map (fun e => isReturn e.2.1) = some true
  first : ∀ e ∈ events.dropLast, isReturn e.2.1 = false
  owned : ∀ e ∈ events, CallAccess (callBorrow base s extent) (ReportedAccess e.1 e.2.1 e.2.2)
  data : ∀ e ∈ events, ∀ a ∈ e.2.2, ∀ p, DataByte a p → canonical p = true ∧
    if a.write then authority.writable p else authority.readable p
  fetch : ∀ p, fetchByte events p → authority.executable p ∧ canonical p = true
  stack : ∀ p ∈ stackTrace (events.map (fun e => e.2.1)) s,
    ∃ used ≤ 504, p = s.regs.get .rsp - BitVec.ofNat 64 used
  platform : platformState out = platformState s

theorem sha256_native_serial {base s message extent authority} (entry : PermissionEntry base s message extent authority) :
    ∃ out, NativeSerial base s out message extent authority (callEvents base s message) := by
  obtain ⟨out,returned,result,actual⟩ := sha256_observed base s message extent entry.toCallerEntry
  obtain ⟨retTrace,retRun,retLength,last,first⟩ := returnAt_execution returned
  obtain ⟨retObs,retActual,retProjection,_⟩ := retRun.observe
  have len := callEvents_length base s message
  have otherLen := (congrArg List.length retProjection).trans retLength
  simp only [List.length_map] at otherLen
  obtain ⟨rfl,_⟩ := actual.unique retActual (len.trans otherLen.symm)
  rw [← retProjection] at last first
  have checked := sha256_data_within entry.toCallerEntry
  have owned := observed_call_access actual extent entry.imageValid (checked.mono (fun _ => callRead_protected) (fun _ => id))
  obtain ⟨_,_,boundRun,boundResult,boundCount,_,stack⟩ := sha256_stack_bound entry.toCallerEntry
  obtain ⟨boundObs,boundActual,boundProjection,_⟩ := boundRun.observe
  have boundLen := (congrArg List.length boundProjection).trans boundCount
  simp only [List.length_map] at boundLen
  obtain ⟨rfl,_⟩ := actual.unique boundActual (len.trans boundLen.symm)
  refine ⟨out,⟨result,actual,returned,rfl,len,?_,?_,owned,?_,?_,?_,actual.erase.platform⟩⟩
  · simpa only [List.getLast?_map, Option.map_map, Function.comp_def] using last
  · intro e h
    apply first (e.1,e.2.1)
    rw [dropLast_map]
    exact List.mem_map_of_mem h
  · intro e he a ha p touched
    have right := checked e he a ha p touched
    by_cases dir : a.write = true
    · simp only [dir,if_true] at right ⊢
      exact ⟨entry.canonicalData p (Or.inr right),entry.writable p right⟩
    · simp only [dir] at right ⊢
      exact ⟨entry.canonicalData p (callRead_protected right),entry.readable p right⟩
  · rintro p ⟨e,member,j,hj,rfl⟩
    have size : codeEnd ≤ image.size := by decide +kernel
    exact actual.erase.fetch_authorized authority (fun k h => ⟨entry.executable k h,
      entry.imageCanonical _ (Crypto.ARM64.Imported.caller_region_contains_offset _ entry.imageValid k
        (Nat.lt_of_lt_of_le h size))⟩) (e.1,e.2.1) (List.mem_map_of_mem member) j hj
  · rw [← boundProjection, List.map_map] at stack
    exact stack

theorem same_call_events {base left right l r} (same : SameContext left right l r) :
    callEvents base left l = callEvents base right r := by
  have padding : Crypto.ARM64.Imported.paddingBlockCount l.bytes = Crypto.ARM64.Imported.paddingBlockCount r.bytes := by
    unfold Crypto.ARM64.Imported.paddingBlockCount
    rw [same.count]
  simp only [callEvents, frameBase, bodyEvents, preparedCallEvents, same.stack, same.input,
    same.output, same.offset, same.count, padding]

end Crypto.X86_64
