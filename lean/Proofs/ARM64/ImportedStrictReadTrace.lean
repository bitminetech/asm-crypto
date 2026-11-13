import Proofs.ARM64.ImportedConfidentialCall
import Proofs.ARM64.ImportedStrictReadCall

/-!
Bytewise confinement for actual SHA-256 instruction observations. The generic
leaf theorem derives every transient data byte's footprint from conservative
permission bounds, ordinary-instruction permission preservation, successful
native execution and its final running state. It introduces no recovery path.

The paired-call rule transfers an independently constructed restricted-view
execution's footprint to the actual full-RX view through the existing semantic
public-control/address theorem. Trace equality is proved internally; it is not
an entry assumption. Fetch, physical alias, loader and concurrency correspondence
remain separate obligations.
-/

namespace Crypto.ARM64.Imported

/-- Bytewise data footprint; fetch permission is a separate obligation. -/
def DataAccess.WithinFootprint (reads writes : BitVec 64 → Prop) (access : DataAccess) : Prop :=
  ∀ i, i < access.bytes → if access.write then writes (access.address + BitVec.ofNat 64 i)
    else reads (access.address + BitVec.ofNat 64 i)

def ObservedDataFootprint (reads writes : BitVec 64 → Prop)
    (observations : List InstructionObservation) : Prop :=
  ∀ observation ∈ observations, ∀ access ∈ observation.accesses, access.WithinFootprint reads writes

theorem allowed_within_footprint (reads writes : BitVec 64 → Prop)
    (permissions : BitVec 64 → Option Arm64.Perm) (m : Arm64.Memory)
    (samePermissions : ∀ p, m.perm p = permissions p)
    (readBound : ∀ p, (permissions p).r = true → reads p)
    (writeBound : ∀ p, ((permissions p).w && !(permissions p).x) = true → writes p)
    (access : DataAccess) (allowed : access.Allowed m) : access.WithinFootprint reads writes := by
  intro i hi
  unfold DataAccess.Allowed at allowed
  cases write : access.write
  · simp only [write, Bool.false_eq_true, ↓reduceIte] at allowed ⊢
    have pair : m.allPerm (·.r) access.address access.bytes = true ∧
        m.allNoLazyFree access.address access.bytes = true := by
      simpa only [Arm64.Memory.canRead, Bool.and_eq_true] using allowed
    have bit := (allPerm_true_iff m (·.r) access.address access.bytes).mp pair.1 i hi
    rw [samePermissions] at bit
    exact readBound _ bit
  · simp only [write, ↓reduceIte] at allowed ⊢
    have bit := (allPerm_true_iff m (fun p => p.w && !p.x) access.address access.bytes).mp allowed i hi
    rw [samePermissions] at bit
    exact writeBound _ bit

theorem runWords_observed_footprint (reads writes : BitVec 64 → Prop)
    (permissions : BitVec 64 → Option Arm64.Perm)
    (readBound : ∀ p, (permissions p).r = true → reads p)
    (writeBound : ∀ p, ((permissions p).w && !(permissions p).x) = true → writes p)
    (words : List (BitVec 32)) (current out : Arm64.State)
    (samePermissions : ∀ p, current.mem.perm p = permissions p)
    (permitted : PermittedWords words) (executed : runWords words current = some out)
    (running : out.status = .Running) :
    ∃ observations, runWordsObserved words current = some (out, observations) ∧
      ObservedDataFootprint reads writes observations := by
  induction words generalizing current with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    refine ⟨[], rfl, ?_⟩
    simp [ObservedDataFootprint]
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction current) = some out at executed
      have instructionAllowed := permitted word (by simp) instruction decoded
      have nextRunning := runWords_running_before rest _ out permitted.tail executed running
      have guards := permitted_accesses_allowed instruction current instructionAllowed nextRunning
      have nextPermissions (p : BitVec 64) :
          (Arm64.execInstWithSvc Arm64.noSyscalls instruction current).mem.perm p = permissions p :=
        (permitted_preserves_permissions instruction instructionAllowed current p).trans (samePermissions p)
      obtain ⟨observations, observed, confined⟩ := ih _ nextPermissions permitted.tail executed
      refine ⟨instructionObservation instruction current :: observations, ?_, ?_⟩
      · simp only [runWordsObserved, decoded, Bind.bind, Option.bind, observed, pure, Pure.pure]
      · intro observation member access accessMember
        rcases List.mem_cons.mp member with same | later
        · subst observation
          exact allowed_within_footprint reads writes permissions current.mem samePermissions
            readBound writeBound access (guards access accessMember)
        · exact confined observation later access accessMember

/-- Transfer a proven byte footprint between two actual native call executions.
The permission-restricted auxiliary execution is supplied by an internal proof,
not a premise imposed on an external SHA caller. Equality of traces is derived. -/
theorem native_paired_call_footprint (reads writes : BitVec 64 → Prop)
    (count : BitVec 64) (base : BitVec 64) (left right : Arm64.State)
    (leftOut rightOut : Arm64.State) (leftObs rightObs : List InstructionObservation)
    (leftPC : left.pc = base) (rightPC : right.pc = base)
    (publicInputs : SamePublicCall left right)
    (countValues : left.mem.read64 (left.readReg64 .x0 + 16#64) =
      right.mem.read64 (right.readReg64 .x0 + 16#64))
    (leftOffsetRead : left.mem.canRead (left.readReg64 .x0 + 8#64) 8 = true)
    (leftCountRead : left.mem.canRead (left.readReg64 .x0 + 16#64) 8 = true)
    (rightOffsetRead : right.mem.canRead (right.readReg64 .x0 + 8#64) 8 = true)
    (rightCountRead : right.mem.canRead (right.readReg64 .x0 + 16#64) 8 = true)
    (leftPath : StaticPath base (wholeCallCode count) left)
    (rightPath : StaticPath base (wholeCallCode count) right)
    (leftObserved : runWordsObserved (wholeCallCode count) left = some (leftOut, leftObs))
    (rightObserved : runWordsObserved (wholeCallCode count) right = some (rightOut, rightObs))
    (leftRunning : leftOut.status = .Running) (rightRunning : rightOut.status = .Running)
    (leftFootprint : ObservedDataFootprint reads writes leftObs) :
    ObservedDataFootprint reads writes rightObs := by
  have same := (native_paired_call count base left right leftOut rightOut leftObs rightObs
    leftPC rightPC publicInputs countValues leftOffsetRead leftCountRead rightOffsetRead rightCountRead
    leftPath rightPath leftObserved rightObserved leftRunning rightRunning).1
  rw [← same]
  exact leftFootprint

theorem strict_runWords_observed_footprint (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (words : List (BitVec 32)) (out : Arm64.State)
    (permitted : PermittedWords words)
    (executed : runWords words (strictState base s message) = some out)
    (running : out.status = .Running) :
    ∃ observations, runWordsObserved words (strictState base s message) = some (out, observations) ∧
      ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) observations := by
  exact runWords_observed_footprint (strictReadFootprint base s message) (permissionWriteFootprint s)
    (strictPermission base s message) (strictPermission_read base s message)
    (strictPermission_write base s message) words (strictState base s message) out
    (strictMemory_perm base s message) permitted executed running

/-- Internal bridge from a constructed strict execution to observations of the
actual logical full-RX call. Strict success/path are later discharged from the
unchanged typed caller inputs, rather than becoming new caller assumptions. -/
theorem logical_call_strict_footprint (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (strictOut actualOut : Arm64.State) (actualObs : List InstructionObservation)
    (strictExecuted : runWords (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
      (strictState base s message) = some strictOut)
    (strictRunning : strictOut.status = .Running)
    (strictPath : StaticPath base (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
      (strictState base s message))
    (actualObserved : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
      (logicalState base s message) = some (actualOut, actualObs)) :
    ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) actualObs := by
  have actualEntry := permission_view_inputs base s message extent authority entry
  have actualExecuted := fetch_observed_raw_execution _ _ _ _ actualObserved
  have actualRunning := observed_call_running base _ message.bytes actualEntry actualOut actualObs actualObserved
  have actualPath := whole_call_staticPath base _ message.bytes actualEntry actualOut actualExecuted actualRunning
  obtain ⟨strictObs, strictObserved, strictFootprint⟩ := strict_runWords_observed_footprint
    base s message _ strictOut (whole_call_permitted _) strictExecuted strictRunning
  have publicInputs : SamePublicCall (strictState base s message) (logicalState base s message) := by
    refine ⟨?_, ?_, rfl, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · change (strictMemory base s message).read64 (s.readReg64 .x0 + 8#64) =
        (logicalMemory base s message).read64 (s.readReg64 .x0 + 8#64)
      rw [strictMemory_read64, logicalMemory_read64]
  have countValues : (strictState base s message).mem.read64 ((strictState base s message).readReg64 .x0 + 16#64) =
      (logicalState base s message).mem.read64 ((logicalState base s message).readReg64 .x0 + 16#64) := by
    change (strictMemory base s message).read64 (s.readReg64 .x0 + 16#64) =
      (logicalMemory base s message).read64 (s.readReg64 .x0 + 16#64)
    rw [strictMemory_read64, logicalMemory_read64]
  exact native_paired_call_footprint (strictReadFootprint base s message) (permissionWriteFootprint s)
    (BitVec.ofNat 64 message.bytes.size) base (strictState base s message) (logicalState base s message)
    strictOut actualOut strictObs actualObs entry.pc entry.pc publicInputs countValues
    (strict_header_read base s message extent authority entry 8 8 (by decide))
    (strict_header_read base s message extent authority entry 16 8 (by decide))
    actualEntry.offsetRead actualEntry.countRead strictPath actualPath strictObserved actualObserved
    strictRunning actualRunning strictFootprint

/-- A data read not serving an input-header, used-payload or private-stack
role lies in the recorded K/H pool; instruction bytes are not relabelled as
constant data. Legitimate shared input/image aliases retain their input role. -/
theorem observed_strict_read_pool (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (observations : List InstructionObservation)
    (confined : ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) observations)
    (observation : InstructionObservation) (member : observation ∈ observations)
    (access : DataAccess) (present : access ∈ observation.accesses) (reading : access.write = false)
    (i : Nat) (bound : i < access.bytes)
    (notHeader : ¬(callerHeader s).Contains (access.address + BitVec.ofNat 64 i))
    (notPayload : ¬(callerPayload s message).Contains (access.address + BitVec.ofNat 64 i))
    (notStack : ¬(callerStack s).Contains (access.address + BitVec.ofNat 64 i)) :
    (callerConstantPool base).Contains (access.address + BitVec.ofNat 64 i) := by
  have inside := confined observation member access present i bound
  simp only [reading, Bool.false_eq_true, ↓reduceIte] at inside
  exact strict_image_data_only_pool base s message _ inside notHeader notPayload notStack

/-- Every actual full-RX observation of a valid typed call satisfies the strict
constant-data footprint. The restricted successful execution and its path are
constructed internally from the same unchanged caller inputs. -/
theorem sha256_strict_read_footprint (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority)
    (out : Arm64.State) (observations : List InstructionObservation)
    (observed : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size))
      (logicalState base s message) = some (out, observations)) :
    ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) observations := by
  obtain ⟨strictOut, strictObs, strictResult⟩ := sha256_strict_read_call base s message extent authority entry
  exact logical_call_strict_footprint base s message extent authority entry strictOut out observations
    strictResult.executed strictResult.running strictResult.path observed

/-- The bounded fetched safe-call result together with the tighter data-read
certificate, with only the established typed caller conditions as entry. -/
theorem sha256_logical_safe_strict_reads (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Crypto.Baseline.Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    ∃ out observations, LogicalCallResult base s message authority out observations ∧
      ObservedDataFootprint (strictReadFootprint base s message) (permissionWriteFootprint s) observations := by
  obtain ⟨out, observations, result⟩ := sha256_logical_safe base s message extent authority entry
  exact ⟨out, observations, result,
    sha256_strict_read_footprint base s message extent authority entry out observations result.observed⟩

end Crypto.ARM64.Imported
