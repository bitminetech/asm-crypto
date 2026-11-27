import Proofs.HMACSHA256.ARM64Ranges

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

set_option maxRecDepth 8192
set_option maxHeartbeats 2800000

inductive LinkedImage (base : Addr) : Arm64.Program → Prop where
  | hash : LinkedImage base (program (shaAddress base))
  | hmac {r : Routine} (reachable : r = entry ∨ r = key ∨ r = finish) :
      LinkedImage base (programAt r (routineAddress base r))

/-- One execution relation for the HMAC instructions and the individually
fetched instructions in its linked SHA-256 calls. -/
inductive NativeExecution (base : Addr) :
    Arm64.State → List InstructionObservation → Arm64.State → Prop where
  | nil (s : Arm64.State) (running : s.status = .Running) : NativeExecution base s [] s
  | cons {p : Arm64.Program} {i : Arm64.Instr} {s out : Arm64.State} {rest : List InstructionObservation}
      (image : LinkedImage base p) (allowed : hmacLocal i = true) (running : s.status = .Running)
      (fetched : p.fetchMem s.mem s.pc = some i)
      (tail : NativeExecution base (Arm64.execInstWithSvc Arm64.noSyscalls i s) rest out) :
      NativeExecution base s (instructionObservation i s :: rest) out

theorem NativeExecution.running {base : Addr} {s out : Arm64.State} {obs : List InstructionObservation}
    (run : NativeExecution base s obs out) : s.status = .Running := by
  cases run
  case nil status => exact status
  case cons _ _ status _ _ => exact status

theorem NativeExecution.append {base : Addr} {s mid out : Arm64.State} {xs ys : List InstructionObservation}
    (one : NativeExecution base s xs mid) (two : NativeExecution base mid ys out) :
    NativeExecution base s (xs ++ ys) out := by
  induction one with
  | nil => exact two
  | cons image allowed running fetched _ ih => exact .cons image allowed running fetched (ih two)

private theorem sha_words_native (base : Addr) (words : List (BitVec 32)) (s out : Arm64.State)
    (obs : List InstructionObservation)
    (observed : runWordsObserved words s = some (out, obs)) (running : out.status = .Running)
    (loaded : (program (shaAddress base)).CodeLoaded s.mem) (permitted : PermittedWords words)
    (path : StaticPath (shaAddress base) words s) : NativeExecution base s obs out := by
  induction words generalizing s obs with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj observed)
    exact .nil _ running
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWordsObserved, decoded] at observed
    | some i =>
      let next := Arm64.execInstWithSvc Arm64.noSyscalls i s
      cases tail : runWordsObserved rest next with
      | none =>
        have : runWordsObserved (word :: rest) s = none := by
          simp only [runWordsObserved, decoded, Bind.bind, Option.bind]
          change (runWordsObserved rest next).bind _ = none
          rw [tail]
          rfl
        rw [this] at observed
        cases observed
      | some named =>
        obtain ⟨after, steps⟩ := named
        have combined : runWordsObserved (word :: rest) s =
            some (after, instructionObservation i s :: steps) := by
          simp only [runWordsObserved, decoded, Bind.bind, Option.bind]
          change (runWordsObserved rest next).bind _ = _
          rw [tail]
          rfl
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (combined.symm.trans observed))
        simp only [StaticPath, decoded] at path
        have sound := permitted _ List.mem_cons_self i decoded
        have done := fetch_observed_raw_execution rest next after steps tail
        have nextRunning := runWords_running_before rest next after permitted.tail done running
        exact .cons .hash
          (by simp [hmacLocal, sound]) (permitted_running_before i sound s nextRunning)
          (loaded_fetch_of_fetch loaded path.1)
          (ih next steps tail (permitted_codeLoaded i sound s loaded) permitted.tail path.2)

theorem ShaCallResult.native_execution {base : Addr} {s out : Arm64.State}
    {message : Crypto.Reference.ByteList} {obs : List InstructionObservation}
    (call : ShaCallResult (shaAddress base) s out message obs) :
    NativeExecution base s obs out := by
  obtain ⟨extent, caller⟩ := call.caller
  have input := caller_entry_inputs (shaAddress base) s message extent caller
  have done := fetch_observed_raw_execution _ _ _ _ call.trace
  exact sha_words_native base _ s out obs call.trace call.running caller.loaded (whole_call_permitted _)
    (whole_call_staticPath (shaAddress base) s message.bytes input out done call.running)

theorem LinkedExecution.native_execution {base : Addr} {s out : Arm64.State} {obs : List InstructionObservation}
    (run : LinkedExecution base s obs out) (running : out.status = .Running) : NativeExecution base s obs out := by
  induction run with
  | nil => exact .nil _ running
  | localStep body allowed live fetch _ ih => exact .cons (.hmac body) allowed live fetch (ih running)
  | shaCall hash _ ih => exact hash.native_execution.append (ih running)

theorem hmac_permissions_preserved (i : Arm64.Instr) (s : Arm64.State)
    (allowed : hmacLocal i = true) (p : Addr) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem.perm p = s.mem.perm p := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | extra
  · exact permitted_preserves_permissions i common s p
  · cases i <;> simp only [hmacExtra, Bool.false_eq_true] at extra
    all_goals rfl

theorem hmac_data_allowed (i : Arm64.Instr) (s : Arm64.State) (allowed : hmacLocal i = true)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running) :
    ∀ a ∈ dataAccesses i s, a.Allowed s.mem := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | extra
  · exact permitted_accesses_allowed i s common running
  · cases i <;> simp only [hmacExtra, Bool.false_eq_true] at extra
    all_goals simp [dataAccesses]

end Crypto.HMACSHA256.ARM64
