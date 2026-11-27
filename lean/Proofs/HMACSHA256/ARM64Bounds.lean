import Proofs.HMACSHA256.ARM64EntryPublic
import Proofs.ARM64.ImportedCallBounds

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported Crypto.Reference

def shaStepBound (length : Nat) : Nat := 512 + 4000 * ((length + 8) / 64 + 1)
def keyStepBound (length : Nat) : Nat := 40 + 6 * (length / 8) + 5 * (length % 8) + shaStepBound length
def finishStepBound (length : Nat) : Nat := 47 + shaStepBound length + shaStepBound 96
def entryStepBound (keyLength messageLength : Nat) : Nat :=
  70 + 6 * (messageLength / 8) + 5 * (messageLength % 8) + keyStepBound keyLength + finishStepBound (64 + messageLength)

private theorem observed_word_count {words : List (BitVec 32)} {s out : Arm64.State}
    {events : List InstructionObservation} (run : runWordsObserved words s = some (out, events)) :
    events.length = words.length := by
  induction words generalizing s out events with
  | nil =>
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj run)
    rfl
  | cons word words ih =>
    unfold runWordsObserved at run
    obtain ⟨i, _, followed⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨⟨mid, tail⟩, sub, finished⟩ := Option.bind_eq_some_iff.mp followed
    obtain ⟨_, eq⟩ := Prod.mk.inj (Option.some.inj finished)
    rw [← eq, List.length_cons, List.length_cons, ih sub]

theorem ShaCallResult.step_bound {base : Addr} {s out : Arm64.State} {input : ByteList} {events}
    (run : ShaCallResult base s out input events) : events.length ≤ shaStepBound input.bytes.size := by
  obtain ⟨_, entry⟩ := run.caller
  have n : input.bytes.size < 2 ^ 64 := by have := entry.length; omega
  rw [observed_word_count run.trace]
  have count := whole_call_code_bound (BitVec.ofNat 64 input.bytes.size)
  simpa only [shaStepBound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n] using count

private theorem copyIterationEvents_length (wide : Bool) (pc sp src dst : Addr) (n : Nat) :
    (copyIterationEvents wide pc sp src dst n).length = (copyGuardCount wide + 4) * n := by
  induction n with
  | zero => simp [copyIterationEvents]
  | succ n ih =>
    simp only [copyIterationEvents, List.length_append, ih, Nat.mul_succ]
    have len (src dst : Addr) : (copyCycleEvents wide true pc sp src dst).length = copyGuardCount wide + 4 := by
      cases wide <;> rfl
    rw [len]

private theorem copyPayloadEvents_length (pc sp src dst : Addr) (n : Nat) :
    (copyPayloadEvents pc sp src dst n).length = 3 + 6 * (n / 8) + 5 * (n % 8) := by
  simp only [copyPayloadEvents, List.length_append, copyIterationEvents_length,
    copyGuardEvents, copyGuardCount, if_true, Bool.false_eq_true, if_false, List.length_cons, List.length_nil]
  omega

private theorem rangeCount (r : Routine) (off n : Nat) (s : Arm64.State) :
    (rangeEvents r off n s).length = ((decodeRange r off n).getD []).length := by
  simp only [rangeEvents, decodedEvents_length]

theorem finish_body_step_bound {base : Addr} {s out : Arm64.State} {input : ByteList} {k0 : HmacKeyBlock}
    (body : FinishBody base (enteredState s 224#64) out input k0) :
    body.nativeTrace.length ≤ finishStepBound input.bytes.size := by
  have a := body.innerHash.step_bound
  have b := body.outerHash.step_bound
  rw [hmacOuter_length] at b
  have init : (frameEnterEvents s.pc s.sp 224#64).length = 7 := rfl
  have tail : (frameReturnEvents out.pc out.sp 224#64 (s.readReg64 .lr)).length = 7 := rfl
  have setup : ((decodeRange finish 0x1c 4).getD []).length = 4 := by decide +kernel
  have header : ((decodeRange finish 0x2c 6).getD []).length = 6 := by decide +kernel
  have mask : ((decodeRange finish 0x44 4).getD []).length = 4 := by decide +kernel
  have pad : ((decodeRange finish 0x54 16).getD []).length = 16 := by decide +kernel
  have outer : ((decodeRange finish 0x94 3).getD []).length = 3 := by decide +kernel
  simp only [FinishBody.nativeTrace, List.length_append, rangeCount, init, tail, setup, header, mask, pad, outer,
    finishStepBound]
  omega

theorem key_trace_step_bound {base : Addr} {s : Arm64.State} {input : ByteList} {events}
    (trace : KeyWholeTrace base s input events) : events.length ≤ keyStepBound input.bytes.size := by
  obtain ⟨body, path, rfl⟩ := trace
  have enter : (frameEnterEvents s.pc s.sp 96#64).length = 7 := rfl
  have clear : (keyZeroEvents base (s.sp - 96#64) (s.readReg64 .x1)).length = 4 := rfl
  have leave : (frameReturnEvents (routineAddress base key + 0x74#64) (s.sp - 96#64) 96#64
    (s.readReg64 .lr)).length = 7 := rfl
  cases path with
  | short =>
    simp only [List.length_append, enter, clear, leave, keyShortEvents, keyTestEvents, keySourceEvents, keyJumpEvents,
      List.length_cons, List.length_nil, copyPayloadEvents_length, keyStepBound]
    omega
  | long _ run _ _ _ _ =>
    have bounds := run.step_bound
    simp only [List.length_append, enter, clear, leave, keyTestEvents, keyInvokeEvents, List.length_cons,
      List.length_nil, keyStepBound]
    omega

private theorem inner_trace_step_bound {base : Addr} {s : Arm64.State} {input : ByteList} {events}
    (trace : InnerTrace base s input events) :
    events.length ≤ 35 + 6 * (input.bytes.size / 8) + 5 * (input.bytes.size % 8) := by
  have head : ((decodeRange entry 0x54 8).getD []).length = 8 := by decide +kernel
  have mask : ((decodeRange entry 0x74 5).getD []).length = 5 := by decide +kernel
  have pad : ((decodeRange entry 0x88 16).getD []).length = 16 := by decide +kernel
  have copy : ((decodeRange entry 0xc8 3).getD []).length = 3 := by decide +kernel
  simp only [trace.trace, innerEvents, List.length_append, rangeCount, copyPayloadEvents_length, head, mask, pad, copy]
  omega

theorem entry_trace_step_bound {base : Addr} {s : Arm64.State} {input message : ByteList} {capacity : Nat} {events}
    (trace : EntryTrace base s input message capacity events) :
    events.length ≤ entryStepBound input.bytes.size message.bytes.size := by
  have pre : (entryPrefixEvents base s capacity message.bytes.size).length ≤ 18 := by
    have save : (frameEnterEvents s.pc s.sp 160#64).length = 7 := rfl
    have args : (entryArgumentEvents (routineAddress base entry + 0x1c#64) (s.sp - 160#64)
      (s.readReg64 .x2) (s.readReg64 .x1)).length = 7 := rfl
    by_cases small : capacity < 96
    all_goals simp [entryPrefixEvents, entryGuardEvents, guardPairEvents, small, save, args]
  have ret : (entryReturnEvents base s).length = 7 := rfl
  cases trace with
  | small =>
    simp only [List.length_append, ret, entryStepBound]
    omega
  | full enough body =>
    have key := key_trace_step_bound body.keyTrace
    have finish := finish_body_step_bound body.finishTrace
    have inner := inner_trace_step_bound body.innerTrace
    rw [hmacInner_length] at finish
    simp only [EntrySuccessTrace.events, List.length_append, ret, entryKeyCallEvents, entryFinishCallEvents, entrySuccessEvents,
      List.length_cons, List.length_nil, entryStepBound]
    omega

end Crypto.HMACSHA256.ARM64
