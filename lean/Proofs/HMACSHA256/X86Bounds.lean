import Proofs.HMACSHA256.X86EntryConcurrency
import Proofs.X86_64.TraceLength

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def keyStepBound (length : Nat) : Nat := 40 + length + callSteps length
def finishStepBound (length : Nat) : Nat := 50 + callSteps length + callSteps 96
def entryStepBound (keyLength messageLength : Nat) : Nat :=
  100 + messageLength + keyStepBound keyLength + finishStepBound (64 + messageLength)

private theorem copy_events_length (pc source dest : Val) (length : Nat) :
    (copyEvents pc source dest length).length = length + 1 := by
  simp only [copyEvents, List.length_map, List.length_range]

theorem key_native_step_bound (base : Val) (s : Cpu) (input : ByteList) :
    (keyNativeEvents base s input).length ≤ keyStepBound input.bytes.size := by
  have front : (keyFrontEvents base s).length = 24 := by
    simp only [keyFrontEvents, keyInitEvents, keyTestEvents, key_clear_setup_decoded, key_length_decoded,
      clearKeyEvents, Option.getD_some, List.length_append, List.length_map, List.length_range]
    rfl
  have tail : (frameReturnEvents .key (routineAddress base key + 0x44#64) (s.regs.get .rsp - 56#64)).length = 8 := rfl
  have copySetup : (keyCopySetupEvents base (s.regs.get .rdi)).length = 3 := by
    simp only [keyCopySetupEvents, short_setup_decoded, Option.getD_some]
    rfl
  have jump : (keyCopyExitEvents base).length = 1 := rfl
  have invoke : (keyCallEvents base (s.regs.get .rsp - 56#64)).length = 3 := by
    simp only [keyCallEvents, long_call_decoded, Option.getD_some]
    rfl
  by_cases small : input.bytes.size ≤ 64
  · simp only [keyNativeEvents, keyBodyEvents, if_pos small, List.length_append, front, tail, copySetup, jump,
      copy_events_length, keyStepBound]
    omega
  · simp only [keyNativeEvents, keyBodyEvents, if_neg small, List.length_append, front, tail, invoke,
      callEvents_length, keyStepBound]
    omega

theorem finish_native_step_bound (base : Val) (s : Cpu) (inner : ByteList) (k0 : HmacKeyBlock) :
    (finishNativeEvents base s inner k0).length ≤ finishStepBound inner.bytes.size := by
  let sp := s.regs.get .rsp - 184#64
  have front : (frameEnterEvents .finish (routineAddress base finish) (s.regs.get .rsp)).length = 7 := rfl
  have innerSetup : (finishInnerSetupEvents base sp).length = 4 := by
    simp only [finishInnerSetupEvents, finish_inner_call_decoded, Option.getD_some]
    rfl
  have header : (finishHeaderEvents base sp).length = 3 := by
    simp only [finishHeaderEvents, finish_header_decoded, Option.getD_some]
    rfl
  have mask : (finishMaskEvents base).length = 1 := by
    simp only [finishMaskEvents, opad_mask_decoded, Option.getD_some]
    rfl
  have pad : (x86PadEvents true (routineAddress base finish + 0x45#64) (s.regs.get .rsi) sp 8).length = 24 := rfl
  have outerSetup : (finishOuterSetupEvents base sp).length = 3 := by
    simp only [finishOuterSetupEvents, finish_outer_call_decoded, Option.getD_some]
    rfl
  have ret : (frameReturnEvents .finish (routineAddress base finish + 0xaf#64) sp).length = 8 := rfl
  simp only [sp] at innerSetup header pad outerSetup ret
  simp only [finishNativeEvents, List.length_append, callEvents_length, hmacOuter_length, finishStepBound,
    front, innerSetup, header, mask, pad, outerSetup, ret]
  omega

theorem entry_native_step_bound (base : Val) (s : Cpu) (input message : ByteList) (capacity : Nat) :
    (entryNativeEvents base s input message capacity).length ≤ entryStepBound input.bytes.size message.bytes.size := by
  have front : (entryFrontEvents base s capacity).length ≤ 18 := by
    have pro : (frameEnterEvents .entry (routineAddress base entry) (s.regs.get .rsp)).length = 7 := rfl
    have args : (entryCapacityEvents base (s.regs.get .rdx) (s.regs.get .rsi)).length = 7 := by
      simp only [entryCapacityEvents, entry_capacity_decoded, Option.getD_some]
      rfl
    by_cases short : capacity < 96
    all_goals simp [entryFrontEvents, x86GuardEvents, pro, args, short]
  have ret : (frameReturnEvents .entry (routineAddress base entry + 0x100#64) (s.regs.get .rsp - 120#64)).length = 8 := rfl
  by_cases short : capacity < hmacScratchRequired message
  · simp only [entryNativeEvents, entryBodyEvents, if_pos short, List.append_nil, List.length_append, ret, entryStepBound]
    omega
  · let stack := s.regs.get .rsp - 120#64
    have invokeKey : (entryKeySetupEvents base stack).length = 3 := by
      simp only [entryKeySetupEvents, entry_key_call_decoded, Option.getD_some]
      rfl
    have header : (entryHeaderEvents base (s.regs.get .rdx) (s.regs.get .rsi)).length = 8 := by
      simp only [entryHeaderEvents, inner_header_decoded, Option.getD_some]
      rfl
    have pad : (x86PadEvents false (routineAddress base entry + 0x72#64) stack (s.regs.get .rdx) 8).length = 24 := rfl
    have copy : (entryCopySetupEvents base (s.regs.get .rsi)).length = 4 := by
      simp only [entryCopySetupEvents, copy_setup_decoded, Option.getD_some]
      rfl
    have invokeFinish : (entryFinishSetupEvents base stack).length = 4 := by
      simp only [entryFinishSetupEvents, entry_finish_call_decoded, Option.getD_some]
      rfl
    have status : (entryStatusEvents base).length = 1 := rfl
    have keyBound := key_native_step_bound base (entryKeyContext s) input
    have finishBound := finish_native_step_bound base (entryFinishContext s)
      (hmacInner message (hmacKey input) capacity) (hmacKey input)
    rw [hmacInner_length] at finishBound
    simp only [stack] at invokeKey pad invokeFinish
    simp only [entryNativeEvents, entryBodyEvents, if_neg short, List.length_append, ret,
      invokeKey, header, pad, copy, copy_events_length, invokeFinish, status, entryStepBound]
    omega

end Crypto.HMACSHA256.X86_64
