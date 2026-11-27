import Proofs.HMACSHA256.X86KeyTrace
import Proofs.HMACSHA256.X86Outer
import Proofs.HMACSHA256.X86PadTrace

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (DataAccess)

set_option maxRecDepth 8192
set_option maxHeartbeats 3600000
set_option linter.unusedSimpArgs false

def FinishCodeRights (base : Val) (authority : Authority) : Prop :=
  ∀ i < finish.image.size, canonical (routineAddress base finish + BitVec.ofNat 64 i) = true ∧
    authority.executable (routineAddress base finish + BitVec.ofNat 64 i)

theorem finish_inner_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0x11#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : FinishCodeRights base authority)
    (write : ∀ i < 8, canonical (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i) = true ∧
      authority.writable (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i)) :
    RangeReady finish base authority 0x11 s ((decodeRange finish 0x11 4).getD []) := by
  rw [finish_inner_call_decoded, Option.getD_some]
  refine range_ready_of_events finish_inner_call_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, lea_stack,
      live, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, lea_stack, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp only [rangeEvents, move_reg, lea_stack, live, localAccesses, dataAccesses, operandAccess,
      List.append_nil, List.nil_append, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false,
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rbx ≠ .rsp),
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rbp ≠ .rsp)] at events
    rcases events with ⟨e | e | e | e, report⟩ <;> rw [e] at report
    · exact False.elim (List.not_mem_nil report)
    · exact False.elim (List.not_mem_nil report)
    · exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ write p hit

theorem finish_header_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0x21#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : FinishCodeRights base authority)
    (write : ∀ i < 24, canonical (s.regs.get .rsp + BitVec.ofNat 64 i) = true ∧
      authority.writable (s.regs.get .rsp + BitVec.ofNat 64 i)) :
    RangeReady finish base authority 0x21 s ((decodeRange finish 0x21 3).getD []) := by
  rw [finish_header_decoded, Option.getD_some]
  refine range_ready_of_events finish_header_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, store_header_word,
      live, pc, BitVec.add_assoc]
  · simp [rangeStates, store_header_word, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp only [rangeEvents, store_header_word, live, localAccesses, dataAccesses, operandAccess,
      Ea.addr, Ea.offset, Size.bytes, show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero,
      List.append_nil, List.nil_append, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at events
    have word (offset : Nat) (fits : offset + 8 ≤ 24) (report : a = ⟨true,
        s.regs.get .rsp + BitVec.ofNat 64 offset, 8⟩) : canonical p = true ∧
        if a.write then authority.writable p else authority.readable p := by
      subst a
      refine word_rights authority true _ ?_ p hit
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact write _ (by omega)
    rcases events with ⟨h | h | h, report⟩ <;> rw [h] at report
    · apply word 0 (by decide)
      simp only [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact List.mem_singleton.mp report
    · exact word 8 (by decide) (List.mem_singleton.mp report)
    · exact word 16 (by decide) (List.mem_singleton.mp report)

theorem finish_mask_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0x3b#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : FinishCodeRights base authority) :
    RangeReady finish base authority 0x3b s ((decodeRange finish 0x3b 1).getD []) := by
  rw [opad_mask_decoded, Option.getD_some]
  refine range_ready_of_events opad_mask_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp [rangeStates, rangeAddresses, pc]
  · simp [rangeStates, direction, live]
  · simp [rangeEvents, localAccesses, dataAccesses, operandAccess]

theorem finish_outer_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0xa4#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : FinishCodeRights base authority)
    (write : ∀ i < 8, canonical (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i) = true ∧
      authority.writable (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i)) :
    RangeReady finish base authority 0xa4 s ((decodeRange finish 0xa4 3).getD []) := by
  rw [finish_outer_call_decoded, Option.getD_some]
  refine range_ready_of_events finish_outer_call_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, live, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp only [rangeEvents, move_reg, live, localAccesses, dataAccesses, operandAccess,
      List.append_nil, List.nil_append, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false,
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rdi ≠ .rsp)] at events
    rcases events with ⟨h | h | h, report⟩ <;> rw [h] at report
    · exact False.elim (List.not_mem_nil report)
    · exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ write p hit

def finishInnerSetupEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base finish + 0x11#64) ((decodeRange finish 0x11 4).getD [])
    [[], [], [], [⟨true, sp - 8#64, 8⟩]]

def finishHeaderEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base finish + 0x21#64) ((decodeRange finish 0x21 3).getD [])
    [[⟨true, sp, 8⟩], [⟨true, sp + 8#64, 8⟩], [⟨true, sp + 16#64, 8⟩]]

def finishMaskEvents (base : Val) : List Event :=
  staticEvents (routineAddress base finish + 0x3b#64) ((decodeRange finish 0x3b 1).getD []) [[]]

def finishOuterSetupEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base finish + 0xa4#64) ((decodeRange finish 0xa4 3).getD [])
    [[], [], [⟨true, sp - 8#64, 8⟩]]

theorem finish_inner_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0x11#64) (live : s.ms = none) :
    rangeEvents ((decodeRange finish 0x11 4).getD []) s = finishInnerSetupEvents base (s.regs.get .rsp) := by
  simp only [finishInnerSetupEvents, finish_inner_call_decoded, Option.getD_some, staticEvents, rangeEvents,
    rangeAddresses, move_reg, lea_stack, live, localAccesses, dataAccesses, operandAccess,
    List.append_nil, List.nil_append, pc,
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rbx ≠ .rsp),
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rbp ≠ .rsp)]
  rfl

theorem finish_header_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0x21#64) (live : s.ms = none) :
    rangeEvents ((decodeRange finish 0x21 3).getD []) s = finishHeaderEvents base (s.regs.get .rsp) := by
  simp only [finishHeaderEvents, finish_header_decoded, Option.getD_some, staticEvents, rangeEvents,
    rangeAddresses, store_header_word, live, localAccesses, dataAccesses, operandAccess,
    Ea.addr, Ea.offset, Size.bytes, show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero,
    List.append_nil, List.nil_append, pc]
  rfl

theorem finish_mask_events {base : Val} (s : Cpu) (pc : s.rip = routineAddress base finish + 0x3b#64) :
    rangeEvents ((decodeRange finish 0x3b 1).getD []) s = finishMaskEvents base := by
  simp [finishMaskEvents, opad_mask_decoded, staticEvents, rangeEvents, rangeAddresses,
    localAccesses, dataAccesses, operandAccess, pc]

theorem finish_outer_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base finish + 0xa4#64) (live : s.ms = none) :
    rangeEvents ((decodeRange finish 0xa4 3).getD []) s = finishOuterSetupEvents base (s.regs.get .rsp) := by
  simp only [finishOuterSetupEvents, finish_outer_call_decoded, Option.getD_some, staticEvents, rangeEvents,
    rangeAddresses, move_reg, live, localAccesses, dataAccesses, operandAccess,
    List.append_nil, List.nil_append, pc,
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rdi ≠ .rsp)]
  rfl

/-- The three SHA-256 ABI arguments that determine the address trace. -/
def shaTraceContext (s : Cpu) (sp input output : Val) : Cpu :=
  { s with regs := ((s.regs.set .rsp sp).set .rdi input).set .rsi output }

theorem sha_trace_context (s : Cpu) (sp input output : Val) :
    (shaTraceContext s sp input output).regs.get .rsp = sp ∧
    (shaTraceContext s sp input output).regs.get .rdi = input ∧
    (shaTraceContext s sp input output).regs.get .rsi = output := by
  simp (config := { decide := true }) only [shaTraceContext, Regs.get_set_same, Regs.get_set_ne, and_true]

theorem call_events_same_arguments {base : Val} {s t : Cpu} {a b : Crypto.Reference.ByteList}
    (sp : s.regs.get .rsp = t.regs.get .rsp) (input : s.regs.get .rdi = t.regs.get .rdi)
    (output : s.regs.get .rsi = t.regs.get .rsi) (offset : a.offset = b.offset)
    (count : a.bytes.size = b.bytes.size) :
    callEvents base s a = callEvents base t b := by
  have padding : Crypto.ARM64.Imported.paddingBlockCount a.bytes =
      Crypto.ARM64.Imported.paddingBlockCount b.bytes := by
    unfold Crypto.ARM64.Imported.paddingBlockCount
    rw [count]
  simp only [callEvents, frameBase, bodyEvents, preparedCallEvents, sp, input, output, offset, count, padding]

end Crypto.HMACSHA256.X86_64
