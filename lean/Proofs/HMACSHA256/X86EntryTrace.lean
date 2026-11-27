import Proofs.HMACSHA256.X86FinishTrace
import Proofs.HMACSHA256.X86EntryFrame
import Proofs.HMACSHA256.X86InnerSetup

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (DataAccess)

set_option maxRecDepth 8192
set_option maxHeartbeats 3600000
set_option linter.unusedSimpArgs false

def EntryCodeRights (base : Val) (authority : Authority) : Prop :=
  ∀ i < entry.image.size, canonical (routineAddress base entry + BitVec.ofNat 64 i) = true ∧
    authority.executable (routineAddress base entry + BitVec.ofNat 64 i)

abbrev ReadWord (authority : Authority) (addr : Val) : Prop :=
  ∀ i < 8, canonical (addr + BitVec.ofNat 64 i) = true ∧ authority.readable (addr + BitVec.ofNat 64 i)

abbrev WriteWord (authority : Authority) (addr : Val) : Prop :=
  ∀ i < 8, canonical (addr + BitVec.ofNat 64 i) = true ∧ authority.writable (addr + BitVec.ofNat 64 i)

theorem entry_capacity_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xe#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) (scratch : ReadWord authority (s.regs.get .rdx))
    (count : ReadWord authority (s.regs.get .rsi + 16#64)) :
    RangeReady entry base authority 0xe s ((decodeRange entry 0xe 7).getD []) := by
  rw [entry_capacity_decoded, Option.getD_some]
  refine range_ready_of_events entry_capacity_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, set_buffer_status,
      load_argument_word, live, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, set_buffer_status, load_argument_word, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp (config := {decide := true}) only [rangeEvents, move_reg, set_buffer_status, load_argument_word,
      live, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
      show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero,
      Regs.get_set_same, Regs.get_set_ne, if_false,
      List.nil_append, List.append_nil, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at events
    rcases events with ⟨h | h | h | h | h | h | h, report⟩ <;> rw [h] at report
    all_goals try exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨false, s.regs.get .rdx, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ scratch p hit
    · obtain rfl : a = ⟨false, s.regs.get .rsi + 16#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ count p hit

def guardFront : List Instr := [
  ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩,
  ⟨.jcc .b 0xcf, 6⟩]

def guardBack : List Instr := [
  ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩,
  ⟨.jcc .b 0xc6, 6⟩]

theorem guard_front_decoded : decodeRange entry 0x27 2 = some guardFront := by decide +kernel
theorem guard_back_decoded : decodeRange entry 0x31 2 = some guardBack := by decide +kernel

private theorem guard_sub (s : Cpu) (live : s.ms = none) :
    step ⟨.bin .sub .q (.reg .rcx) (.imm 96#64), 4⟩ s = { s with
      regs := s.regs.set .rcx (s.regs.get .rcx - 96#64)
      flags := Flags.sub .q (s.regs.get .rcx) 96#64 s.flags, rip := s.rip + 4#64 } :=
  sub_step s live

private theorem guard_front_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x27#64) (live : s.ms = none)
    (direction : s.flags.df = false) (code : EntryCodeRights base authority) :
    RangeReady entry base authority 0x27 s guardFront := by
  refine range_ready_of_events guard_front_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · unfold guardFront
    hmac_x86_known
  · simp [guardFront, rangeStates, rangeAddresses, guard_sub, sub_step, live, pc]
  · simp [guardFront, rangeStates, guard_sub, sub_step, live, direction, Flags.sub, Flags.fromResult]
  · simp [guardFront, rangeEvents, localAccesses, dataAccesses, operandAccess, guard_sub, sub_step, live]

private theorem guard_back_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x31#64) (live : s.ms = none)
    (direction : s.flags.df = false) (code : EntryCodeRights base authority) :
    RangeReady entry base authority 0x31 s guardBack := by
  refine range_ready_of_events guard_back_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · unfold guardBack
    hmac_x86_known
  · simp [guardBack, rangeStates, rangeAddresses, cmp_step, live, pc]
  · simp [guardBack, rangeStates, cmp_step, live, direction, Flags.sub, Flags.fromResult]
  · simp [guardBack, rangeEvents, localAccesses, dataAccesses, operandAccess, cmp_step, live]

def x86GuardEvents (pc : Val) (capacity : Nat) : List Event :=
  [(pc, ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩, []), (pc + 4#64, ⟨.jcc .b 0xcf, 6⟩, [])] ++
    if capacity < 96 then [] else
      [(pc + 10#64, ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩, []), (pc + 13#64, ⟨.jcc .b 0xc6, 6⟩, [])]

theorem runGuard_observes {base : Val} {authority : Authority} {s out : Cpu}
    (run : runGuard s = some out) (pc : s.rip = routineAddress base entry + 0x27#64)
    (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority)
    (loaded : entry.Loaded (routineAddress base entry) s.mem.read)
    (readonly : ∀ j < entry.image.size, ¬ authority.writable (routineAddress base entry + BitVec.ofNat 64 j)) :
    LinkedExecution base authority s (x86GuardEvents s.rip (s.regs.get .rcx).toNat) out := by
  let mid := X86.run guardFront s
  let next := X86.run guardBack mid
  have checked : runGuard s = (if mid.rip = s.rip + 10#64 then some next else some mid) := by
    obtain ⟨sub, first, cmp, second⟩ := guard_decoded
    rw [runGuard, sub, first, cmp, second]
    rfl
  have front := ready_range_executes entry base authority 0x27 s guardFront (.inl rfl) loaded readonly
    (guard_front_ready s pc live direction code)
  have frontTrace : rangeEvents guardFront s =
      [(s.rip, ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩, []), (s.rip + 4#64, ⟨.jcc .b 0xcf, 6⟩, [])] := by
    simp [rangeEvents, guardFront, guard_sub, sub_step, localAccesses, dataAccesses, operandAccess, live]
  have exitPC : canonical (s.rip + 0xd9#64) = true := by
    rw [pc, BitVec.add_assoc]
    exact (code 0x100 (by decide +kernel)).1
  let first := step ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩ s
  have firstLive : first.ms = none := by simp [first, guard_sub, sub_step, live]
  have target : canonical (first.rip + 6#64 + 0xcf#64) = true := by
    simpa [first, guard_sub, sub_step, live, BitVec.add_assoc] using exitPC
  have branch : mid = { first with rip := if (s.regs.get .rcx).toNat < 96
        then s.rip + 0xd9#64 else s.rip + 10#64 } := by
    change step ⟨.jcc .b 0xcf, 6⟩ first = _
    have update : step ⟨.jcc .b 0xcf, 6⟩ first = { first with rip :=
        if first.flags.cf then first.rip + 6#64 + 0xcf#64 else first.rip + 6#64 } :=
      branch_step first 0xcf firstLive target
    rw [update]
    simp [first, guard_sub, sub_step, live, Flags.sub, Flags.subCF, Value.uval, BitVec.add_assoc]
  have midLive : mid.ms = none := by rw [branch]; exact firstLive
  have midDF : mid.flags.df = false := by
    rw [branch]
    simp [first, guard_sub, sub_step, live, direction, Flags.sub, Flags.fromResult]
  by_cases small : (s.regs.get .rcx).toNat < 96
  · have apart : s.rip + 0xd9#64 ≠ s.rip + 10#64 :=
      fun eq => (by decide : 0xd9#64 ≠ 10#64) ((BitVec.add_right_inj s.rip).mp eq)
    have path : mid.rip ≠ s.rip + 10#64 := by rw [branch]; exact if_pos small ▸ apart
    rw [checked, if_neg path] at run
    have returned := Option.some.inj run
    rw [x86GuardEvents, if_pos small, List.append_nil, ← frontTrace, ← returned]
    exact front
  · have path : mid.rip = s.rip + 10#64 := by rw [branch]; exact if_neg small
    have nextPC : mid.rip = routineAddress base entry + 0x31#64 := by
      rw [path, pc, BitVec.add_assoc]
      rfl
    rw [checked, if_pos path] at run
    have returned := Option.some.inj run
    have back := ready_range_executes entry base authority 0x31 mid guardBack (.inl rfl)
      (front.keeps_routine entry loaded readonly) readonly (guard_back_ready mid nextPC midLive midDF code)
    have backTrace : rangeEvents guardBack mid =
        [(s.rip + 10#64, ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩, []),
          (s.rip + 13#64, ⟨.jcc .b 0xc6, 6⟩, [])] := by
      simp [rangeEvents, guardBack, cmp_step, midLive, path, BitVec.add_assoc, localAccesses,
        dataAccesses, operandAccess]
    rw [x86GuardEvents, if_neg small, ← frontTrace, ← backTrace, ← returned]
    exact front.append back

theorem entry_key_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x3a#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) (push : WriteWord authority (s.regs.get .rsp - 8#64)) :
    RangeReady entry base authority 0x3a s ((decodeRange entry 0x3a 3).getD []) := by
  rw [entry_key_call_decoded, Option.getD_some]
  refine range_ready_of_events entry_key_call_decoded (by decide +kernel) (by decide +kernel) ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, live, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp (config := {decide := true}) only [rangeEvents, move_reg, live, localAccesses, dataAccesses,
      operandAccess, List.append_nil, List.nil_append, Option.getD_some, List.mem_cons, List.not_mem_nil,
      or_false, Regs.get_set_ne] at events
    rcases events with ⟨h | h | h, report⟩ <;> rw [h] at report
    · exact False.elim (List.not_mem_nil report)
    · exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ push p hit

theorem entry_finish_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xeb#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) (push : WriteWord authority (s.regs.get .rsp - 8#64)) :
    RangeReady entry base authority 0xeb s ((decodeRange entry 0xeb 4).getD []) := by
  rw [entry_finish_call_decoded, Option.getD_some]
  refine range_ready_of_events entry_finish_call_decoded (by decide +kernel) (by decide +kernel) ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, entry_scratch_pointer,
      live, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, entry_scratch_pointer, live, direction]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp (config := {decide := true}) only [rangeEvents, move_reg, entry_scratch_pointer, live,
      localAccesses, dataAccesses, operandAccess, List.append_nil, List.nil_append, Option.getD_some,
      List.mem_cons, List.not_mem_nil, or_false, Regs.get_set_ne] at events
    rcases events with ⟨h | h | h | h, report⟩ <;> rw [h] at report
    all_goals try exact False.elim (List.not_mem_nil report)
    obtain rfl : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp report
    exact word_rights authority true _ push p hit

theorem entry_status_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xfb#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) : RangeReady entry base authority 0xfb s [⟨.mov .d (.reg .rax) (.imm 0#64), 5⟩] := by
  refine range_ready_of_events zero_status_decoded (by decide +kernel) (by decide +kernel) ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp [rangeStates, rangeAddresses, pc]
  · simp [rangeStates, live, direction]
  · simp [rangeEvents, localAccesses, dataAccesses, operandAccess]

theorem entry_header_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x45#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) (scratch : ReadWord authority (s.regs.get .r12))
    (count : ReadWord authority (s.regs.get .rbp + 16#64))
    (writeSize : WriteWord authority (s.regs.get .r12 + 8#64))
    (writeOffset : WriteWord authority (s.regs.get .r12 + 16#64))
    (writeCount : WriteWord authority (s.regs.get .r12 + 24#64)) :
    RangeReady entry base authority 0x45 s ((decodeRange entry 0x45 8).getD []) := by
  rw [inner_header_decoded, Option.getD_some]
  refine range_ready_of_events inner_header_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, load_argument_word,
      subtract_rax, store_scratch, add_rax, set_ipad, Operand.isMem, live, pc, BitVec.add_assoc]
  · simp [rangeStates, load_argument_word, subtract_rax, store_scratch, add_rax, set_ipad,
      Operand.isMem, live, direction, Flags.sub, Flags.add, Flags.fromResult]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp (config := {decide := true}) only [rangeEvents, load_argument_word, subtract_rax,
      store_scratch, add_rax, set_ipad, Operand.isMem, live,
      localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
      show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero,
      Regs.get_set_ne, List.append_nil, List.nil_append, Option.getD_some, List.mem_cons,
      List.not_mem_nil, or_false, if_false] at events
    rcases events with ⟨h | h | h | h | h | h | h | h, report⟩ <;> rw [h] at report
    all_goals try exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨false, s.regs.get .r12, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ scratch p hit
    · obtain rfl : a = ⟨true, s.regs.get .r12 + 8#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ writeSize p hit
    · obtain rfl : a = ⟨true, s.regs.get .r12 + 16#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ writeOffset p hit
    · obtain rfl : a = ⟨false, s.regs.get .rbp + 16#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ count p hit
    · obtain rfl : a = ⟨true, s.regs.get .r12 + 24#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority true _ writeCount p hit

theorem entry_copy_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xd9#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : EntryCodeRights base authority) (offset : ReadWord authority (s.regs.get .rbp + 8#64))
    (count : ReadWord authority (s.regs.get .rbp + 16#64)) :
    RangeReady entry base authority 0xd9 s ((decodeRange entry 0xd9 4).getD []) := by
  rw [copy_setup_decoded, Option.getD_some]
  refine range_ready_of_events copy_setup_decoded (by decide +kernel) (by decide +kernel) ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, load_argument_word,
      add_message_base, lea_message_dest, live, pc, BitVec.add_assoc]
  · simp [rangeStates, load_argument_word, add_message_base, lea_message_dest, live, direction, Flags.add, Flags.fromResult]
  · intro e occurred a observed p hit
    have events := And.intro occurred observed
    simp (config := {decide := true}) only [rangeEvents, load_argument_word, add_message_base, lea_message_dest,
      live, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
      show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero,
      Regs.get_set_ne, List.append_nil, List.nil_append, Option.getD_some, List.mem_cons,
      List.not_mem_nil, or_false, if_false] at events
    rcases events with ⟨h | h | h | h, report⟩ <;> rw [h] at report
    all_goals try exact False.elim (List.not_mem_nil report)
    · obtain rfl : a = ⟨false, s.regs.get .rbp + 8#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ offset p hit
    · obtain rfl : a = ⟨false, s.regs.get .rbp + 16#64, 8⟩ := List.mem_singleton.mp report
      exact word_rights authority false _ count p hit

def entryCapacityEvents (base scratch message : Val) : List Event :=
  staticEvents (routineAddress base entry + 0xe#64) ((decodeRange entry 0xe 7).getD [])
    [[], [], [], [], [], [⟨false, scratch, 8⟩], [⟨false, message + 16#64, 8⟩]]

def entryKeySetupEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base entry + 0x3a#64) ((decodeRange entry 0x3a 3).getD [])
    [[], [], [⟨true, sp - 8#64, 8⟩]]

def entryHeaderEvents (base scratch message : Val) : List Event :=
  staticEvents (routineAddress base entry + 0x45#64) ((decodeRange entry 0x45 8).getD [])
    [[⟨false, scratch, 8⟩], [], [⟨true, scratch + 8#64, 8⟩], [⟨true, scratch + 16#64, 8⟩],
      [⟨false, message + 16#64, 8⟩], [], [⟨true, scratch + 24#64, 8⟩], []]

def entryCopySetupEvents (base message : Val) : List Event :=
  staticEvents (routineAddress base entry + 0xd9#64) ((decodeRange entry 0xd9 4).getD [])
    [[⟨false, message + 8#64, 8⟩], [], [], [⟨false, message + 16#64, 8⟩]]

def entryFinishSetupEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base entry + 0xeb#64) ((decodeRange entry 0xeb 4).getD [])
    [[], [], [], [⟨true, sp - 8#64, 8⟩]]

def entryStatusEvents (base : Val) : List Event :=
  [(routineAddress base entry + 0xfb#64, ⟨.mov .d (.reg .rax) (.imm 0#64), 5⟩, [])]

theorem entry_capacity_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xe#64) (live : s.ms = none) :
    rangeEvents ((decodeRange entry 0xe 7).getD []) s =
      entryCapacityEvents base (s.regs.get .rdx) (s.regs.get .rsi) := by
  simp (config := {decide := true}) only [entryCapacityEvents, entry_capacity_decoded, Option.getD_some,
    staticEvents, rangeAddresses, rangeEvents, move_reg, set_buffer_status, load_argument_word,
    live, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, pc,
    Regs.get_set_same, Regs.get_set_ne, if_false, List.nil_append, List.append_nil]
  rfl

theorem entry_key_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x3a#64) (live : s.ms = none) :
    rangeEvents ((decodeRange entry 0x3a 3).getD []) s = entryKeySetupEvents base (s.regs.get .rsp) := by
  simp (config := {decide := true}) only [entryKeySetupEvents, entry_key_call_decoded, Option.getD_some,
    staticEvents, rangeAddresses, rangeEvents, move_reg, live, localAccesses, dataAccesses,
    operandAccess, List.append_nil, List.nil_append, Regs.get_set_ne, pc]
  rfl

theorem entry_header_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0x45#64) (live : s.ms = none) :
    rangeEvents ((decodeRange entry 0x45 8).getD []) s =
      entryHeaderEvents base (s.regs.get .r12) (s.regs.get .rbp) := by
  simp (config := {decide := true}) only [entryHeaderEvents, inner_header_decoded, Option.getD_some,
    staticEvents, rangeAddresses, rangeEvents, load_argument_word, subtract_rax,
    store_scratch, add_rax, set_ipad, Operand.isMem, live,
    localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, pc,
    Regs.get_set_ne, List.append_nil, List.nil_append, if_false]
  rfl

theorem entry_copy_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xd9#64) (live : s.ms = none) :
    rangeEvents ((decodeRange entry 0xd9 4).getD []) s = entryCopySetupEvents base (s.regs.get .rbp) := by
  simp (config := {decide := true}) only [entryCopySetupEvents, copy_setup_decoded, Option.getD_some,
    staticEvents, rangeAddresses, rangeEvents, load_argument_word, add_message_base, lea_message_dest,
    live, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes,
    show (0 : Val) = 0#64 from rfl, BitVec.zero_add, BitVec.add_zero, pc,
    Regs.get_set_ne, List.append_nil, List.nil_append, if_false]
  rfl

theorem entry_finish_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base entry + 0xeb#64) (live : s.ms = none) :
    rangeEvents ((decodeRange entry 0xeb 4).getD []) s = entryFinishSetupEvents base (s.regs.get .rsp) := by
  simp (config := {decide := true}) only [entryFinishSetupEvents, entry_finish_call_decoded, Option.getD_some,
    staticEvents, rangeAddresses, rangeEvents, move_reg, entry_scratch_pointer, live,
    localAccesses, dataAccesses, operandAccess, List.append_nil, List.nil_append, Regs.get_set_ne, pc]
  rfl

theorem entry_status_events {base : Val} (s : Cpu) (pc : s.rip = routineAddress base entry + 0xfb#64) :
    rangeEvents [⟨.mov .d (.reg .rax) (.imm 0#64), 5⟩] s = entryStatusEvents base := by
  simp [entryStatusEvents, rangeEvents, localAccesses, dataAccesses, operandAccess, pc]

end Crypto.HMACSHA256.X86_64
