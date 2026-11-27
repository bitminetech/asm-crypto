import Proofs.HMACSHA256.X86FrameTrace
import Proofs.HMACSHA256.X86RepeatTrace
import Proofs.HMACSHA256.X86KeySetup
import Proofs.HMACSHA256.X86Key

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority)
open Crypto.ARM64.Imported (DataAccess)

set_option maxRecDepth 8192
set_option maxHeartbeats 3800000
set_option linter.unusedSimpArgs false

def KeyCodeRights (base : Val) (authority : Authority) : Prop :=
  ∀ i < key.image.size, canonical (routineAddress base key + BitVec.ofNat 64 i) = true ∧
    authority.executable (routineAddress base key + BitVec.ofNat 64 i)

theorem word_rights (authority : Authority) (write : Bool) (addr : Val)
    (range : ∀ i < 8, canonical (addr + BitVec.ofNat 64 i) = true ∧
      if write then authority.writable (addr + BitVec.ofNat 64 i)
      else authority.readable (addr + BitVec.ofNat 64 i)) :
    ∀ p, DataByte ⟨write, addr, 8⟩ p → canonical p = true ∧
      if write then authority.writable p else authority.readable p := by
  rintro p ⟨i, hi, rfl⟩
  exact range i hi

scoped macro "hmac_x86_known" : tactic =>
  `(tactic| (
    intro i present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    repeat' first | (rcases present with present | present) | (subst i)
    all_goals refine ⟨?_, by decide⟩
    all_goals first
      | exact .scalar ⟨.mov _ _ _, rfl⟩
      | exact .scalar ⟨.lea _ _ _, rfl⟩
      | exact .scalar ⟨.bin _ _ _ _, rfl⟩
      | exact .scalar ⟨.jump _, rfl⟩
      | exact .scalar ⟨.branch _ _, rfl⟩
      | exact .call _ rfl
  ))

theorem key_clear_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0xe#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : KeyCodeRights base authority) :
    RangeReady key base authority 0xe s ((decodeRange key 0xe 5).getD []) := by
  rw [key_clear_setup_decoded, Option.getD_some]
  refine range_ready_of_events key_clear_setup_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg,
      xor_accumulator, set_clear_count, live, Cpu.undefBit, pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, xor_accumulator, set_clear_count, Cpu.undefBit,
      live, direction, Flags.logic, Flags.fromResult]
  · simp [rangeEvents, localAccesses, dataAccesses, operandAccess, move_reg, xor_accumulator,
      set_clear_count, Cpu.undefBit, live]

theorem key_length_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x21#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : KeyCodeRights base authority)
    (read : ∀ i < 8, canonical (s.regs.get .rbx + 16#64 + BitVec.ofNat 64 i) = true ∧
      authority.readable (s.regs.get .rbx + 16#64 + BitVec.ofNat 64 i)) :
    RangeReady key base authority 0x21 s ((decodeRange key 0x21 3).getD []) := by
  rw [key_length_decoded, Option.getD_some]
  have load := load_argument_word s .rcx { base := some .rbx, disp := 16#64 } 4 live rfl
  refine range_ready_of_events key_length_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, load, compare_key_length,
      live, pc, BitVec.add_assoc]
  · simp [rangeStates, load, compare_key_length, live, direction, Flags.sub, Flags.fromResult]
  · intro event retired a seen p hit
    have events := And.intro retired seen
    simp only [rangeEvents, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset,
      Size.bytes, load, compare_key_length, live, show (0 : Val) = 0#64 from rfl,
      BitVec.add_zero, BitVec.zero_add, List.append_nil, List.nil_append, Option.getD_some,
      List.mem_cons, List.not_mem_nil, or_false] at events
    rcases events with ⟨h | h | h, present⟩ <;> rw [h] at present
    · obtain rfl : a = ⟨false, s.regs.get .rbx + 16#64, 8⟩ := List.mem_singleton.mp present
      exact word_rights authority false _ read p hit
    · exact False.elim (List.not_mem_nil present)
    · exact False.elim (List.not_mem_nil present)

theorem key_copy_setup_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x2b#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : KeyCodeRights base authority)
    (read : ∀ i < 8, canonical (s.regs.get .rbx + 8#64 + BitVec.ofNat 64 i) = true ∧
      authority.readable (s.regs.get .rbx + 8#64 + BitVec.ofNat 64 i)) :
    RangeReady key base authority 0x2b s ((decodeRange key 0x2b 3).getD []) := by
  rw [short_setup_decoded, Option.getD_some]
  have load := load_argument_word s .rsi { base := some .rbx, disp := 8#64 } 4 live rfl
  refine range_ready_of_events short_setup_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, load, add_key_base,
      live, pc, BitVec.add_assoc]
  · simp [rangeStates, load, add_key_base, live, direction, Flags.add, Flags.fromResult]
  · intro event retired a seen p hit
    have events := And.intro retired seen
    simp only [rangeEvents, localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset,
      Size.bytes, load, add_key_base, live, show (0 : Val) = 0#64 from rfl,
      BitVec.add_zero, BitVec.zero_add, List.append_nil, List.nil_append, Option.getD_some,
      List.mem_cons, List.not_mem_nil, or_false] at events
    rcases events with ⟨h | h | h, present⟩ <;> rw [h] at present
    · obtain rfl : a = ⟨false, s.regs.get .rbx + 8#64, 8⟩ := List.mem_singleton.mp present
      exact word_rights authority false _ read p hit
    · exact False.elim (List.not_mem_nil present)
    · exact False.elim (List.not_mem_nil present)

theorem key_copy_exit_decoded : decodeRange key 0x37 1 = some [⟨.jmp (.rel 11#64), 2⟩] := by
  decide +kernel

theorem key_copy_exit_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x37#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : KeyCodeRights base authority) :
    RangeReady key base authority 0x37 s [⟨.jmp (.rel 11#64), 2⟩] := by
  refine range_ready_of_events key_copy_exit_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp [rangeStates, rangeAddresses, pc]
  · simp [rangeStates, live, direction]
  · simp [rangeEvents, localAccesses, dataAccesses]

theorem key_call_ready {base : Val} {authority : Authority} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x39#64) (live : s.ms = none) (direction : s.flags.df = false)
    (code : KeyCodeRights base authority)
    (write : ∀ i < 8, canonical (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i) = true ∧
      authority.writable (s.regs.get .rsp - 8#64 + BitVec.ofNat 64 i)) :
    RangeReady key base authority 0x39 s ((decodeRange key 0x39 3).getD []) := by
  rw [long_call_decoded, Option.getD_some]
  refine range_ready_of_events long_call_decoded (by decide +kernel) (by decide +kernel)
    ?_ code ?_ ?_ ?_
  · hmac_x86_known
  · simp only [rangeStates, rangeAddresses, List.map_cons, List.map_nil, move_reg, live,
      pc, BitVec.add_assoc]
  · simp [rangeStates, move_reg, live, direction]
  · intro event retired a seen p hit
    have events := And.intro retired seen
    simp only [rangeEvents, move_reg, live, localAccesses, dataAccesses, operandAccess,
      List.append_nil, List.nil_append, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false,
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
      Regs.get_set_ne _ _ _ _ (by decide : GPR.rdi ≠ .rsp)] at events
    rcases events with ⟨h | h | h, present⟩ <;> rw [h] at present
    · exact False.elim (List.not_mem_nil present)
    · exact False.elim (List.not_mem_nil present)
    · obtain rfl : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp present
      exact word_rights authority true _ write p hit

def keyInitEvents (base : Val) : List Event :=
  staticEvents (routineAddress base key + 0xe#64) ((decodeRange key 0xe 5).getD []) [[], [], [], [], []]

def keyTestEvents (base src : Val) : List Event :=
  staticEvents (routineAddress base key + 0x21#64) ((decodeRange key 0x21 3).getD [])
    [[⟨false, src + 16#64, 8⟩], [], []]

def keyCopySetupEvents (base src : Val) : List Event :=
  staticEvents (routineAddress base key + 0x2b#64) ((decodeRange key 0x2b 3).getD [])
    [[⟨false, src + 8#64, 8⟩], [], []]

def keyCopyExitEvents (base : Val) : List Event :=
  [(routineAddress base key + 0x37#64, ⟨.jmp (.rel 11#64), 2⟩, [])]

def keyCallEvents (base sp : Val) : List Event :=
  staticEvents (routineAddress base key + 0x39#64) ((decodeRange key 0x39 3).getD [])
    [[], [], [⟨true, sp - 8#64, 8⟩]]

theorem key_init_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0xe#64) (live : s.ms = none) :
    rangeEvents ((decodeRange key 0xe 5).getD []) s = keyInitEvents base := by
  simp only [keyInitEvents, key_clear_setup_decoded, Option.getD_some, staticEvents, rangeEvents, rangeAddresses,
    localAccesses, dataAccesses, operandAccess, move_reg, xor_accumulator, set_clear_count,
    live, Cpu.undefBit, List.nil_append, List.append_nil, pc]
  rfl

theorem key_test_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x21#64) (live : s.ms = none) :
    rangeEvents ((decodeRange key 0x21 3).getD []) s = keyTestEvents base (s.regs.get .rbx) := by
  have load := load_argument_word s .rcx { base := some .rbx, disp := 16#64 } 4 live rfl
  simp only [keyTestEvents, key_length_decoded, Option.getD_some, staticEvents, rangeEvents, rangeAddresses,
    localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes, load, compare_key_length,
    live, show (0 : Val) = 0#64 from rfl, BitVec.add_zero, BitVec.zero_add, List.append_nil, List.nil_append, pc]
  rfl

theorem key_copy_setup_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x2b#64) (live : s.ms = none) :
    rangeEvents ((decodeRange key 0x2b 3).getD []) s = keyCopySetupEvents base (s.regs.get .rbx) := by
  have load := load_argument_word s .rsi { base := some .rbx, disp := 8#64 } 4 live rfl
  simp only [keyCopySetupEvents, short_setup_decoded, Option.getD_some, staticEvents, rangeEvents, rangeAddresses,
    localAccesses, dataAccesses, operandAccess, Ea.addr, Ea.offset, Size.bytes, load, add_key_base,
    live, show (0 : Val) = 0#64 from rfl, BitVec.add_zero, BitVec.zero_add, List.append_nil, List.nil_append, pc]
  rfl

theorem key_copy_exit_events {base : Val} (s : Cpu) (pc : s.rip = routineAddress base key + 0x37#64) :
    rangeEvents [⟨.jmp (.rel 11#64), 2⟩] s = keyCopyExitEvents base := by
  simp [rangeEvents, keyCopyExitEvents, localAccesses, dataAccesses, pc]

theorem key_call_events {base : Val} (s : Cpu)
    (pc : s.rip = routineAddress base key + 0x39#64) (live : s.ms = none) :
    rangeEvents ((decodeRange key 0x39 3).getD []) s = keyCallEvents base (s.regs.get .rsp) := by
  simp only [keyCallEvents, long_call_decoded, Option.getD_some, staticEvents, rangeEvents, rangeAddresses,
    localAccesses, dataAccesses, operandAccess, move_reg, live, List.append_nil, List.nil_append, pc,
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rsi ≠ .rsp),
    Regs.get_set_ne _ _ _ _ (by decide : GPR.rdi ≠ .rsp)]
  rfl

end Crypto.HMACSHA256.X86_64
