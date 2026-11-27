import Proofs.HMACSHA256.X86Ranges
import Proofs.HMACSHA256.X86FrameMemory
import Proofs.HMACSHA256.X86Return
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.Baseline (Authority Region)
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset)

private theorem pushed_once (s : Cpu) (item : GPR × Nat) (live : s.ms = none) :
    step ⟨.push .q (.reg item.1), item.2⟩ s = saveRegister s item := by
  rw [step_push_reg _ _ live]
  simp [saveRegister, Cpu.getReg, Size.bytes]

private theorem restore_sp (s : Cpu) (item : GPR × Nat) (fixed : item.1 ≠ .rsp) :
    (restoreSlot s item).regs.get .rsp = s.regs.get .rsp + 8#64 := by
  simp only [restoreSlot, Regs.get_set_ne _ _ _ _ fixed, Regs.get_set_same]

def saveEvents (pc sp : Val) : List (GPR × Nat) → List Event
  | [] => []
  | (reg, len) :: rest =>
    let addr := sp - 8#64
    (pc, ⟨.push .q (.reg reg), len⟩, [⟨true, addr, 8⟩]) ::
      saveEvents (pc + BitVec.ofNat 64 len) addr rest

def restoreEvents (pc sp : Val) : List (GPR × Nat) → List Event
  | [] => [(pc, ⟨.ret, 1⟩, [⟨false, sp, 8⟩])]
  | item :: rest =>
    (pc, popInstruction item, [⟨false, sp, 8⟩]) ::
      restoreEvents (pc + BitVec.ofNat 64 item.2) (sp + 8#64) rest

private theorem run_pushes_events (slots : List (GPR × Nat)) (s : Cpu) (live : s.ms = none) :
    rangeEvents (slots.map (fun (reg, len) => ⟨.push .q (.reg reg), len⟩)) s =
      saveEvents s.rip (s.regs.get .rsp) slots := by
  induction slots generalizing s with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨reg, len⟩ := item
    change (_, _, _) :: rangeEvents _ (step ⟨.push .q (.reg reg), len⟩ s) = _
    rw [pushed_once s (reg, len) live, ih (saveRegister s (reg, len)) live]
    simp only [saveRegister, saveEvents, Regs.get_set_same]
    rfl

def frameEnterEvents (r : HmacRoutine) (pc sp : Val) : List Event :=
  saveEvents pc sp saveSlots ++ [(pc + 10#64, allocate r, [])]

theorem frame_prologue_events (r : HmacRoutine) (s : Cpu) (live : s.ms = none) :
    rangeEvents (saveCode r) s = frameEnterEvents r s.rip (s.regs.get .rsp) := by
  unfold saveCode frameEnterEvents
  rw [rangeEvents_append, run_pushes_events _ _ live, run_save_registers _ _ live]
  have pc : (saveSlots.foldl saveRegister s).rip = s.rip + 10#64 := by
    simp only [saveSlots, List.foldl_cons, List.foldl_nil, saveRegister, BitVec.add_assoc]
    rfl
  simp only [rangeEvents, pc]
  rfl

private theorem run_pops_events (slots : List (GPR × Nat)) (s : Cpu) (live : s.ms = none)
    (fixed : ∀ item ∈ slots, item.1 ≠ .rsp) :
    rangeEvents (slots.map popInstruction ++ [⟨.ret, 1⟩]) s =
      restoreEvents s.rip (s.regs.get .rsp) slots := by
  induction slots generalizing s with
  | nil => rfl
  | cons item rest ih =>
    have kept := fixed item List.mem_cons_self
    have following := ih (restoreSlot s item) live (fun p h => fixed p (List.mem_cons_of_mem _ h))
    change (_, _, _) :: rangeEvents (rest.map popInstruction ++ [⟨.ret, 1⟩])
      (step (popInstruction item) s) = _
    rw [pop_step _ _ live, following, restore_sp _ _ kept]
    rfl

private theorem pushes_ready (r : HmacRoutine) (base : Val) (authority : Authority)
    (s : Cpu) (off : Nat) (slots : List (GPR × Nat))
    (pc : s.rip = routineAddress base r.image + BitVec.ofNat 64 off)
    (live : s.ms = none) (direction : s.flags.df = false)
    (bounded : r.image.image.size < 2 ^ 64)
    (decode : decodeRange r.image off (slots.length + 1) =
      some (slots.map (fun (reg, len) => ⟨.push .q (.reg reg), len⟩) ++ [allocate r]))
    (code : ∀ i < r.image.image.size, canonical (routineAddress base r.image + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r.image + BitVec.ofNat 64 i))
    (lengths : ∀ item ∈ slots, 0 < item.2)
    (within : off + (slots.map Prod.snd).sum + r.allocLength ≤ r.image.image.size)
    (writable : ∀ j < 8 * slots.length, canonical (s.regs.get .rsp - BitVec.ofNat 64 (8 * slots.length) +
      BitVec.ofNat 64 j) = true ∧ authority.writable (s.regs.get .rsp - BitVec.ofNat 64 (8 * slots.length) +
        BitVec.ofNat 64 j)) :
    RangeReady r.image base authority off s (slots.map (fun (reg, len) => ⟨.push .q (.reg reg), len⟩) ++ [allocate r]) := by
  induction slots generalizing off s with
  | nil =>
    obtain ⟨head, _⟩ := decode_range_cons decode
    have len : (allocate r).len = r.allocLength := rfl
    have positive : 0 < (allocate r).len := by cases r <;> decide
    have fits : off + (allocate r).len ≤ r.image.image.size := by simpa only [len, List.map_nil, List.sum_nil, Nat.add_zero] using within
    refine ⟨pc, by omega, head, positive, fits, .scalar ⟨.bin .sub .q (.reg .rsp) (.imm r.locals), rfl⟩,
      live, direction, ⟨[], rfl, ?_, by simp⟩, trivial⟩
    rw [pc]
    exact fetch_rights code fits
  | cons item rest ih =>
    obtain ⟨reg, len⟩ := item
    let i : Instr := ⟨.push .q (.reg reg), len⟩
    let next := saveRegister s (reg, len)
    obtain ⟨decoded, tail⟩ := decode_range_cons decode
    have length : 0 < len := lengths (reg,len) List.mem_cons_self
    have fits : off + len ≤ r.image.image.size := by
      simp only [List.map_cons, List.sum_cons] at within
      omega
    have sp : next.regs.get .rsp = s.regs.get .rsp - 8#64 := by simp only [next, saveRegister, Regs.get_set_same]
    have nextPc : next.rip = routineAddress base r.image + BitVec.ofNat 64 (off + len) := by
      change s.rip + BitVec.ofNat 64 len = _
      rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
    have front (p : Val) (h : DataByte ⟨true, s.regs.get .rsp - 8#64, 8⟩ p) :
        canonical p = true ∧ authority.writable p := by
      obtain ⟨j, hj, rfl⟩ := h
      change j < 8 at hj
      have eq : s.regs.get .rsp - 8#64 + BitVec.ofNat 64 j =
          s.regs.get .rsp - BitVec.ofNat 64 (8 * ((reg,len) :: rest).length) +
            BitVec.ofNat 64 (8 * rest.length + j) := by
        simp only [List.length_cons, Nat.mul_succ, BitVec.ofNat_add]
        rw [BitVec.add_comm (BitVec.ofNat 64 (8 * rest.length)) (BitVec.ofNat 64 8),
          ← BitVec.sub_sub, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [eq]
      exact writable _ (by simp only [List.length_cons, Nat.mul_succ]; omega)
    refine ⟨pc, by omega, decoded, length, fits, .scalar ⟨.push reg, rfl⟩, live, direction,
      ⟨[⟨true, s.regs.get .rsp - 8#64, 8⟩], rfl, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [pc]
        exact fetch_rights code fits
      · intro a ha p hit
        have eq : a = ⟨true, s.regs.get .rsp - 8#64, 8⟩ := List.mem_singleton.mp ha
        subst a
        exact front p hit
    · change RangeReady r.image base authority (off + len) (step i s) _
      have same : step i s = next := pushed_once s (reg, len) live
      rw [same]
      apply ih next (off + len) nextPc live direction tail
        (fun item h => lengths item (List.mem_cons_of_mem _ h))
      · simp only [List.map_cons, List.sum_cons] at within
        omega
      · intro j hj
        rw [sp, BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm 8]
        exact writable j (by simp only [List.length_cons, Nat.mul_succ]; omega)

set_option maxRecDepth 8192 in
theorem frame_prologue_ready (r : HmacRoutine) (base : Val) (authority : Authority) (s : Cpu)
    (pc : s.rip = routineAddress base r.image) (live : s.ms = none) (direction : s.flags.df = false)
    (code : ∀ i < r.image.image.size, canonical (routineAddress base r.image + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r.image + BitVec.ofNat 64 i))
    (write : ∀ j < 48, canonical (savedBase s + BitVec.ofNat 64 j) = true ∧
      authority.writable (savedBase s + BitVec.ofNat 64 j)) :
    RangeReady r.image base authority 0 s (saveCode r) := by
  apply pushes_ready r base authority s 0 saveSlots (by simpa only [BitVec.add_zero] using pc)
    live direction (by cases r <;> decide +kernel) (prologue_decoded r) code
  · intro item member
    simp only [saveSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h|h|h|h|h|h <;> subst item <;> decide
  · cases r <;> decide +kernel
  · exact write


def HmacRoutine.returnOffset : HmacRoutine → Nat
  | .entry => 0x100
  | .key => 0x44
  | .finish => 0xaf

theorem epilogue_decoded (r : HmacRoutine) :
    decodeRange r.image r.returnOffset 8 = some (returnCode r.locals r.allocLength) := by
  cases r
  · exact entry_return_decoded
  · exact key_return_decoded
  · exact finish_return_decoded

def frameReturnEvents (r : HmacRoutine) (pc sp : Val) : List Event :=
  (pc, ⟨.bin .add .q (.reg .rsp) (.imm r.locals), r.allocLength⟩, []) ::
    restoreEvents (pc + BitVec.ofNat 64 r.allocLength) (sp + r.locals) returnSlots

private theorem fixed_return_slots : ∀ slot ∈ returnSlots, slot.1 ≠ .rsp := by
  intro slot member
  simp only [returnSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h|h|h|h|h|h <;> subst slot <;> decide

theorem frame_return_events (r : HmacRoutine) (s : Cpu) (live : s.ms = none) :
    rangeEvents (returnCode r.locals r.allocLength) s =
      frameReturnEvents r s.rip (s.regs.get .rsp) := by
  let next := releaseFrame s r.locals r.allocLength
  have following := run_pops_events returnSlots next live fixed_return_slots
  change (_, _, _) :: rangeEvents (returnSlots.map popInstruction ++ [⟨.ret, 1⟩])
    (step ⟨.bin .add .q (.reg .rsp) (.imm r.locals), r.allocLength⟩ s) = _
  rw [release_step, following]
  · change (_, _, _) :: restoreEvents (s.rip + BitVec.ofNat 64 r.allocLength)
      ((next.regs).get .rsp) returnSlots = _
    simp only [next, releaseFrame, Regs.get_set_same]
    rfl
  · exact live

private theorem stack_read (authority : Authority) (sp : Val)
    (read : ∀ j < 8, canonical (sp + BitVec.ofNat 64 j) = true ∧
      authority.readable (sp + BitVec.ofNat 64 j))
    (a : DataAccess) (present : a ∈ [⟨false, sp, 8⟩]) (p : Val) (hit : DataByte a p) :
    canonical p = true ∧ if a.write then authority.writable p else authority.readable p := by
  have eq : a = ⟨false, sp, 8⟩ := List.mem_singleton.mp present
  subst a
  obtain ⟨j, hj, rfl⟩ := hit
  exact read j hj

private theorem pops_ready (r : HmacRoutine) (base : Val) (authority : Authority)
    (s : Cpu) (off : Nat) (slots : List (GPR × Nat))
    (pc : s.rip = routineAddress base r.image + BitVec.ofNat 64 off)
    (live : s.ms = none) (direction : s.flags.df = false)
    (bounded : r.image.image.size < 2 ^ 64)
    (decode : decodeRange r.image off (slots.length + 1) =
      some (slots.map popInstruction ++ [⟨.ret, 1⟩]))
    (code : ∀ i < r.image.image.size, canonical (routineAddress base r.image + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r.image + BitVec.ofNat 64 i))
    (fixed : ∀ item ∈ slots, item.1 ≠ .rsp) (lengths : ∀ item ∈ slots, 0 < item.2)
    (within : off + (slots.map Prod.snd).sum + 1 ≤ r.image.image.size)
    (readable : ∀ j < 8 * (slots.length + 1), canonical (s.regs.get .rsp + BitVec.ofNat 64 j) = true ∧
      authority.readable (s.regs.get .rsp + BitVec.ofNat 64 j)) :
    RangeReady r.image base authority off s (slots.map popInstruction ++ [⟨.ret, 1⟩]) := by
  induction slots generalizing off s with
  | nil =>
    obtain ⟨head, _⟩ := decode_range_cons decode
    have fits : off + 1 ≤ r.image.image.size := by
      simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using within
    refine ⟨pc, by omega, head, by decide, fits, .scalar ⟨.ret, rfl⟩, live, direction,
      ⟨[⟨false, s.regs.get .rsp, 8⟩], rfl, ⟨?_, stack_read _ _ readable⟩⟩, trivial⟩
    rw [pc]
    exact fetch_rights code fits
  | cons item tail ih =>
    let next := restoreSlot s item
    obtain ⟨head, decoded⟩ := decode_range_cons decode
    have len : 0 < item.2 := lengths _ List.mem_cons_self
    have fits : off + item.2 ≤ r.image.image.size := by
      simp only [List.map_cons, List.sum_cons] at within
      omega
    have nextPc : next.rip = routineAddress base r.image + BitVec.ofNat 64 (off + item.2) := by
      change s.rip + BitVec.ofNat 64 item.2 = _
      rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
    have read (j : Nat) (hj : j < 8) := readable j (by
      simp only [List.length_cons, Nat.mul_succ]
      omega)
    refine ⟨pc, by omega, head, len, fits, .scalar ⟨.pop item.1, rfl⟩, live, direction,
      ⟨[⟨false, s.regs.get .rsp, 8⟩], rfl, ⟨?_, stack_read _ _ read⟩⟩, ?_⟩
    · rw [pc]
      exact fetch_rights code fits
    · change RangeReady r.image base authority (off + item.2) (step (popInstruction item) s)
        (tail.map popInstruction ++ [⟨.ret, 1⟩])
      rw [pop_step _ _ live]
      apply ih next (off + item.2) nextPc live direction decoded
        (fun j h => fixed j (List.mem_cons_of_mem _ h)) (fun j h => lengths j (List.mem_cons_of_mem _ h))
      · simp only [List.map_cons, List.sum_cons] at within
        omega
      · intro j hj
        rw [restore_sp _ _ (fixed item List.mem_cons_self), BitVec.add_assoc,
          ← show BitVec.ofNat 64 8 = 8#64 from rfl, ← BitVec.ofNat_add]
        exact readable _ (by simp only [List.length_cons, Nat.mul_succ]; omega)

set_option maxRecDepth 8192 in
theorem frame_epilogue_ready (r : HmacRoutine) (base : Val) (authority : Authority) (s : Cpu)
    (pc : s.rip = routineAddress base r.image + BitVec.ofNat 64 r.returnOffset)
    (live : s.ms = none) (direction : s.flags.df = false)
    (code : ∀ i < r.image.image.size, canonical (routineAddress base r.image + BitVec.ofNat 64 i) = true ∧
      authority.executable (routineAddress base r.image + BitVec.ofNat 64 i))
    (read : ∀ j < 56, canonical (s.regs.get .rsp + r.locals + BitVec.ofNat 64 j) = true ∧
      authority.readable (s.regs.get .rsp + r.locals + BitVec.ofNat 64 j)) :
    RangeReady r.image base authority r.returnOffset s (returnCode r.locals r.allocLength) := by
  let next := releaseFrame s r.locals r.allocLength
  obtain ⟨head, tail⟩ := decode_range_cons (epilogue_decoded r)
  have fits : r.returnOffset + r.allocLength ≤ r.image.image.size := by cases r <;> decide +kernel
  have bound : r.image.image.size < 2 ^ 64 := by cases r <;> decide +kernel
  have len : 0 < r.allocLength := by cases r <;> decide
  have nextPC : next.rip = routineAddress base r.image + BitVec.ofNat 64 (r.returnOffset + r.allocLength) := by
    change s.rip + BitVec.ofNat 64 r.allocLength = _
    rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨pc, by omega, head, len, fits, .scalar ⟨.bin .add .q (.reg .rsp) (.imm r.locals), rfl⟩,
    live, direction, ⟨[], rfl, ?_, by simp⟩, ?_⟩
  · rw [pc]
    exact fetch_rights code fits
  · change RangeReady r.image base authority (r.returnOffset + r.allocLength)
      (step ⟨.bin .add .q (.reg .rsp) (.imm r.locals), r.allocLength⟩ s)
      (returnSlots.map popInstruction ++ [⟨.ret, 1⟩])
    rw [release_step _ _ _ live]
    apply pops_ready r base authority next _ returnSlots nextPC live direction bound tail code fixed_return_slots
    · intro item member
      simp only [returnSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h|h|h|h|h|h <;> subst item <;> decide
    · cases r <;> decide +kernel
    · intro j hj
      change canonical (next.regs.get .rsp + BitVec.ofNat 64 j) = true ∧
        authority.readable (next.regs.get .rsp + BitVec.ofNat 64 j)
      simpa only [next, releaseFrame, Regs.get_set_same] using read j hj

end Crypto.HMACSHA256.X86_64
