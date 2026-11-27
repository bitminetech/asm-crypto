import Proofs.HMACSHA256.RISCV64Setup
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64
open Crypto.Baseline (Region)
open Crypto.HMACSHA256.ARM64 (read64_eq_of_cells writeWords writeWords_outside writeWords_word)

inductive HmacRoutine where
  | entry | key | finish

def HmacRoutine.image : HmacRoutine → Routine
  | .entry => Crypto.HMACSHA256.RISCV64.entry
  | .key => Crypto.HMACSHA256.RISCV64.key
  | .finish => Crypto.HMACSHA256.RISCV64.finish

def HmacRoutine.frameSize : HmacRoutine → Nat
  | .entry => 176
  | .key => 112
  | .finish => 240

def HmacRoutine.savedOffset : HmacRoutine → Nat
  | .entry => 64
  | .key => 0
  | .finish => 128

def HmacRoutine.returnOffset : HmacRoutine → Nat
  | .entry => 0x112
  | .key => 0x88
  | .finish => 0xbc

structure FrameSlot where
  index : Nat
  register : Reg
  deriving DecidableEq

def frameSlots : List FrameSlot := [
  ⟨0, 1#5⟩, ⟨1, 8#5⟩, ⟨2, 9#5⟩, ⟨3, 18#5⟩, ⟨4, 19#5⟩, ⟨5, 20#5⟩, ⟨6, 21#5⟩,
  ⟨7, 22#5⟩, ⟨8, 23#5⟩, ⟨9, 24#5⟩, ⟨10, 25#5⟩, ⟨11, 26#5⟩, ⟨12, 27#5⟩]

def FrameSlot.address (r : HmacRoutine) (s : CPU) (slot : FrameSlot) : Addr :=
  s.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * slot.index)

def saveOne (r : HmacRoutine) (slot : FrameSlot) : Op :=
  .scalar ⟨.store .double slot.register 2#5 (BitVec.ofNat 64 (r.savedOffset + 8 * slot.index)), 2⟩

def loadOne (r : HmacRoutine) (slot : FrameSlot) : Op :=
  .scalar ⟨.load .double slot.register 2#5 (BitVec.ofNat 64 (r.savedOffset + 8 * slot.index)), 2⟩

def enterCode (r : HmacRoutine) : List Op :=
  .scalar ⟨.addi 2#5 2#5 (-BitVec.ofNat 64 r.frameSize), 2⟩ :: frameSlots.map (saveOne r)

def returnCode (r : HmacRoutine) : List Op :=
  frameSlots.map (loadOne r) ++
    [.scalar ⟨.addi 2#5 2#5 (BitVec.ofNat 64 r.frameSize), 2⟩, .scalar ⟨.ret, 2⟩]

theorem entered_decoded (r : HmacRoutine) :
    decodeRange r.image 0 14 = some (enterCode r) := by
  cases r <;> decide +kernel

theorem returned_decoded (r : HmacRoutine) :
    decodeRange r.image r.returnOffset 15 = some (returnCode r) := by
  cases r <;> decide +kernel

def reserveFrame (r : HmacRoutine) (s : CPU) : CPU :=
  (s.advance 2).put 2#5 (s.reg 2#5 - BitVec.ofNat 64 r.frameSize)

def spillSlot (r : HmacRoutine) (s : CPU) (slot : FrameSlot) : CPU :=
  (s.advance 2).write (s.mem.write64 (slot.address r s) (s.reg slot.register))

def enteredFrame (r : HmacRoutine) (s : CPU) : CPU :=
  frameSlots.foldl (spillSlot r) (reserveFrame r s)

private theorem save_fold (r : HmacRoutine) (s : CPU) (slots : List FrameSlot) :
    runOps (slots.map (saveOne r)) s = slots.foldl (spillSlot r) s := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot rest ih =>
    change runOps (rest.map (saveOne r)) ((saveOne r slot).step s) =
      rest.foldl (spillSlot r) (spillSlot r s slot)
    have step : (saveOne r slot).step s = spillSlot r s slot := rfl
    rw [step, ih]

set_option maxHeartbeats 1400000 in
/-- The prologue reserves its target frame and saves the link and all twelve
LP64D saved integer registers in the recorded stack slots. -/
theorem enter_frame (r : HmacRoutine) (s : CPU) :
    runRange r.image 0 14 s = some (enteredFrame r s) := by
  unfold runRange
  rw [entered_decoded]
  have runHead (op : Op) (tail : List Op) :
      runOps (op :: tail) s = runOps tail (op.step s) := rfl
  simp only [Option.map_some, enterCode, runHead]
  have reserve : (Op.scalar ⟨.addi 2#5 2#5 (-BitVec.ofNat 64 r.frameSize), 2⟩).step s =
      reserveFrame r s := by
    simp [Op.step, Instruction.step, reserveFrame, BitVec.sub_eq_add_neg]
  rw [reserve, save_fold]
  rfl

private theorem spillFold_reg (r : HmacRoutine) (slots : List FrameSlot) (s : CPU) (reg : Reg) :
    (slots.foldl (spillSlot r) s).reg reg = s.reg reg := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot tail ih => rw [List.foldl_cons, ih, spillSlot, reg_write, reg_advance]

theorem enteredFrame_reg (r : HmacRoutine) (s : CPU) (reg : Reg) (other : reg ≠ 2#5) :
    (enteredFrame r s).reg reg = s.reg reg := by
  unfold enteredFrame
  rw [spillFold_reg, reserveFrame, reg_put, if_neg other, reg_advance]
  split
  · rename_i zero
    rw [zero, reg_zero]
  · rfl

theorem enteredFrame_sp (r : HmacRoutine) (s : CPU) :
    (enteredFrame r s).reg 2#5 = s.reg 2#5 - BitVec.ofNat 64 r.frameSize := by
  rw [enteredFrame, spillFold_reg, reserveFrame, reg_put]
  rfl

theorem enteredFrame_pc (r : HmacRoutine) (s : CPU) : (enteredFrame r s).pc = s.pc + 28#64 := by
  have progress (slots : List FrameSlot) (t : CPU) :
      (slots.foldl (spillSlot r) t).pc = t.pc + BitVec.ofNat 64 (2 * slots.length) := by
    induction slots generalizing t with
    | nil => simp
    | cons slot tail ih =>
      rw [List.foldl_cons, ih, spillSlot, pc_write]
      change t.pc + 2#64 + BitVec.ofNat 64 (2 * tail.length) = _
      simp only [List.length_cons, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
      rw [BitVec.add_comm (2#64) (BitVec.ofNat 64 (2 * tail.length))]
  rw [enteredFrame, progress, reserveFrame, pc_put]
  change s.pc + 2#64 + 26#64 = s.pc + 28#64
  rw [BitVec.add_assoc]
  rfl

def frameSlot (i : Nat) : FrameSlot := frameSlots[i]?.getD ⟨i, 0⟩

private theorem frameSlots_from_range : frameSlots = (List.range 13).map frameSlot := by
  decide +kernel

theorem frameSlot_index (i : Fin 13) : (frameSlot i.val).index = i.val := by
  have indices : ∀ j : Fin 13, (frameSlot j.val).index = j.val := by decide +kernel
  exact indices i

private theorem spillWords (r : HmacRoutine) (s : CPU) (n : Nat) (within : n ≤ 13) :
    (((List.range n).map frameSlot).foldl (spillSlot r) s).mem =
      writeWords s.mem (s.reg 2#5 + BitVec.ofNat 64 r.savedOffset)
        (fun i => s.reg (frameSlot i).register) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    let mid := ((List.range n).map frameSlot).foldl (spillSlot r) s
    change (spillSlot r mid (frameSlot n)).mem = _
    rw [spillSlot, memory_write, FrameSlot.address, ih (by omega), spillFold_reg,
      show (frameSlot n).index = n from frameSlot_index ⟨n, by omega⟩]
    simp only [writeWords, BitVec.ofNat_add, BitVec.add_assoc, mid, spillFold_reg]

theorem enteredFrame_memory (r : HmacRoutine) (s : CPU) :
    (enteredFrame r s).mem =
      writeWords s.mem (s.reg 2#5 - BitVec.ofNat 64 r.frameSize + BitVec.ofNat 64 r.savedOffset)
        (fun i => (reserveFrame r s).reg (frameSlot i).register) 13 := by
  unfold enteredFrame
  rw [frameSlots_from_range, spillWords _ _ _ (by decide)]
  have reserved : (reserveFrame r s).reg 2#5 = s.reg 2#5 - BitVec.ofNat 64 r.frameSize := by
    rw [reserveFrame, reg_put]
    rfl
  rw [reserved]
  rfl

theorem enteredFrame_outside (r : HmacRoutine) (s : CPU) (p : Addr)
    (outside : 104 ≤
      (p - (s.reg 2#5 - BitVec.ofNat 64 r.frameSize + BitVec.ofNat 64 r.savedOffset)).toNat) :
    (enteredFrame r s).mem.cells p = s.mem.cells p := by
  rw [enteredFrame_memory]
  exact writeWords_outside _ _ _ 13 _ outside

theorem enteredFrame_slot (r : HmacRoutine) (s : CPU) (i : Fin 13) :
    (enteredFrame r s).mem.read64 (s.reg 2#5 - BitVec.ofNat 64 r.frameSize +
      BitVec.ofNat 64 (r.savedOffset + 8 * i.val)) = s.reg (frameSlot i.val).register := by
  have preserve : ∀ i : Fin 13, (frameSlot i.val).register ≠ 2#5 := by decide +kernel
  rw [enteredFrame_memory, BitVec.ofNat_add, ← BitVec.add_assoc,
    writeWords_word _ _ _ 13 i.val i.isLt (by decide)]
  rw [reserveFrame, reg_put, if_neg (preserve i), reg_advance]
  split
  · rename_i zero
    rw [zero, reg_zero]
  · rfl

def reloadSlot (r : HmacRoutine) (s : CPU) (slot : FrameSlot) : CPU :=
  (s.advance 2).put slot.register (s.mem.read64 (slot.address r s))

def readyReturn (r : HmacRoutine) (s : CPU) : CPU :=
  frameSlots.foldl (reloadSlot r) s

private theorem load_fold (r : HmacRoutine) (s : CPU) (slots : List FrameSlot) :
    runOps (slots.map (loadOne r)) s = slots.foldl (reloadSlot r) s := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot rest ih =>
    change runOps (rest.map (loadOne r)) ((loadOne r slot).step s) =
      rest.foldl (reloadSlot r) (reloadSlot r s slot)
    have step : (loadOne r slot).step s = reloadSlot r s slot := rfl
    rw [step, ih]

def restoredFrame (r : HmacRoutine) (s : CPU) : CPU :=
  let st := readyReturn r s
  let shifted := (st.advance 2).put 2#5 (st.reg 2#5 + BitVec.ofNat 64 r.frameSize)
  setPC shifted (st.reg 1 &&& ~~~(1 : Addr))

/-- The epilogue restores the stack slots, releases the full frame, and
returns through the architectural JALR target represented by RET. -/
theorem return_frame (r : HmacRoutine) (s : CPU) :
    runRange r.image r.returnOffset 15 s = some (restoredFrame r s) := by
  unfold runRange
  rw [returned_decoded]
  have blocks : runOps (returnCode r) s =
      runOps [.scalar ⟨.addi 2#5 2#5 (BitVec.ofNat 64 r.frameSize), 2⟩, .scalar ⟨.ret, 2⟩]
        (runOps (frameSlots.map (loadOne r)) s) := by
    simp only [returnCode, runOps, List.foldl_append]
  rw [Option.map_some, blocks, load_fold]
  change some (runOps [.scalar ⟨.addi 2#5 2#5 (BitVec.ofNat 64 r.frameSize), 2⟩, .scalar ⟨.ret, 2⟩]
    (readyReturn r s)) = _
  generalize state : readyReturn r s = st
  unfold restoredFrame
  rw [state]
  dsimp [runOps, Op.step, Instruction.step, setPC]
  have unchanged (t : CPU) (value : Addr) : (t.put 2#5 value).reg 1#5 = t.reg 1#5 := by
    rw [reg_put, if_neg (by decide : (1#5 : Reg) ≠ 0), if_neg (by decide : (1#5 : Reg) ≠ 2#5)]
  rw [unchanged, reg_advance]

theorem readyReturn_memory (r : HmacRoutine) (s : CPU) : (readyReturn r s).mem = s.mem := by
  have keep (slots : List FrameSlot) (t : CPU) : (slots.foldl (reloadSlot r) t).mem = t.mem := by
    induction slots generalizing t with
    | nil => rfl
    | cons slot tail ih =>
      rw [List.foldl_cons, ih, reloadSlot, memory_put, memory_advance]
  exact keep frameSlots s

theorem readyReturn_sp (r : HmacRoutine) (s : CPU) : (readyReturn r s).reg 2#5 = s.reg 2#5 := by
  have notSP : ∀ slot ∈ frameSlots, slot.register ≠ 2#5 := by decide +kernel
  have keep (slots : List FrameSlot) (t : CPU) (ok : ∀ slot ∈ slots, slot.register ≠ 2#5) :
      (slots.foldl (reloadSlot r) t).reg 2#5 = t.reg 2#5 := by
    induction slots generalizing t with
    | nil => rfl
    | cons slot tail ih =>
      rw [List.foldl_cons, ih _ (fun slot hs => ok _ (List.mem_cons_of_mem _ hs)),
        reloadSlot, reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0),
        if_neg (Ne.symm (ok slot (by simp))), reg_advance]
  exact keep frameSlots s notSP

private theorem reload_keeps (r : HmacRoutine) (s : CPU) (slots : List FrameSlot)
    (reg : Reg) (other : ∀ slot ∈ slots, slot.register ≠ reg) :
    (slots.foldl (reloadSlot r) s).reg reg = s.reg reg := by
  induction slots generalizing s with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, ih _ (fun slot h => other slot (List.mem_cons_of_mem _ h)),
      reloadSlot, reg_put, if_neg (Ne.symm (other head (List.mem_cons_self))), reg_advance]
    split
    · rename_i zero
      rw [zero, reg_zero]
    · rfl

theorem frameSlot_mem (i : Fin 13) : frameSlot i.val ∈ frameSlots := by
  have all : ∀ j : Fin 13, frameSlot j.val ∈ frameSlots := by decide +kernel
  exact all i

theorem returned_other_register (r : HmacRoutine) (s : CPU) (reg : Reg) (noSP : reg ≠ 2#5)
    (other : ∀ slot ∈ frameSlots, slot.register ≠ reg) :
    (restoredFrame r s).reg reg = s.reg reg := by
  simp only [restoredFrame, setPC_reg, reg_put, reg_advance, if_neg noSP]
  split
  · rename_i zero
    rw [zero, reg_zero]
  · exact reload_keeps r s frameSlots reg other

private theorem frame_registers_unique : (frameSlots.map FrameSlot.register).Nodup := by decide +kernel

theorem readyReturn_slot (r : HmacRoutine) (s : CPU) (slot : FrameSlot) (inFrame : slot ∈ frameSlots) :
    (readyReturn r s).reg slot.register = s.mem.read64 (slot.address r s) := by
  have frameValid : ∀ slot ∈ frameSlots, slot.register ≠ 0 ∧ slot.register ≠ 2#5 := by
    decide +kernel
  have reduce (slots : List FrameSlot) (t : CPU) (inside : slot ∈ slots)
      (unique : (slots.map FrameSlot.register).Nodup)
      (valid : ∀ q ∈ slots, q.register ≠ 0 ∧ q.register ≠ 2#5) :
      (slots.foldl (reloadSlot r) t).reg slot.register = t.mem.read64 (slot.address r t) := by
    induction slots generalizing t with
    | nil => simp at inside
    | cons head tail ih =>
      have hValid := valid head List.mem_cons_self
      have tValid (q : FrameSlot) (h : q ∈ tail) := valid q (List.mem_cons_of_mem _ h)
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.foldl_cons]
      rcases List.mem_cons.mp inside with same | remaining
      · subst head
        rw [reload_keeps _ _ _ _ (fun q h eq => unique.1 (List.mem_map.mpr ⟨q, h, eq⟩)),
          reloadSlot, reg_put, if_neg hValid.1, if_pos rfl]
      · rw [ih _ remaining unique.2 tValid, reloadSlot, memory_put, memory_advance, FrameSlot.address,
          reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0), if_neg (Ne.symm hValid.2), reg_advance]
        rfl
  exact reduce frameSlots s inFrame frame_registers_unique frameValid

theorem restoredFrame_slot (r : HmacRoutine) (s : CPU) (slot : FrameSlot) (inFrame : slot ∈ frameSlots)
    (saved : slot.register ≠ 2#5) :
    (restoredFrame r s).reg slot.register = s.mem.read64 (slot.address r s) := by
  simp only [restoredFrame, setPC_reg, reg_put, if_neg saved, reg_advance]
  have nonzero : ∀ slot ∈ frameSlots, slot.register ≠ 0 := by decide +kernel
  rw [if_neg (nonzero slot inFrame), readyReturn_slot _ _ _ inFrame]

theorem restoredFrame_pc (r : HmacRoutine) (s : CPU) :
    (restoredFrame r s).pc =
      s.mem.read64 (s.reg 2#5 + BitVec.ofNat 64 r.savedOffset) &&& ~~~(1 : Addr) := by
  let link : FrameSlot := ⟨0, 1#5⟩
  have atLink : link ∈ frameSlots := by decide +kernel
  have saved := readyReturn_slot r s link atLink
  change (readyReturn r s).reg 1#5 = _ at saved
  unfold restoredFrame
  rw [setPC_pc]
  change (readyReturn r s).reg 1#5 &&& _ = _
  rw [saved]
  simp [link, FrameSlot.address]

theorem restoredFrame_sp (r : HmacRoutine) (s : CPU) :
    (restoredFrame r s).reg 2#5 = s.reg 2#5 + BitVec.ofNat 64 r.frameSize := by
  simp only [restoredFrame, setPC_reg, reg_put]
  rw [if_neg (by decide : (2#5 : Reg) ≠ 0), if_true, readyReturn_sp]

theorem restoredFrame_memory (r : HmacRoutine) (s : CPU) :
    (restoredFrame r s).mem = s.mem := by
  simp only [restoredFrame, setPC_mem, memory_put, memory_advance, readyReturn_memory]

private theorem aligned_link (addr : Addr) (even : addr.toNat % 2 = 0) :
    addr &&& ~~~(1 : Addr) = addr := by
  have bit0 : addr &&& (1 : Addr) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change addr.toNat &&& (2 ^ 1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact even
  have ones : (1 : Addr) ||| ~~~(1 : Addr) = BitVec.allOnes 64 := by decide
  calc
    addr &&& ~~~(1 : Addr) = (addr &&& (1 : Addr)) ||| (addr &&& ~~~(1 : Addr)) := by
      rw [bit0]
      exact BitVec.zero_or.symm
    _ = addr &&& ((1 : Addr) ||| ~~~(1 : Addr)) := BitVec.and_or_distrib_left.symm
    _ = addr := by rw [ones, BitVec.and_allOnes]

set_option maxHeartbeats 1700000 in
/-- Restoring a prologue's actual stack record needs only the unchanged
save bytes and the original frame pointer. The body may use the other
stack slots and may invoke arbitrary callees preserving this footprint. -/
theorem epilogue_restores (r : HmacRoutine) (s body : CPU)
    (sp : body.reg 2#5 = (enteredFrame r s).reg 2#5)
    (linkAligned : (s.reg 1#5).toNat % 2 = 0)
    (saved : ∀ i : Fin 104,
      let p := body.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + i.val)
      body.mem.cells p = (enteredFrame r s).mem.cells p) :
    (restoredFrame r body).reg 2#5 = s.reg 2#5 ∧
    (restoredFrame r body).pc = s.reg 1#5 ∧
    ∀ i : Fin 13, (restoredFrame r body).reg (frameSlot i.val).register =
      s.reg (frameSlot i.val).register := by
  have nonSP : ∀ i : Fin 13, (frameSlot i.val).register ≠ 2#5 := by decide +kernel
  have savedWord (i : Fin 13) :
      body.mem.read64 (body.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * i.val)) =
        s.reg (frameSlot i.val).register := by
    calc
      _ = (enteredFrame r s).mem.read64
          (body.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * i.val)) := by
        refine read64_eq_of_cells _ ?_
        intro j
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        simpa only [Nat.add_assoc] using
          saved ⟨8 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
      _ = _ := by
        rw [sp, enteredFrame_sp]
        exact enteredFrame_slot r s i
  refine ⟨?_, ?_, ?_⟩
  · rw [restoredFrame_sp, sp, enteredFrame_sp, BitVec.sub_add_cancel]
  · rw [restoredFrame_pc, show body.reg 2#5 + BitVec.ofNat 64 r.savedOffset =
      body.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * (⟨0, by decide⟩ : Fin 13).val) from by simp,
      savedWord ⟨0, by decide⟩]
    exact aligned_link _ linkAligned
  · intro i
    rw [restoredFrame_slot _ _ _ (frameSlot_mem i) (nonSP i), FrameSlot.address, frameSlot_index i]
    exact savedWord i

end Crypto.HMACSHA256.RISCV64
