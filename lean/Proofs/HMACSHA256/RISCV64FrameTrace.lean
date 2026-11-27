import Proofs.HMACSHA256.RISCV64FramePermissions

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

def spillEvents (r : HmacRoutine) (saving : Bool) (sp pc : Addr) : List FrameSlot → List (List Access)
  | [] => []
  | slot :: tail =>
    let p := sp + BitVec.ofNat 64 (r.savedOffset + 8 * slot.index)
    [.fetch pc 2, if saving then .write p .double else .read p .double] ::
      spillEvents r saving sp (pc + 2#64) tail

private def transferSlot (r : HmacRoutine) (saving : Bool) (slot : FrameSlot) : Op :=
  if saving then saveOne r slot else loadOne r slot

private theorem observe_slot (r : HmacRoutine) (saving : Bool) (s : CPU) (slot : FrameSlot) :
    (transferSlot r saving slot).accesses s =
      [.fetch s.pc 2, if saving then .write (slot.address r s) .double else .read (slot.address r s) .double] := by
  cases saving <;> rfl

private theorem slot_preserves_sp (r : HmacRoutine) (saving : Bool) (s : CPU) (slot : FrameSlot)
    (other : slot.register ≠ 2#5) :
    ((transferSlot r saving slot).step s).reg 2#5 = s.reg 2#5 := by
  cases saving
  · simp (config := {decide := true}) only [transferSlot, Bool.false_eq_true, if_false,
      loadOne, Op.step, Instruction.step, reg_put, reg_advance, if_neg (Ne.symm other)]
  · rfl

private theorem observe_slots (r : HmacRoutine) (saving : Bool) (s : CPU) (slots : List FrameSlot)
    (fixed : ∀ slot ∈ slots, slot.register ≠ 2#5) :
    runOpsEvents (slots.map (transferSlot r saving)) s = spillEvents r saving (s.reg 2#5) s.pc slots := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot tail ih =>
    let op := transferSlot r saving slot
    have same := slot_preserves_sp r saving s slot (fixed _ List.mem_cons_self)
    have next : (op.step s).pc = s.pc + 2#64 := by cases saving <;> rfl
    change op.accesses s :: runOpsEvents (tail.map (transferSlot r saving)) (op.step s) = _
    rw [observe_slot, ih _ (fun i hi => fixed i (List.mem_cons_of_mem _ hi)), same, next]
    rfl

private theorem frame_slots_avoid_sp : ∀ slot ∈ frameSlots, slot.register ≠ 2#5 := by
  have checked : ∀ i : Fin frameSlots.length, frameSlots[i.val].register ≠ 2#5 := by decide +kernel
  intro slot present
  obtain ⟨i, valid, eq⟩ := List.mem_iff_getElem.mp present
  exact eq ▸ checked ⟨i,valid⟩

def prologueEvents (r : HmacRoutine) (pc sp : Addr) : List (List Access) :=
  [.fetch pc 2] :: spillEvents r true (sp - BitVec.ofNat 64 r.frameSize) (pc + 2#64) frameSlots

def epilogueEvents (r : HmacRoutine) (pc sp : Addr) : List (List Access) :=
  spillEvents r false sp pc frameSlots ++ [[.fetch (pc + 26#64) 2], [.fetch (pc + 28#64) 2]]

set_option maxRecDepth 8192 in
theorem enter_events (r : HmacRoutine) (s : CPU) :
    runOpsEvents (enterCode r) s = prologueEvents r s.pc (s.reg 2#5) := by
  let reserve : Op := .scalar ⟨.addi 2#5 2#5 (-BitVec.ofNat 64 r.frameSize), 2⟩
  change [.fetch s.pc 2] :: runOpsEvents (frameSlots.map (transferSlot r true)) (reserve.step s) = _
  rw [observe_slots r true _ _ frame_slots_avoid_sp]
  have sp : (reserve.step s).reg 2#5 = s.reg 2#5 - BitVec.ofNat 64 r.frameSize := by
    simp (config := {decide := true}) [reserve, Op.step, Instruction.step, reg_put, BitVec.sub_eq_add_neg]
  rw [sp]
  rfl

private theorem runOpsEvents_append (a b : List Op) (s : CPU) :
    runOpsEvents (a ++ b) s = runOpsEvents a s ++ runOpsEvents b (runOps a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons op tail ih =>
    change _ :: runOpsEvents (tail ++ b) (op.step s) = _
    rw [ih]
    rfl

private theorem restore_slot_pc (r : HmacRoutine) (s : CPU) (slots : List FrameSlot) :
    (runOps (slots.map (loadOne r)) s).pc = s.pc + BitVec.ofNat 64 (2 * slots.length) := by
  induction slots generalizing s with
  | nil => simp [runOps]
  | cons slot rest ih =>
    let next := (loadOne r slot).step s
    change (runOps (rest.map (loadOne r)) next).pc = _
    rw [ih next, show next.pc = s.pc + 2#64 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    simp only [List.length_cons, Nat.mul_succ]
    omega

set_option maxRecDepth 8192 in
theorem return_events (r : HmacRoutine) (s : CPU) :
    runOpsEvents (returnCode r) s = epilogueEvents r s.pc (s.reg 2#5) := by
  unfold returnCode
  rw [runOpsEvents_append]
  change runOpsEvents (frameSlots.map (transferSlot r false)) s ++ _ = _
  rw [observe_slots _ _ _ _ frame_slots_avoid_sp]
  let after := runOps (frameSlots.map (loadOne r)) s
  have pc : after.pc = s.pc + 26#64 := restore_slot_pc r s frameSlots
  change _ ++ [[Access.fetch after.pc 2], [Access.fetch (after.pc + 2#64) 2]] = _
  rw [pc, BitVec.add_assoc]
  rfl

end Crypto.HMACSHA256.RISCV64
