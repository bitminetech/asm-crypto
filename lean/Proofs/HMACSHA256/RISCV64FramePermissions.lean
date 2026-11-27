import Proofs.HMACSHA256.RISCV64Frame
import Proofs.HMACSHA256.RISCV64Ranges

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

private theorem decode_cons {r : Routine} {off count : Nat} {op : Op} {tail : List Op}
    (decoded : decodeRange r off (count + 1) = some (op :: tail)) :
    decodeAt r off = some op ∧ decodeRange r (off + op.width) count = some tail := by
  cases hd : decodeAt r off with
  | none => simp [decodeRange, hd] at decoded
  | some head =>
    cases tl : decodeRange r (off + head.width) count with
    | none => simp [decodeRange, hd, tl] at decoded
    | some rest =>
      have eq : head = op ∧ rest = tail := by simpa [decodeRange, hd, tl] using decoded
      obtain ⟨rfl,rfl⟩ := eq
      exact ⟨rfl, tl⟩

private def slotOp (r : HmacRoutine) (saving : Bool) (slot : FrameSlot) : Op :=
  if saving then saveOne r slot else loadOne r slot

private def slotAccess (r : HmacRoutine) (saving : Bool) (s : CPU) (slot : FrameSlot) : Access :=
  if saving then .write (slot.address r s) .double else .read (slot.address r s) .double

private theorem slot_width (r : HmacRoutine) (saving : Bool) (slot : FrameSlot) :
    (slotOp r saving slot).width = 2 := by cases saving <;> rfl

private theorem slot_accesses (r : HmacRoutine) (saving : Bool) (s : CPU) (slot : FrameSlot) :
    (slotOp r saving slot).accesses s = [.fetch s.pc 2, slotAccess r saving s slot] := by
  cases saving <;> rfl

private theorem slot_step (r : HmacRoutine) (saving : Bool) (s : CPU) (slot : FrameSlot)
    (preserved : slot.register ≠ 2#5) :
    ((slotOp r saving slot).step s).pc = s.pc + 2#64 ∧
      ((slotOp r saving slot).step s).reg 2#5 = s.reg 2#5 := by
  cases saving <;>
    simp (config := {decide := true}) only [slotOp, Bool.false_eq_true, if_false, if_true,
      saveOne, loadOne, Op.step, Instruction.step, pc_put, pc_write, pc_advance,
      reg_write, reg_advance, reg_put, Ne.symm preserved, and_true]

private theorem ready_slots (r : HmacRoutine) (saving : Bool) (base : Addr) (initial : Memory) (s : CPU)
    (off : Nat) (slots : List FrameSlot)
    (pc : s.pc = routineAddress base r.image + BitVec.ofNat 64 off)
    (within : off + 2 * slots.length ≤ r.image.image.size)
    (bounded : r.image.image.size < 2 ^ 64)
    (even : off % 2 = 0) (codeAligned : (routineAddress base r.image).toNat % 2 = 0)
    (exec : initial.canExec (routineAddress base r.image) r.image.image.size = true)
    (decoded : decodeRange r.image off slots.length = some (slots.map (slotOp r saving)))
    (fixed : ∀ slot ∈ slots, slot.register ≠ 2#5)
    (access : ∀ slot ∈ slots, (slotAccess r saving s slot).permitted initial = true) :
    RangeReady r.image base initial off s (slots.map (slotOp r saving)) := by
  induction slots generalizing off s with
  | nil => trivial
  | cons slot tail ih =>
    obtain ⟨head, later⟩ := decode_cons decoded
    let op := slotOp r saving slot
    have width : op.width = 2 := slot_width _ _ _
    have effect := slot_step r saving s slot (fixed slot (List.mem_cons_self ..))
    simp only [List.length_cons] at within
    have span : off + 2 ≤ r.image.image.size := by omega
    have fetch := fetch_of_grant (m := initial) codeAligned span even exec
    have data := access slot (List.mem_cons_self ..)
    refine ⟨pc, by omega, head, by rw [width]; decide, by rw [width]; exact span, ?_, ?_⟩
    · rw [slot_accesses, pc]
      simp [fetch, data]
    · rw [width] at later ⊢
      apply ih
      · rw [effect.1, pc, BitVec.add_assoc, BitVec.ofNat_add]
      · omega
      · omega
      · exact later
      · intro x present
        exact fixed x (List.mem_cons_of_mem _ present)
      · intro x present
        have same : slotAccess r saving (op.step s) x = slotAccess r saving s x := by
          have pointer : x.address r (op.step s) = x.address r s := by
            unfold FrameSlot.address
            rw [show (op.step s).reg 2#5 = s.reg 2#5 from effect.2]
          simp only [slotAccess, pointer]
        rw [same]
        exact access x (List.mem_cons_of_mem _ present)

private theorem slot_index_bound (slot : FrameSlot) (h : slot ∈ frameSlots) : slot.index < 13 := by
  have checked : ∀ i : Fin frameSlots.length, (frameSlots[i.val]).index < 13 := by decide +kernel
  obtain ⟨i, within, eq⟩ := List.mem_iff_getElem.mp h
  exact eq ▸ checked ⟨i,within⟩

private theorem slot_fixed (slot : FrameSlot) (h : slot ∈ frameSlots) : slot.register ≠ 2#5 := by
  have checked : ∀ i : Fin frameSlots.length, (frameSlots[i.val]).register ≠ 2#5 := by decide +kernel
  obtain ⟨i, within, eq⟩ := List.mem_iff_getElem.mp h
  exact eq ▸ checked ⟨i,within⟩

private theorem ready_append {r : Routine} {base : Addr} {m : Memory} {pc : Nat}
    {s : CPU} {a b : List Op}
    (first : RangeReady r base m pc s a)
    (rest : RangeReady r base m (pc + (a.map Op.width).sum) (runOps a s) b) :
    RangeReady r base m pc s (a ++ b) := by
  induction a generalizing pc s with
  | nil => exact rest
  | cons op tail ih =>
    obtain ⟨atPC, address, decoded, width, within, allowed, next⟩ := first
    refine ⟨atPC, address, decoded, width, within, allowed, ih next ?_⟩
    have size : pc + ((op :: tail).map Op.width).sum =
        pc + op.width + (tail.map Op.width).sum := by simp [Nat.add_assoc]
    rw [size] at rest
    exact rest

private theorem slot_pc_after (r : HmacRoutine) (saving : Bool) (s : CPU) (slots : List FrameSlot)
    (fixed : ∀ slot ∈ slots, slot.register ≠ 2#5) :
    (runOps (slots.map (slotOp r saving)) s).pc = s.pc + BitVec.ofNat 64 (2 * slots.length) := by
  induction slots generalizing s with
  | nil => simp [runOps]
  | cons slot tail ih =>
    let op := slotOp r saving slot
    have effect := slot_step r saving s slot (fixed slot (List.mem_cons_self ..))
    change (runOps (tail.map (slotOp r saving)) (op.step s)).pc = _
    rw [ih _ (fun x hx => fixed x (List.mem_cons_of_mem _ hx)), effect.1, BitVec.add_assoc, ← BitVec.ofNat_add]
    have length : 2 + 2 * tail.length = 2 * (slot :: tail).length := by
      simp only [List.length_cons]
      omega
    rw [length]

private theorem frame_slot_fits (r : HmacRoutine) (slot : FrameSlot) (seen : slot ∈ frameSlots) :
    r.savedOffset + 8 * slot.index + 8 ≤ r.frameSize ∧
      (r.savedOffset + 8 * slot.index) % 8 = 0 := by
  have bound := slot_index_bound slot seen
  cases r <;> simp only [HmacRoutine.frameSize, HmacRoutine.savedOffset] <;> omega

private theorem frame_sizes (r : HmacRoutine) :
    2 + 2 * frameSlots.length ≤ r.image.image.size ∧
    r.returnOffset + 2 * frameSlots.length + 4 ≤ r.image.image.size ∧
    r.image.image.size < 2 ^ 64 ∧ r.returnOffset % 2 = 0 := by
  cases r <;> decide +kernel

set_option maxRecDepth 8192 in
theorem frame_prologue_allowed (r : HmacRoutine) (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base r.image)
    (codeAligned : (routineAddress base r.image).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base r.image) r.image.image.size = true)
    (writeAligned : (s.reg 2#5 - BitVec.ofNat 64 r.frameSize).toNat % 8 = 0)
    (writable : s.mem.canWrite (s.reg 2#5 - BitVec.ofNat 64 r.frameSize) r.frameSize = true) :
    RangeAllowed r.image base 0 14 s := by
  let op : Op := .scalar ⟨.addi 2#5 2#5 (-BitVec.ofNat 64 r.frameSize), 2⟩
  obtain ⟨prefixFits, _, bounded, _⟩ := frame_sizes r
  have decoded : decodeRange r.image (0 + op.width) frameSlots.length =
      some (frameSlots.map (slotOp r true)) ∧ decodeAt r.image 0 = some op := by
    have whole : decodeRange r.image 0 (frameSlots.length + 1) =
        some (op :: frameSlots.map (slotOp r true)) := entered_decoded r
    exact (decode_cons whole).symm
  have frameFits : 0 + 2 ≤ r.image.image.size := by omega
  have fetch := fetch_of_grant (off := 0) (width := 2) codeAligned frameFits rfl exec
  have next : (op.step s).pc = routineAddress base r.image + BitVec.ofNat 64 2 := by
    change s.pc + 2#64 = _
    rw [pc]
  have sp : (op.step s).reg 2#5 = s.reg 2#5 - BitVec.ofNat 64 r.frameSize := by
    change ((s.advance 2).put 2#5 (s.reg 2#5 + (-BitVec.ofNat 64 r.frameSize))).reg 2#5 = _
    rw [reg_put, if_neg (by decide : (2#5 : Reg) ≠ 0), if_pos rfl, BitVec.sub_eq_add_neg]
  refine ⟨enterCode r, entered_decoded r, ?_⟩
  refine ⟨by simpa only [BitVec.add_zero] using pc,
    by decide, decoded.2, by change 0 < 2; decide, frameFits, ?_, ?_⟩
  · change ((Access.fetch s.pc 2).permitted s.mem && true) = true
    rw [pc, Bool.and_true]
    simpa only [BitVec.add_zero] using fetch
  · change RangeReady r.image base s.mem 2 (op.step s) (frameSlots.map (slotOp r true))
    refine ready_slots r true base s.mem (op.step s) 2 frameSlots next prefixFits bounded
      (by decide) codeAligned exec decoded.1 slot_fixed ?_
    intro slot isSlot
    change (Access.write ((op.step s).reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * slot.index))
      .double).permitted s.mem = true
    rw [sp]
    exact write_of_grant writeAligned (frame_slot_fits r slot isSlot).1
      (frame_slot_fits r slot isSlot).2 writable

private theorem frame_return_decoded (r : HmacRoutine) :
    decodeRange r.image r.returnOffset frameSlots.length = some (frameSlots.map (slotOp r false)) ∧
    decodeAt r.image (r.returnOffset + 2 * frameSlots.length) =
      some (.scalar ⟨.addi 2#5 2#5 (BitVec.ofNat 64 r.frameSize), 2⟩) ∧
    decodeAt r.image (r.returnOffset + 2 * frameSlots.length + 2) = some (.scalar ⟨.ret, 2⟩) := by
  cases r <;> decide +kernel

private theorem slot_bytes (r : HmacRoutine) (saving : Bool) (slots : List FrameSlot) :
    (((slots.map (slotOp r saving)).map Op.width).sum) = 2 * slots.length := by
  induction slots with
  | nil => rfl
  | cons slot tail ih =>
    simp only [List.map_cons, List.sum_cons, slot_width, List.length_cons, ih]
    omega

set_option maxRecDepth 8192 in
theorem frame_epilogue_allowed (r : HmacRoutine) (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base r.image + BitVec.ofNat 64 r.returnOffset)
    (codeAligned : (routineAddress base r.image).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base r.image) r.image.image.size = true)
    (readAligned : (s.reg 2#5).toNat % 8 = 0)
    (readable : s.mem.canRead (s.reg 2#5) r.frameSize = true) :
    RangeAllowed r.image base r.returnOffset 15 s := by
  let restored := frameSlots.map (slotOp r false)
  let adjust : Op := .scalar ⟨.addi 2#5 2#5 (BitVec.ofNat 64 r.frameSize), 2⟩
  let ret : Op := .scalar ⟨.ret, 2⟩
  let tail := r.returnOffset + 2 * frameSlots.length
  obtain ⟨_, tailFits, bounded, even⟩ := frame_sizes r
  obtain ⟨decoding, adjustDecoded, retDecoded⟩ := frame_return_decoded r
  have grantSlots : RangeReady r.image base s.mem r.returnOffset s restored := by
    refine ready_slots r false base s.mem s r.returnOffset frameSlots pc (by omega) bounded
      even codeAligned exec decoding slot_fixed ?_
    intro slot isSlot
    change (Access.read (s.reg 2#5 + BitVec.ofNat 64 (r.savedOffset + 8 * slot.index))
      .double).permitted s.mem = true
    exact read_of_grant readAligned (frame_slot_fits r slot isSlot).1
      (frame_slot_fits r slot isSlot).2 readable
  let mid := runOps restored s
  have midPC : mid.pc = routineAddress base r.image + BitVec.ofNat 64 tail := by
    rw [show mid.pc = _ from slot_pc_after r false s frameSlots slot_fixed, pc,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have rPC : (adjust.step mid).pc = routineAddress base r.image + BitVec.ofNat 64 (tail + 2) := by
    change mid.pc + 2#64 = _
    rw [midPC, BitVec.add_assoc, BitVec.ofNat_add tail 2]
  have aexec := fetch_of_grant (off := tail) (width := 2) codeAligned
    (by dsimp [tail]; omega) (by dsimp [tail]; omega) exec
  have rexec := fetch_of_grant (off := tail + 2) (width := 2) codeAligned
    (by dsimp [tail]; omega) (by dsimp [tail]; omega) exec
  refine ⟨returnCode r, returned_decoded r, ?_⟩
  change RangeReady r.image base s.mem r.returnOffset s (restored ++ [adjust, ret])
  apply ready_append grantSlots
  change RangeReady r.image base s.mem (r.returnOffset + ((frameSlots.map (slotOp r false)).map Op.width).sum)
    mid [adjust, ret]
  rw [slot_bytes]
  change RangeReady r.image base s.mem tail mid [adjust, ret]
  refine ⟨midPC, by dsimp [tail]; omega, adjustDecoded, by change 0 < 2; decide,
    by change tail + 2 ≤ r.image.image.size; dsimp [tail]; omega, ?_,
    rPC, by change tail + 2 < 2 ^ 64; dsimp [tail]; omega, retDecoded, by decide,
    by change tail + 2 + 2 ≤ r.image.image.size; dsimp [tail]; omega, ?_, trivial⟩
  · change ((Access.fetch mid.pc 2).permitted s.mem && true) = true
    rw [midPC, Bool.and_true]
    exact aexec
  · change ((Access.fetch (adjust.step mid).pc 2).permitted s.mem && true) = true
    rw [rPC, Bool.and_true]
    exact rexec

end Crypto.HMACSHA256.RISCV64
