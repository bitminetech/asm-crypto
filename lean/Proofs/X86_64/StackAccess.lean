import Proofs.X86_64.SerialContract
import Proofs.X86_64.MemoryEffect

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset)

def stackOffset (pc : Nat) (a : AccessForm) : Nat :=
  (BitVec.ofNat 64 (504 - stackDepth pc) + a.ea.disp).toNat

private def stackFormChecked (pc : Nat) (a : AccessForm) : Bool :=
  if directStack a then
    let offset := stackOffset pc a
    decide (offset + a.bytes ≤ 512 ∧
      (a.write = true → offset + a.bytes ≤ 504) ∧
      (504 - stackDepth pc ≤ offset ∨
        (pc < 10 ∧ a.write = true ∧ offset + 8 = 504 - stackDepth pc)))
  else true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem stack_forms_checked : codeLayout.all (fun p =>
    ((accessForms p.2).getD []).all (stackFormChecked p.1)) = true := by decide +kernel

private theorem stack_depth_bound (off : Nat) : stackDepth off ≤ 504 := by
  unfold stackDepth
  split <;> decide

private theorem direct_stack_address {base : Val} {entry current : Cpu} {i : Instr} {a : AccessForm}
    (sp : current.regs.get .rsp = entry.regs.get .rsp -
      BitVec.ofNat 64 (stackDepth (current.rip-base).toNat))
    (direct : directStack a) :
    (a.eval current (current.rip + BitVec.ofNat 64 i.len)).address =
      frameBase entry + BitVec.ofNat 64 (stackOffset (current.rip-base).toNat a) := by
  let d := stackDepth (current.rip-base).toNat
  let offset := stackOffset (current.rip-base).toNat a
  have depth : d ≤ 504 := stack_depth_bound _
  have rsp : current.regs.get .rsp = frameBase entry + BitVec.ofNat 64 (504-d) := by
    have origin : frameBase entry+504 = entry.regs.get .rsp := BitVec.sub_add_cancel _ _
    have sum : (504 : Val) = BitVec.ofNat 64 (504-d) + BitVec.ofNat 64 d := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel depth]
      rfl
    calc
      current.regs.get .rsp = (frameBase entry+504)-BitVec.ofNat 64 d := by
        rw [origin]; exact sp
      _ = _ := by rw [sum, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  obtain ⟨b,idx,rip,seg⟩ := direct
  simp only [AccessForm.eval, Ea.addr, seg, Ea.offset, b, idx, rip, rsp]
  change frameBase entry + BitVec.ofNat 64 (504-d) + 0 + a.ea.disp =
    frameBase entry + BitVec.ofNat 64 ((BitVec.ofNat 64 (504-d) + a.ea.disp).toNat)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp [BitVec.add_assoc]

/-- A direct RSP access lies in the live frame including the incoming return
slot. A PUSH may write exactly its eight-byte acquisition below RSP. -/
theorem direct_stack_operand {base : Val} {entry current : Cpu} {i : Instr} {a : AccessForm}
    (site : ((current.rip-base).toNat, i) ∈ codeLayout)
    (present : a ∈ (accessForms i).getD [])
    (sp : current.regs.get .rsp = entry.regs.get .rsp -
      BitVec.ofNat 64 (stackDepth (current.rip-base).toNat))
    (direct : directStack a)
    (valid : (stackRegion entry).Valid)
    {p : Val} (touched : DataByte (a.eval current (current.rip + BitVec.ofNat 64 i.len)) p) :
    (stackRegion entry).Contains p ∧
      (a.write = true → (Region.mk (frameBase entry) 504).Contains p) ∧
      (504 - stackDepth (current.rip-base).toNat ≤ stackOffset (current.rip-base).toNat a ∨
        ((current.rip-base).toNat < 10 ∧ a.write = true ∧
          stackOffset (current.rip-base).toNat a + 8 = 504 - stackDepth (current.rip-base).toNat)) := by
  have check := List.all_eq_true.mp (List.all_eq_true.mp stack_forms_checked _ site) a present
  simp only [stackFormChecked, if_pos direct, decide_eq_true_eq] at check
  obtain ⟨j,hj,rfl⟩ := touched
  let offset := stackOffset (current.rip-base).toNat a
  have address := direct_stack_address (i := i) sp direct
  rw [address, BitVec.add_assoc, ← BitVec.ofNat_add]
  have within := check.1
  change offset+a.bytes ≤ 512 at within
  change j < a.bytes at hj
  refine ⟨caller_region_contains_offset _ valid (offset+j) (by change offset+j < 512; omega),
    fun writes => caller_region_contains_offset _ ?_ (offset+j) ?_, check.2.2⟩
  · change (frameBase entry).toNat + 512 ≤ 2^64 at valid
    change (frameBase entry).toNat + 504 ≤ 2^64
    omega
  · have within := check.2.1 writes
    change offset+a.bytes ≤ 504 at within
    change j < a.bytes at hj
    change offset+j < 504
    omega

/-- Independent read, write and canonicality grants for the stack reservation.
The incoming return slot only needs read permission. -/
structure StackGrants (entry : Cpu) (authority : Authority) : Prop where
  readable : ∀ p, (stackRegion entry).Contains p → authority.readable p
  writable : ∀ p, (Region.mk (frameBase entry) 504).Contains p → authority.writable p
  canonical : ∀ p, (stackRegion entry).Contains p → X86.canonical p = true

def DirectStackAuthorized (base : Val) (entry : Cpu) (authority : Authority)
    (event : Val × Instr × List DataAccess) : Prop :=
  ∀ a ∈ (accessForms event.2.1).getD [], directStack a →
    ∃ access ∈ event.2.2, access.write = a.write ∧ access.bytes = a.bytes ∧
      access.address = frameBase entry + BitVec.ofNat 64 (stackOffset (event.1-base).toNat a) ∧
      ∀ p, DataByte access p → X86.canonical p = true ∧
        if access.write then authority.writable p else authority.readable p

attribute [local irreducible] X86.step

private theorem direct_stack_event {base : Val} {entry current : Cpu} {i : Instr} {accesses : List DataAccess}
    (layout : ((current.rip-base).toNat,i) ∈ codeLayout) (leaf : ScalarLeaf i)
    (obs : dataAccesses i current = some accesses)
    (sp : current.regs.get .rsp = entry.regs.get .rsp -
      BitVec.ofNat 64 (stackDepth (current.rip-base).toNat))
    (valid : (stackRegion entry).Valid) (authority : Authority) (grants : StackGrants entry authority) :
    DirectStackAuthorized base entry authority (current.rip,i,accesses) := by
  intro form present direct
  have source := dataAccesses_forms i current leaf
  rw [obs] at source
  cases h : accessForms i with
  | none => simp [h] at present
  | some list =>
    rw [h, Option.getD_some] at present
    rw [h] at source
    have accessEq := Option.some.inj source
    let access := form.eval current (current.rip + BitVec.ofNat 64 i.len)
    have member : access ∈ accesses := by rw [accessEq]; exact List.mem_map_of_mem present
    have address : access.address = frameBase entry + BitVec.ofNat 64 (stackOffset (current.rip-base).toNat form) := by
      unfold access
      exact direct_stack_address sp direct
    refine ⟨access,member,rfl,rfl,address,?_⟩
    intro p bytes
    have ⟨range,writeRange,_⟩ := direct_stack_operand layout (by simpa [h] using present) sp direct valid bytes
    refine ⟨grants.canonical p range,?_⟩
    change if form.write then authority.writable p else authority.readable p
    by_cases writes : form.write = true
    · simpa only [if_pos writes] using grants.writable _ (writeRange writes)
    · simpa only [if_neg writes] using grants.readable _ range

private theorem observed_stack_authorized {base : Val} {entry s out : Cpu} {events}
    (run : ObservedExecution base s events out) (valid : (stackRegion entry).Valid)
    (sites : ∀ e ∈ events, ((e.1-base).toNat,e.2.1) ∈ codeLayout)
    (depths : stackTrace (events.map (fun e => e.2.1)) s =
      events.map (fun e => entry.regs.get .rsp - BitVec.ofNat 64 (stackDepth (e.1-base).toNat)))
    (authority : Authority) (grants : StackGrants entry authority) :
    ∀ e ∈ events, DirectStackAuthorized base entry authority e := by
  induction run with
  | nil => simp
  | @cons s next out i accesses tail fetched executed obs rest ih =>
    have one : X86.step i s = next := by
      cases stopped : s.stopped with
      | false => simpa [stepLoaded, stopped, fetched, guard] using executed
      | true => simp [stepLoaded, stopped, guard] at executed
    simp only [List.map_cons, stackTrace, List.cons.injEq, one] at depths
    intro e member
    rcases List.mem_cons.mp member with rfl | later
    · exact direct_stack_event (sites _ List.mem_cons_self) (fetched_scalar fetched) obs depths.1 valid authority grants
    · exact ih (fun e h => sites e (List.mem_cons_of_mem _ h)) depths.2 e later

/-- Every direct stack operand in the actual fetched call has the granted
permissions and a canonical address. Indexed stack operands have separate
index bounds in the corresponding loops. -/
theorem sha256_direct_stack_authorized {base s message extent} (entry : CallerEntry base s message extent)
    (authority : Authority) (grants : StackGrants s authority) :
    ∃ out trace observations events, SerialContract base s out message trace observations ∧
      ObservedExecution base s events out ∧ ∀ e ∈ events, DirectStackAuthorized base s authority e := by
  obtain ⟨out,trace,observations,call⟩ := sha256_serial_contract entry
  obtain ⟨events,run,code,_⟩ := call.executed.observe
  have instr := congrArg (List.map Prod.snd) code
  simp only [List.map_map, Function.comp_def] at instr
  refine ⟨out,trace,observations,events,call,run,observed_stack_authorized run entry.stackValid ?_ ?_ authority grants⟩
  · intro e member
    exact call.layout (e.1,e.2.1) (code ▸ List.mem_map_of_mem member)
  · rw [instr,call.exactStack,← code,List.map_map]
    rfl

end Crypto.X86_64
