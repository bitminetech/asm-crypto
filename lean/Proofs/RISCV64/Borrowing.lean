import Proofs.RISCV64.Caller
import Proofs.RISCV64.Scheduling
import Proofs.Borrow

namespace Crypto.RISCV64

open Crypto.Baseline (Region BorrowScope AccessEvent CallAccess EnvironmentAccess DataRace borrow_accesses_race_free)
open Crypto.ARM64.Imported (address_reconstruct caller_region_contains_offset memoryBytes32)

def callBorrow (base : Addr) (s : CPU) (extent : Nat) : BorrowScope where
  shared p := (callerInput s extent).Contains p ∨ (callerImage base).Contains p
  exclusive p := (callerStack s).Contains p ∨ (callerOutput s).Contains p

private theorem InRegion.byte_inside {r : Region} {p : Addr} {length : Nat} {w : Width}
    (fits : InRegion r.base length p w) (valid : r.Valid) (size : length ≤ r.bytes)
    (j : Nat) (hj : j < w.bytes) : r.Contains (p + BitVec.ofNat 64 j) := by
  obtain ⟨off, bound, _, rfl⟩ := fits
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact caller_region_contains_offset r valid _ (by omega)

private theorem within_data_borrow {base : Addr} {s : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) {a : Access} (inside : CallData base s message.bytes.size a) :
    a.Within (callBorrow base s extent).protected := by
  cases a with
  | fetch => exact inside.elim
  | write addr w =>
    intro i hi
    change i < w.bytes at hi
    change (callBorrow base s extent).protected (addr + BitVec.ofNat 64 i)
    rcases inside with stack | output
    · exact .inr (.inl (stack.byte_inside (r := callerStack s) entry.stackValid (Nat.le_refl 480) i hi))
    · exact .inr (.inr (output.byte_inside (r := callerOutput s) entry.outputValid (Nat.le_refl 32) i hi))
  | read addr w =>
    intro i hi
    change i < w.bytes at hi
    change (callBorrow base s extent).protected (addr + BitVec.ofNat 64 i)
    rcases inside with stack | header | payload | imageRange
    · exact .inr (.inl (stack.byte_inside (r := callerStack s) entry.stackValid (Nat.le_refl 480) i hi))
    · have bound : 24 ≤ (callerInput s extent).bytes := by
        obtain ⟨minOffset, _, fits, _⟩ := entry.layout
        change 24 ≤ extent
        have := entry.accessible
        omega
      exact .inl (.inl (header.byte_inside (r := callerInput s extent) entry.inputValid bound i hi))
    · have baseInput : inputPayload s = (callerInput s extent).base + BitVec.ofNat 64 message.offset := by
        unfold inputPayload
        rw [entry.offsetValue]
        rfl
      rw [baseInput] at payload
      have fits : message.offset + message.bytes.size ≤ (callerInput s extent).bytes := by
        obtain ⟨_, _, minSize, countFits⟩ := entry.layout
        change _ ≤ extent
        have := entry.accessible
        omega
      have aligned : message.offset % w.bytes = 0 := by
        have := entry.layout.2.1
        cases w <;> simp only [Width.bytes] <;> omega
      exact .inl (.inl ((payload.enclose fits aligned).byte_inside (r := callerInput s extent)
        entry.inputValid (Nat.le_refl _) i hi))
    · exact .inl (.inr (imageRange.byte_inside (r := callerImage base) entry.imageValid (Nat.le_refl _) i hi))

private theorem ImageExecution.fetchBytes {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution base s code out) {addr : Addr} {size : Nat}
    (found : Access.fetch addr size ∈ accessTrace code s) (j : Nat) (hj : j < size) :
    ∃ i < codeEnd, addr + BitVec.ofNat 64 j = base + BitVec.ofNat 64 i := by
  induction path with
  | nil => simp [accessTrace] at found
  | @cons s out i tail decoded last rest ih =>
    simp only [accessTrace, Instruction.observations, List.cons_append, List.mem_cons, List.mem_append] at found
    rcases found with here | operand | later
    · obtain ⟨rfl, rfl⟩ := Access.fetch.inj here
      have fits := (decodeAt_range decoded).2
      refine ⟨(s.pc-base).toNat+j, by omega, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, address_reconstruct base s.pc]
    · cases op : i.op <;> simp [Op.accesses, op] at operand
    · exact ih later

private theorem covers_image (base : Addr) (s : CPU) (extent : Nat) (valid : (callerImage base).Valid)
    (j : Nat) (inside : j < image.size) : (callBorrow base s extent).protected (base+BitVec.ofNat 64 j) :=
  .inl (.inr (caller_region_contains_offset (callerImage base) valid j inside))

theorem call_access_borrow {base : Addr} {s out : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) (path : ImageExecution base s (callCode message.bytes.size) out)
    (a : Access) (observed : a ∈ accessTrace (callCode message.bytes.size) s) :
    a.Within (callBorrow base s extent).protected := by
  cases a with
  | fetch address bytes =>
    intro j hj
    obtain ⟨i, fit, pos⟩ := path.fetchBytes observed j hj
    change (callBorrow base s extent).protected (address+BitVec.ofNat 64 j)
    rw [pos]
    apply covers_image base s extent entry.imageValid
    have fits : codeEnd ≤ image.size := by decide +kernel
    omega
  | read addr w =>
    apply within_data_borrow entry
    apply call_data_footprint base s message.bytes entry.decoded_layout.1
    rw [dataTrace_eq]
    exact List.mem_filter.mpr ⟨observed, rfl⟩
  | write addr w =>
    apply within_data_borrow entry
    apply call_data_footprint base s message.bytes entry.decoded_layout.1
    rw [dataTrace_eq]
    exact List.mem_filter.mpr ⟨observed, rfl⟩

def memoryEvent (a : Access) : AccessEvent where
  reads p := match a with
    | .fetch .. | .read .. => ∃ j < a.span.2, p = a.span.1 + BitVec.ofNat 64 j
    | .write .. => False
  writes p := match a with
    | .write .. => ∃ j < a.span.2, p = a.span.1 + BitVec.ofNat 64 j
    | _ => False
  releases _ := False
  changesProtection _ := False

theorem borrowed_access_safe {base : Addr} {s out : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) (path : ImageExecution base s (callCode message.bytes.size) out)
    (a : Access) (observed : a ∈ accessTrace (callCode message.bytes.size) s) :
    CallAccess (callBorrow base s extent) (memoryEvent a) := by
  refine ⟨?_, ?_, fun _ h => h, fun _ h => h⟩
  · intro p read
    have within := call_access_borrow entry path a observed
    cases a with
    | write => exact read.elim
    | read | fetch =>
      obtain ⟨j, bound, rfl⟩ := read
      exact within j bound
  · intro p wrote
    cases a with
    | read | fetch => exact wrote.elim
    | write addr w =>
      obtain ⟨j, bound, rfl⟩ := wrote
      have inData : Access.write addr w ∈ dataTrace (callCode message.bytes.size) s := by
        rw [dataTrace_eq]
        exact List.mem_filter.mpr ⟨observed, rfl⟩
      have place := call_data_footprint base s message.bytes entry.decoded_layout.1 (.write addr w) inData
      rcases place with stack | output
      · exact .inl (stack.byte_inside (r := callerStack s) entry.stackValid (Nat.le_refl _) j bound)
      · exact .inr (output.byte_inside (r := callerOutput s) entry.outputValid (Nat.le_refl _) j bound)

theorem borrowed_access_no_race {base : Addr} {s out : CPU} {message : Crypto.Reference.ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) (path : ImageExecution base s (callCode message.bytes.size) out)
    (a : Access) (observed : a ∈ accessTrace (callCode message.bytes.size) s) (other : AccessEvent)
    (allowed : EnvironmentAccess (callBorrow base s extent) other) : ¬DataRace (memoryEvent a) other :=
  borrow_accesses_race_free _ _ _ (borrowed_access_safe entry path a observed) allowed

theorem caller_scheduled_path (base : Addr) (s : CPU) (message : Crypto.Reference.ByteList) (extent : Nat)
    (entry : CallerEntry base s message extent) (env : MemorySchedule (callBorrow base s extent).protected)
    (profile : TimingProfile) :
    ∃ out serial,
      runScheduledUntilReturn base env 0 s (callSteps message.bytes.size) =
        some (out, accessTrace (callCode message.bytes.size) s) ∧
      runUntilReturn base s (callSteps message.bytes.size) = some serial ∧
      runScheduledCosted base env profile 0 s (callSteps message.bytes.size) =
        some (out, profile.runCost (callCode message.bytes.size) s) ∧
      BorrowAgreement (callBorrow base s extent).protected serial out ∧
      ∀ a ∈ accessTrace (callCode message.bytes.size) s,
        CallAccess (callBorrow base s extent) (memoryEvent a) := by
  obtain ⟨inputs, grants⟩ := entry.decoded_layout
  obtain ⟨serial, executed, _⟩ := serial_sha256 base s message.bytes inputs entry.output_outside
  have path := executed.decoded
  have data := call_initial_data_permitted base s message.bytes inputs grants
  have allowed := path.initial_permitted s.mem (by have := entry.imageAligned; omega) entry.textExecute data
  have valid := permittedPath_of_accesses base s _ entry.loaded entry.imageReadOnly allowed
  have hasRet := call_has_return message.bytes.size
  have count : (callCode message.bytes.size).length = callSteps message.bytes.size := call_instruction_count _
  obtain ⟨out, scheduled, timed, agree⟩ := path.scheduled valid hasRet env profile
    (covers_image base s extent entry.imageValid) (call_access_borrow entry path) 0 s
    (BorrowAgreement.refl _ _)
  have serialReturn := path.to_first_return valid hasRet
  rw [count] at scheduled serialReturn timed
  exact ⟨out, serial, scheduled, serialReturn, timed, agree, fun a ha => borrowed_access_safe entry path a ha⟩

end Crypto.RISCV64
