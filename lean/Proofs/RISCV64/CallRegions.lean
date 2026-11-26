import Proofs.RISCV64.FixedAccess
import Proofs.RISCV64.RegionPermissions

namespace Crypto.RISCV64

def CallData (base : Addr) (s : CPU) (size : Nat) : Access → Prop
  | .read addr w => InRegion (entryStack s) 480 addr w ∨ InRegion (s.reg 10) 24 addr w ∨
      InRegion (inputPayload s) size addr w ∨ InRegion base image.size addr w
  | .write addr w => InRegion (entryStack s) 480 addr w ∨ InRegion (s.reg 11) 32 addr w
  | .fetch .. => False

/-- Initial permissions for independently established caller regions. The
layout proof must establish that the header and used payload fit the actual
borrowed input buffer. -/
structure CallRegionPermissions (base : Addr) (s : CPU) (size : Nat) : Prop where
  stackReadable : s.mem.canRead (entryStack s) 480 = true
  stackWritable : s.mem.canWrite (entryStack s) 480 = true
  headerReadable : s.mem.canRead (s.reg 10) 24 = true
  payloadReadable : s.mem.canRead (inputPayload s) size = true
  imageReadable : s.mem.canRead base image.size = true
  digestWritable : s.mem.canWrite (s.reg 11) 32 = true
  stackAligned : (entryStack s).toNat % 8 = 0
  headerAligned : (s.reg 10).toNat % 8 = 0
  payloadAligned : (inputPayload s).toNat % 8 = 0
  imageAligned : base.toNat % 8 = 0
  digestAligned : (s.reg 11).toNat % 8 = 0

theorem CallRegionPermissions.permits {base : Addr} {s : CPU} {size : Nat} {a : Access}
    (grants : CallRegionPermissions base s size) (within : CallData base s size a) :
    a.permitted s.mem = true := by
  have aligned (p : Addr) (width : Width) (on8 : p.toNat % 8 = 0) : p.toNat % width.bytes = 0 := by
    cases width <;> simp only [Width.bytes] <;> omega
  cases a with
  | fetch => exact within.elim
  | read addr w =>
    rcases within with stack | header | payload | imageRange
    · exact stack.permitted_read (aligned _ _ grants.stackAligned) grants.stackReadable
    · exact header.permitted_read (aligned _ _ grants.headerAligned) grants.headerReadable
    · exact payload.permitted_read (aligned _ _ grants.payloadAligned) grants.payloadReadable
    · exact imageRange.permitted_read (aligned _ _ grants.imageAligned) grants.imageReadable
  | write addr w =>
    rcases within with stack | digest
    · exact stack.permitted_write (aligned _ _ grants.stackAligned) grants.stackWritable
    · exact digest.permitted_write (aligned _ _ grants.digestAligned) grants.digestWritable

theorem save_accesses (base : Addr) (s : CPU) (size : Nat) (a : Access)
    (found : a ∈ dataTrace saveFrame s) : CallData base s size a := by
  have split : saveFrame = saveFrame.take 1 ++ saveFrame.drop 1 := (List.take_append_drop 1 saveFrame).symm
  rw [split, dataTrace_append,
    empty_dataTrace (code := saveFrame.take 1) (by decide), List.nil_append] at found
  have check : checkedFixedAccess (saveFrame.drop 1) [⟨true, 2, 480⟩] = true := by decide
  obtain ⟨r, listed, range⟩ := fixed_accesses check found
  have same : r = ⟨true, 2, 480⟩ := List.mem_singleton.mp listed
  subst r
  have sp : (run (saveFrame.take 1) s).reg 2 = entryStack s := by
    change ((s.advance 2).put 2 (s.reg 2 + -480)).reg 2 = s.reg 2 - 480
    simp (config := { decide := true }) [BitVec.sub_eq_add_neg]
  cases a with
  | fetch => exact range.elim
  | read => exact (Bool.false_ne_true range.1.symm).elim
  | write => exact .inl (by simpa only [sp] using range.2)

theorem header_accesses (base : Addr) (s t : CPU) (size : Nat) (header : t.reg 10 = s.reg 10)
    (a : Access) (found : a ∈ dataTrace headerBody t) : CallData base s size a := by
  have check : checkedFixedAccess headerBody [⟨false, 10, 24⟩] = true := by decide
  obtain ⟨r, listed, range⟩ := fixed_accesses check found
  have same : r = ⟨false, 10, 24⟩ := List.mem_singleton.mp listed
  subst r
  cases a with
  | fetch => exact range.elim
  | read => exact .inr (.inl (by simpa only [header] using range.2))
  | write => exact (Bool.false_ne_true range.1).elim

theorem zero_accesses (base : Addr) (s t : CPU) (size : Nat) (stack : t.reg 2 = entryStack s)
    (a : Access) (found : a ∈ dataTrace zeroPadding t) : CallData base s size a := by
  have check : checkedFixedAccess zeroPadding [⟨true, 2, 480⟩] = true := by decide
  obtain ⟨r, listed, range⟩ := fixed_accesses check found
  have same : r = ⟨true, 2, 480⟩ := List.mem_singleton.mp listed
  subst r
  cases a with
  | fetch => exact range.elim
  | read => exact (Bool.false_ne_true range.1.symm).elim
  | write => exact .inl (by simpa only [stack] using range.2)

theorem digest_accesses (base : Addr) (s t : CPU) (size : Nat) (stack : t.reg 2 = entryStack s)
    (output : t.reg 11 = s.reg 11) (a : Access) (found : a ∈ dataTrace digestCode t) :
    CallData base s size a := by
  have check : checkedFixedAccess digestCode [⟨false, 2, 480⟩, ⟨true, 11, 32⟩] = true := by decide
  obtain ⟨r, listed, range⟩ := fixed_accesses check found
  rcases List.mem_cons.mp listed with same | other
  · subst r
    cases a with
    | fetch => exact range.elim
    | read => exact .inl (by simpa only [stack] using range.2)
    | write => exact (Bool.false_ne_true range.1).elim
  · have same : r = ⟨true, 11, 32⟩ := List.mem_singleton.mp other
    subst r
    cases a with
    | fetch => exact range.elim
    | read => exact (Bool.false_ne_true range.1.symm).elim
    | write => exact .inr (by simpa only [output] using range.2)

theorem return_accesses (base : Addr) (s t : CPU) (size : Nat) (stack : t.reg 2 = entryStack s)
    (a : Access) (found : a ∈ dataTrace returnCode t) : CallData base s size a := by
  have split : returnCode = returnCode.take 9 ++ returnCode.drop 9 := (List.take_append_drop 9 returnCode).symm
  rw [split, dataTrace_append, empty_dataTrace (code := returnCode.drop 9) (by decide), List.append_nil] at found
  have check : checkedFixedAccess (returnCode.take 9) [⟨false, 2, 480⟩] = true := by decide
  obtain ⟨r, listed, range⟩ := fixed_accesses check found
  have same : r = ⟨false, 2, 480⟩ := List.mem_singleton.mp listed
  subst r
  cases a with
  | fetch => exact range.elim
  | read => exact .inl (by simpa only [stack] using range.2)
  | write => exact (Bool.false_ne_true range.1).elim

end Crypto.RISCV64
