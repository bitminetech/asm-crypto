import Proofs.HMACSHA256.X86KeyResources
import Proofs.HMACSHA256.X86Scheduling
import Proofs.HMACSHA256.X86Platform

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference Crypto.Baseline
open Crypto.ARM64.Imported (caller_region_contains_offset)

def linkedCode (base p : Val) : Prop :=
  (imageRegion (shaAddress base)).Contains p ∨
    ∃ r : Routine, (r = entry ∨ r = key ∨ r = finish) ∧ (⟨routineAddress base r, r.image.size⟩ : Region).Contains p

def keyBorrow (base : Val) (s : Cpu) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (keyInput s extent).Contains p ∨ (keyReturn s).Contains p
  exclusive p := (keyWorkspace s).Contains p ∨ (keyOutput s).Contains p

structure KeyCall (base : Val) (s : Cpu) (input : ByteList) (extent : Nat) (authority : Authority) : Prop where
  layout : input.WellFormed
  accessible : input.size ≤ extent
  sizeBound : input.size < 2 ^ 64
  lengthBound : input.bytes.size < 2 ^ 61
  encoded : EncodedByteList (byteView s.mem) (s.regs.get .rdi) input
  resources : KeyResources base s extent authority
  pc : s.rip = routineAddress base key
  live : s.ms = none
  direction : s.flags.df = false
  shaCanonical : canonical (shaAddress base) = true
  shaLoaded : ImageLoaded (shaAddress base) s.mem
  loaded : key.Loaded (routineAddress base key) s.mem.read
  fetchAuthority : KeyFetchAuthority base s authority

theorem key_execution_concurrent {base : Val} {s : Cpu} {input : ByteList} {extent : Nat}
    {authority : Authority} (caller : KeyCall base s input extent authority)
    (rights : ScopedAuthority (keyBorrow base s extent) authority)
    (environment : Environment (keyBorrow base s extent)) :
    ∃ out, LinkedSchedule base authority environment 0 s (keyNativeEvents base s input) out ∧
      out.ms = none ∧ out.flags.df = s.flags.df ∧
      out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧ out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
      (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧
      (∀ i : Fin 64, out.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec) ∧
      (∀ p, (keyBorrow base s extent).protected p → ¬ (keyWorkspace s).Contains p →
        ¬ (keyOutput s).Contains p → out.mem.read p = s.mem.read p) ∧
      (∀ e ∈ keyNativeEvents base s input, CallAccess (keyBorrow base s extent) (ReportedAccess e.1 e.2.1 e.2.2)) ∧
      platformState out = platformState s := by
  let scope := keyBorrow base s extent
  obtain ⟨serial, ⟨result⟩⟩ := key_execution_from_caller base s input extent authority caller.layout caller.accessible
    caller.sizeBound caller.lengthBound caller.encoded caller.resources caller.pc caller.live caller.direction
    caller.shaCanonical caller.shaLoaded caller.loaded
  have executed := result.native caller.fetchAuthority
  have owned := executed.borrowed_accesses rights
  obtain ⟨mem, scheduled, same⟩ := executed.schedule environment owned 0 s.mem (KeepsBorrowed.refl scope _)
  exact ⟨{serial with mem := mem}, scheduled, result.live, result.direction, result.sp, result.link,
    result.saved,
    fun i => (same _ (.inr (.inr (caller_region_contains_offset (keyOutput s)
      caller.resources.outputValid i.val i.isLt)))).trans (result.bytes i),
    fun p protectedCell offStack offOutput => (same p protectedCell).trans (result.frame p offStack offOutput),
    owned, executed.platform⟩

end Crypto.HMACSHA256.X86_64
