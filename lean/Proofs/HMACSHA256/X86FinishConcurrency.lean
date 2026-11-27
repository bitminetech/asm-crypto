import Proofs.HMACSHA256.X86FinishResources
import Proofs.HMACSHA256.X86KeyConcurrency

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference Crypto.Baseline
open Crypto.ARM64.Imported (caller_region_contains_offset memoryBytes32)

def finishBorrow (base : Val) (s : Cpu) (extent : Nat) : BorrowScope where
  shared p := linkedCode base p ∨ (finishInput s extent).Contains p ∨ (finishKey s).Contains p ∨
    (finishReturn s).Contains p
  exclusive p := (finishWorkspace s).Contains p ∨ (finishMac s).Contains p

structure FinishCall (base : Val) (s : Cpu) (inner : ByteList) (k0 : HmacKeyBlock) (extent : Nat)
    (authority : Authority) : Prop where
  layout : inner.WellFormed
  accessible : inner.size ≤ extent
  sizeBound : inner.size < 2 ^ 64
  lengthBound : inner.bytes.size < 2 ^ 61
  typed : EncodedByteList (byteView s.mem) (s.regs.get .rdi) inner
  keyAt : ∀ i : Fin 64, s.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec
  resources : FinishResources base s extent authority
  pc : s.rip = routineAddress base finish
  live : s.ms = none
  shaCanonical : canonical (shaAddress base) = true
  shaLoaded : ImageLoaded (shaAddress base) s.mem
  fetchAuthority : FinishFetchAuthority base s authority

theorem finish_execution_concurrent {base : Val} {s : Cpu} {inner : ByteList} {k0 : HmacKeyBlock}
    {extent : Nat} {authority : Authority} (caller : FinishCall base s inner k0 extent authority)
    (rights : ScopedAuthority (finishBorrow base s extent) authority)
    (environment : Environment (finishBorrow base s extent)) :
    ∃ out, LinkedSchedule base authority environment 0 s (finishNativeEvents base s inner k0) out ∧
      out.ms = none ∧ out.regs.get .rsp = s.regs.get .rsp + 8#64 ∧
      out.rip = s.mem.readSize .q (s.regs.get .rsp) ∧
      (∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)) ∧
      memoryBytes32 (byteView out.mem) (s.regs.get .rdx) = (hmacFinish inner k0).map UInt8.toBitVec ∧
      (∀ p, (finishBorrow base s extent).protected p → ¬ (finishWorkspace s).Contains p →
        ¬ (finishMac s).Contains p → out.mem.read p = s.mem.read p) ∧
      (∀ e ∈ finishNativeEvents base s inner k0, CallAccess (finishBorrow base s extent) (ReportedAccess e.1 e.2.1 e.2.2)) ∧
      platformState out = platformState s := by
  let scope := finishBorrow base s extent
  obtain ⟨serial, ⟨result⟩⟩ := finish_execution_from_caller base s inner k0 extent authority caller.layout
    caller.accessible caller.sizeBound caller.lengthBound caller.typed caller.keyAt caller.resources caller.pc
    caller.live caller.shaCanonical caller.shaLoaded
  obtain ⟨executed, _⟩ := result.native caller.fetchAuthority
  have owned := executed.borrowed_accesses rights
  obtain ⟨mem, scheduled, same⟩ := executed.schedule environment owned 0 s.mem (KeepsBorrowed.refl scope _)
  refine ⟨{serial with mem := mem}, scheduled, result.live, result.sp, result.link, result.saved, ?_,
    fun p protectedCell offStack offOutput => (same p protectedCell).trans (result.frame p offStack offOutput),
    owned, executed.platform⟩
  rw [← result.digest]
  apply Vector.ext
  intro i hi
  simp only [memoryBytes32, Vector.getElem_ofFn, byteView_read]
  exact same _ (.inr (.inr (caller_region_contains_offset (finishMac s) caller.resources.macValid i hi)))

end Crypto.HMACSHA256.X86_64
