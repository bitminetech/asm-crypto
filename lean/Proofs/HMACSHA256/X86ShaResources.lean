import Proofs.HMACSHA256.X86ShaEntry

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.Baseline (Authority)

theorem ShaResources.of_caller_regions {base : Val} {s : Cpu} {message : ByteList}
    {extent : Nat} {authority : Authority}
    (loaded : ImageLoaded base s.mem)
    (stackAligned : (s.regs.get .rsp).toNat % 16 = 8)
    (inputAligned : (s.regs.get .rdi).toNat % 8 = 0)
    (inputValid : (inputRegion s extent).Valid)
    (outputValid : (outputRegion s).Valid)
    (stackValid : (stackRegion s).Valid)
    (imageValid : (imageRegion base).Valid)
    (inputStack : (inputRegion s extent).Disjoint (stackRegion s))
    (imageStack : (imageRegion base).Disjoint (stackRegion s))
    (stackOutput : (stackRegion s).Disjoint (outputRegion s))
    (imageOutput : (imageRegion base).Disjoint (outputRegion s))
    (inputOutput : (inputRegion s extent).Disjoint (outputRegion s))
    (imageCanonical : ∀ p, (imageRegion base).Contains p → canonical p = true)
    (inputCanonical : ∀ p, (inputRegion s extent).Contains p → canonical p = true)
    (stackCanonical : ∀ p, (stackRegion s).Contains p → canonical p = true)
    (outputCanonical : ∀ p, (outputRegion s).Contains p → canonical p = true)
    (inputRead : ∀ p, (inputRegion s extent).Contains p → authority.readable p)
    (imageRead : ∀ p, (imageRegion base).Contains p → authority.readable p)
    (stackRead : ∀ p, (stackRegion s).Contains p → authority.readable p)
    (stackWrite : ∀ p, (stackRegion s).Contains p → authority.writable p)
    (outputWrite : ∀ p, (outputRegion s).Contains p → authority.writable p)
    (executable : ∀ j < codeEnd, authority.executable (base + BitVec.ofNat 64 j)) :
    ShaResources base s message extent authority := by
  have slot (p : Val) (h : (Crypto.Baseline.Region.mk (s.regs.get .rsp) 8).Contains p) :
      (stackRegion s).Contains p := by
    have eq : frameBase s + 504#64 = s.regs.get .rsp := BitVec.sub_add_cancel _ _
    have start : (frameBase s).toNat + 504 = (s.regs.get .rsp).toNat := by
      simp only [stackRegion, Crypto.Baseline.Region.Valid] at stackValid
      have nat := congrArg BitVec.toNat eq
      rw [BitVec.toNat_add] at nat
      change ((frameBase s).toNat + 504) % 2 ^ 64 = _ at nat
      rw [Nat.mod_eq_of_lt (by omega)] at nat
      exact nat
    simp only [Crypto.Baseline.Region.Contains, stackRegion] at h ⊢
    omega
  have lower (p : Val) (h : (Crypto.Baseline.Region.mk (frameBase s) 504).Contains p) :
      (stackRegion s).Contains p := by
    simp only [Crypto.Baseline.Region.Contains, stackRegion] at h ⊢
    omega
  refine ⟨loaded, stackAligned, inputAligned, inputValid, outputValid, stackValid, imageValid,
    inputStack, imageStack, stackOutput, imageOutput, inputOutput, imageCanonical, ?_, ?_, ?_, executable⟩
  · intro p h
    rcases h with ((input | image | link) | (output | workspace))
    · exact inputCanonical p input
    · exact imageCanonical p image
    · exact stackCanonical p (slot p link)
    · exact outputCanonical p output
    · exact stackCanonical p (lower p workspace)
  · intro p h
    rcases h with (⟨input, _⟩ | image | link | workspace)
    · exact inputRead p input
    · exact imageRead p image
    · exact stackRead p (slot p link)
    · exact stackRead p (lower p workspace)
  · intro p h
    rcases h with output | workspace
    · exact outputWrite p output
    · exact stackWrite p (lower p workspace)

end Crypto.HMACSHA256.X86_64
