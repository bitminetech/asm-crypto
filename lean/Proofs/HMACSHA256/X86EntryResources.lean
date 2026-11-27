import Proofs.HMACSHA256.X86EntryFrame
import Proofs.HMACSHA256.X86FinishResources
import Proofs.HMACSHA256.X86KeyResources

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64
open Crypto.ARM64.Imported (caller_region_contains_offset)
open Crypto.Baseline (Authority Region)

def entryInputKey (s : Cpu) (extent : Nat) : Region := ⟨s.regs.get .rdi, extent⟩
def entryMessage (s : Cpu) (extent : Nat) : Region := ⟨s.regs.get .rsi, extent⟩
def entryScratch (s : Cpu) (capacity : Nat) : Region := ⟨s.regs.get .rdx, capacity⟩
def entryMac (s : Cpu) : Region := ⟨s.regs.get .rcx, 32⟩
def entryWorkspace (s : Cpu) : Region := ⟨s.regs.get .rsp - 824#64, 824⟩
def entryReturn (s : Cpu) : Region := ⟨s.regs.get .rsp, 8⟩
def entryImage (base : Val) : Region := ⟨routineAddress base entry, entry.image.size⟩

structure EntryResources (base : Val) (s : Cpu) (keyExtent messageExtent capacity : Nat)
    (authority : Authority) : Prop where
  available : 824 ≤ (s.regs.get .rsp).toNat
  aligned : (s.regs.get .rsp).toNat % 16 = 8
  keyAligned : (s.regs.get .rdi).toNat % 8 = 0
  messageAligned : (s.regs.get .rsi).toNat % 8 = 0
  scratchAligned : (s.regs.get .rdx).toNat % 8 = 0
  keyValid : (entryInputKey s keyExtent).Valid
  messageValid : (entryMessage s messageExtent).Valid
  scratchValid : (entryScratch s capacity).Valid
  macValid : (entryMac s).Valid
  returnValid : (entryReturn s).Valid
  shaValid : (imageRegion (shaAddress base)).Valid
  keyCodeValid : (keyImage base).Valid
  entryCodeValid : (entryImage base).Valid
  stackKey : (entryWorkspace s).Disjoint (entryInputKey s keyExtent)
  stackMessage : (entryWorkspace s).Disjoint (entryMessage s messageExtent)
  stackScratch : (entryWorkspace s).Disjoint (entryScratch s capacity)
  stackMac : (entryWorkspace s).Disjoint (entryMac s)
  stackSha : (entryWorkspace s).Disjoint (imageRegion (shaAddress base))
  stackKeyCode : (entryWorkspace s).Disjoint (keyImage base)
  stackEntryCode : (entryWorkspace s).Disjoint (entryImage base)
  returnMac : (entryReturn s).Disjoint (entryMac s)
  returnScratch : (entryReturn s).Disjoint (entryScratch s capacity)
  scratchMessage : (entryScratch s capacity).Disjoint (entryMessage s messageExtent)
  scratchMac : (entryScratch s capacity).Disjoint (entryMac s)
  scratchEntryCode : (entryScratch s capacity).Disjoint (entryImage base)
  scratchSha : (entryScratch s capacity).Disjoint (imageRegion (shaAddress base))
  macSha : (entryMac s).Disjoint (imageRegion (shaAddress base))
  keyCanonical : ∀ p, (entryInputKey s keyExtent).Contains p → canonical p = true
  messageCanonical : ∀ p, (entryMessage s messageExtent).Contains p → canonical p = true
  scratchCanonical : ∀ p, (entryScratch s capacity).Contains p → canonical p = true
  macCanonical : ∀ p, (entryMac s).Contains p → canonical p = true
  stackCanonical : ∀ p, (entryWorkspace s).Contains p → canonical p = true
  shaCanonical : ∀ p, (imageRegion (shaAddress base)).Contains p → canonical p = true
  keyCodeCanonical : ∀ p, (keyImage base).Contains p → canonical p = true
  entryCodeCanonical : ∀ p, (entryImage base).Contains p → canonical p = true
  exitCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true
  finishCanonical : canonical (routineAddress base finish) = true
  finishLinks : canonical (routineAddress base finish + 0x21#64) = true ∧
    canonical (routineAddress base finish + 0xaf#64) = true
  keyRead : ∀ p, (entryInputKey s keyExtent).Contains p → authority.readable p
  messageRead : ∀ p, (entryMessage s messageExtent).Contains p → authority.readable p
  scratchRead : ∀ p, (entryScratch s capacity).Contains p → authority.readable p
  macWrite : ∀ p, (entryMac s).Contains p → authority.writable p
  stackRead : ∀ p, (entryWorkspace s).Contains p → authority.readable p
  stackWrite : ∀ p, (entryWorkspace s).Contains p → authority.writable p
  shaRead : ∀ p, (imageRegion (shaAddress base)).Contains p → authority.readable p
  shaExecutable : ∀ i < codeEnd, authority.executable (shaAddress base + BitVec.ofNat 64 i)

theorem EntryResources.entry_pc_canonical {base s k n cap authority}
    (g : EntryResources base s k n cap authority) (off : Nat) (within : off < entry.image.size) :
    canonical (routineAddress base entry + BitVec.ofNat 64 off) = true :=
  g.entryCodeCanonical _ (caller_region_contains_offset (entryImage base) g.entryCodeValid off within)

theorem EntryResources.key_pc_canonical {base s k n cap authority}
    (g : EntryResources base s k n cap authority) (off : Nat) (within : off < key.image.size) :
    canonical (routineAddress base key + BitVec.ofNat 64 off) = true :=
  g.keyCodeCanonical _ (caller_region_contains_offset (keyImage base) g.keyCodeValid off within)

theorem EntryResources.sha_base_canonical {base s k n cap authority}
    (g : EntryResources base s k n cap authority) :
    canonical (shaAddress base) = true := by
  apply g.shaCanonical
  have includes := caller_region_contains_offset (imageRegion (shaAddress base)) g.shaValid 0
    (by change 0 < image.size; decide +kernel)
  change (imageRegion (shaAddress base)).Contains (shaAddress base + 0#64) at includes
  simpa only [BitVec.add_zero] using includes

def entryKeyBlock (s : Cpu) : Region := regionSlice (entryWorkspace s) 704 64
def entryHelperReturn (s : Cpu) : Region := regionSlice (entryWorkspace s) 696 8

theorem entry_slice (s : Cpu) (off n : Nat) (fit : off ≤ 824) :
    regionSlice (entryWorkspace s) off n = ⟨s.regs.get .rsp - BitVec.ofNat 64 (824 - off), n⟩ :=
  stackRegion_slice _ 824 off n fit

theorem entry_slice_valid {base s k n cap authority} (g : EntryResources base s k n cap authority)
    (off bytes : Nat) (fits : off + bytes ≤ 824) :
    (regionSlice (entryWorkspace s) off bytes).Valid :=
  regionSlice_valid _ _ _ (stackRegion_valid _ _ g.available) fits

theorem entry_slice_inside {base s k n cap authority} (g : EntryResources base s k n cap authority)
    (off bytes : Nat) (fits : off + bytes ≤ 824) (p : Val)
    (h : (regionSlice (entryWorkspace s) off bytes).Contains p) : (entryWorkspace s).Contains p :=
  regionSlice_inside _ _ _ (stackRegion_valid _ _ g.available) fits p h

theorem entry_slice_disjoint {base s k n cap authority} (g : EntryResources base s k n cap authority)
    (off bytes after afterBytes : Nat) (ordered : off + bytes ≤ after) (fits : after + afterBytes ≤ 824) :
    (regionSlice (entryWorkspace s) off bytes).Disjoint (regionSlice (entryWorkspace s) after afterBytes) :=
  regionSlices_disjoint _ _ _ _ _ (stackRegion_valid _ _ g.available) ordered fits

theorem entry_helper_alignment {base s k n cap authority} (g : EntryResources base s k n cap authority) :
    (s.regs.get .rsp - 128#64).toNat % 16 = 8 := by
  have prior := frame_base_end (s.regs.get .rsp) 128 (by have := g.available; omega)
  have aligned := g.aligned
  change (s.regs.get .rsp - BitVec.ofNat 64 128).toNat % 16 = 8
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2800000 in
theorem EntryResources.key_grants {base s k n cap authority}
    (g : EntryResources base s k n cap authority) (called : Cpu)
    (src : called.regs.get .rdi = s.regs.get .rdi)
    (dst : called.regs.get .rsi = (entryKeyBlock s).base)
    (sp : called.regs.get .rsp = s.regs.get .rsp - 128#64)
    (link : canonical (called.mem.readSize .q (called.regs.get .rsp)) = true) :
    KeyResources base called k authority := by
  let nested := regionSlice (entryWorkspace s) 128 568
  have input : keyInput called k = entryInputKey s k := by simp only [keyInput, entryInputKey, src]
  have output : keyOutput called = entryKeyBlock s := by
    change (⟨called.regs.get .rsi, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [dst]
  have stack : keyWorkspace called = nested := by
    change (⟨called.regs.get .rsp - 568#64, 568⟩ : Region) =
      regionSlice (entryWorkspace s) 128 568
    rw [sp, BitVec.sub_sub, entry_slice s 128 568 (by decide)]
    rfl
  have ret : keyReturn called = entryHelperReturn s := by
    unfold keyReturn entryHelperReturn
    rw [sp, entry_slice s 696 8 (by decide)]
  have byteHeight := frame_base_end (s.regs.get .rsp) 128 (by have := g.available; omega)
  have stackInside (p : Val) (h : (keyWorkspace called).Contains p) : (entryWorkspace s).Contains p := by
    rw [stack] at h
    exact entry_slice_inside g 128 568 (by decide) p h
  have keyInside (p : Val) (h : (keyOutput called).Contains p) : (entryWorkspace s).Contains p := by
    rw [output] at h
    exact entry_slice_inside g 704 64 (by decide) p h
  exact {
    available := by rw [sp]; have := g.available; omega
    aligned := sp.symm ▸ entry_helper_alignment g
    inputAligned := src.symm ▸ g.keyAligned
    inputValid := input.symm ▸ g.keyValid
    outputValid := output.symm ▸ entry_slice_valid g 704 64 (by decide)
    returnValid := ret.symm ▸ entry_slice_valid g 696 8 (by decide)
    imageValid := g.shaValid
    keyImageValid := g.keyCodeValid
    stackInput := fun p h => g.stackKey p ⟨stackInside p h.1, input ▸ h.2⟩
    stackOutput := by
      rw [stack, output]
      exact entry_slice_disjoint g 128 568 704 64 (by decide) (by decide)
    stackImage := fun p h => g.stackSha p ⟨stackInside p h.1,h.2⟩
    stackKeyImage := fun p h => g.stackKeyCode p ⟨stackInside p h.1,h.2⟩
    outputInput := fun p h => g.stackKey p ⟨keyInside p h.1,input ▸ h.2⟩
    outputImage := fun p h => g.stackSha p ⟨keyInside p h.1,h.2⟩
    outputKeyImage := fun p h => g.stackKeyCode p ⟨keyInside p h.1,h.2⟩
    returnOutput := by
      rw [ret, output]
      exact entry_slice_disjoint g 696 8 704 64 (by decide) (by decide)
    inputCanonical := fun p h => g.keyCanonical p (input ▸ h)
    outputCanonical := fun p h => g.stackCanonical p (keyInside p h)
    stackCanonical := fun p h => g.stackCanonical p (stackInside p h)
    codeCanonical := g.shaCanonical
    helperCanonical := g.keyCodeCanonical
    returnCanonical := link
    inputRead := fun p h => g.keyRead p (input ▸ h)
    outputWrite := fun p h => g.stackWrite p (keyInside p h)
    stackRead := fun p h => g.stackRead p (stackInside p h)
    stackWrite := fun p h => g.stackWrite p (stackInside p h)
    codeRead := g.shaRead
    shaExecutable := g.shaExecutable
  }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2800000 in
theorem EntryResources.finish_grants {base s k n cap authority}
    (g : EntryResources base s k n cap authority) (called : Cpu)
    (capMin : 8 ≤ cap)
    (src : called.regs.get .rdi = s.regs.get .rdx + 8#64)
    (block : called.regs.get .rsi = (entryKeyBlock s).base)
    (dst : called.regs.get .rdx = s.regs.get .rcx)
    (sp : called.regs.get .rsp = s.regs.get .rsp - 128#64)
    (link : canonical (called.mem.readSize .q (called.regs.get .rsp)) = true) :
    FinishResources base called (cap - 8) authority := by
  let nested := regionSlice (entryWorkspace s) 0 696
  let inner := regionSlice (entryScratch s cap) 8 (cap - 8)
  have enough : 8 + (cap - 8) ≤ (entryScratch s cap).bytes := by change _ ≤ cap; omega
  have input : finishInput called (cap - 8) = inner := by simp only [finishInput, src, inner, regionSlice, entryScratch]
  have keyRegion : finishKey called = entryKeyBlock s := by
    change (⟨called.regs.get .rsi, 64⟩ : Region) = ⟨(entryKeyBlock s).base, 64⟩
    rw [block]
  have mac : finishMac called = entryMac s := by simp only [finishMac, entryMac, dst]
  have stack : finishWorkspace called = nested := by
    change (⟨called.regs.get .rsp - 696#64, 696⟩ : Region) =
      regionSlice (entryWorkspace s) 0 696
    rw [sp, BitVec.sub_sub, entry_slice s 0 696 (by decide)]
    rfl
  have ret : finishReturn called = entryHelperReturn s := by
    unfold finishReturn entryHelperReturn
    rw [sp, entry_slice s 696 8 (by decide)]
  have stackInside (p : Val) (h : (finishWorkspace called).Contains p) : (entryWorkspace s).Contains p := by
    rw [stack] at h
    exact entry_slice_inside g 0 696 (by decide) p h
  have keyInside (p : Val) (h : (finishKey called).Contains p) : (entryWorkspace s).Contains p := by
    rw [keyRegion] at h
    exact entry_slice_inside g 704 64 (by decide) p h
  have inputInside (p : Val) (h : (finishInput called (cap - 8)).Contains p) :
      (entryScratch s cap).Contains p := by
    rw [input] at h
    exact regionSlice_inside _ _ _ g.scratchValid enough p h
  have byteHeight := frame_base_end (s.regs.get .rsp) 128 (by have := g.available; omega)
  exact {
    available := by rw [sp]; have := g.available; omega
    aligned := sp.symm ▸ entry_helper_alignment g
    inputAligned := by
      rw [src, BitVec.toNat_add]
      change ((s.regs.get .rdx).toNat + 8) % 2 ^ 64 % 8 = 0
      have := g.scratchAligned
      omega
    inputValid := input.symm ▸ regionSlice_valid _ _ _ g.scratchValid enough
    keyValid := keyRegion.symm ▸ entry_slice_valid g 704 64 (by decide)
    macValid := mac.symm ▸ g.macValid
    imageValid := g.shaValid
    returnValid := ret.symm ▸ entry_slice_valid g 696 8 (by decide)
    stackInput := fun p h => g.stackScratch p ⟨stackInside p h.1,inputInside p h.2⟩
    stackKey := by
      rw [stack, keyRegion]
      exact entry_slice_disjoint g 0 696 704 64 (by decide) (by decide)
    stackMac := fun p h => g.stackMac p ⟨stackInside p h.1,mac ▸ h.2⟩
    stackImage := fun p h => g.stackSha p ⟨stackInside p h.1,h.2⟩
    returnMac := fun p h => g.stackMac p ⟨entry_slice_inside g 696 8 (by decide) p
      (show (entryHelperReturn s).Contains p from ret ▸ h.1),mac ▸ h.2⟩
    macInput := fun p h => g.scratchMac p ⟨inputInside p h.2,mac ▸ h.1⟩
    macKey := fun p h => g.stackMac p ⟨keyInside p h.2,mac ▸ h.1⟩
    macImage := fun p h => g.macSha p ⟨mac ▸ h.1,h.2⟩
    inputCanonical := fun p h => g.scratchCanonical p (inputInside p h)
    keyCanonical := fun p h => g.stackCanonical p (keyInside p h)
    macCanonical := fun p h => g.macCanonical p (mac ▸ h)
    stackCanonical := fun p h => g.stackCanonical p (stackInside p h)
    codeCanonical := g.shaCanonical
    returnCanonical := link
    innerLinkCanonical := g.finishLinks.1
    outerLinkCanonical := g.finishLinks.2
    inputRead := fun p h => g.scratchRead p (inputInside p h)
    keyRead := fun p h => g.stackRead p (keyInside p h)
    macWrite := fun p h => g.macWrite p (mac ▸ h)
    stackRead := fun p h => g.stackRead p (stackInside p h)
    stackWrite := fun p h => g.stackWrite p (stackInside p h)
    imageRead := g.shaRead
    shaExecutable := g.shaExecutable
  }

end Crypto.HMACSHA256.X86_64
