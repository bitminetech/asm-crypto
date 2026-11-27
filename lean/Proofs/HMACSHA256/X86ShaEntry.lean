import Proofs.HMACSHA256.EncodedByteList
import Proofs.X86_64.NativeSafety

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.Baseline (Authority)

/-- The genuine SHA-256 code and buffer conditions at an x86-64 call.
The typed layout is derived independently from the HMAC serialization. -/
structure ShaResources (base : Val) (s : Cpu) (message : ByteList) (extent : Nat)
    (authority : Authority) : Prop where
  loaded : ImageLoaded base s.mem
  stackAligned : (s.regs.get .rsp).toNat % 16 = 8
  inputAligned : (s.regs.get .rdi).toNat % 8 = 0
  inputValid : (inputRegion s extent).Valid
  outputValid : (outputRegion s).Valid
  stackValid : (stackRegion s).Valid
  imageValid : (imageRegion base).Valid
  inputStack : (inputRegion s extent).Disjoint (stackRegion s)
  imageStack : (imageRegion base).Disjoint (stackRegion s)
  stackOutput : (stackRegion s).Disjoint (outputRegion s)
  imageOutput : (imageRegion base).Disjoint (outputRegion s)
  inputOutput : (inputRegion s extent).Disjoint (outputRegion s)
  imageCanonical : ∀ p, (imageRegion base).Contains p → canonical p = true
  canonicalData : ∀ p, (callBorrow base s extent).protected p → canonical p = true
  readable : ∀ p, callRead base s message extent p → authority.readable p
  writable : ∀ p, (callBorrow base s extent).exclusive p → authority.writable p
  executable : ∀ j < codeEnd, authority.executable (base + BitVec.ofNat 64 j)

theorem establish_sha_entry {base : Val} {s : Cpu} {message : ByteList} {extent : Nat}
    {authority : Authority} (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (sizeBound : message.size < 2 ^ 64) (lengthBound : message.bytes.size < 2 ^ 61)
    (encoding : EncodedByteList (byteView s.mem) (s.regs.get .rdi) message)
    (resources : ShaResources base s message extent authority) (pc : s.rip = base) (live : s.ms = none)
    (returnCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true) :
    PermissionEntry base s message extent authority where
  live := live
  pc := pc
  loaded := resources.loaded
  layout := layout
  size64 := sizeBound
  accessible := accessible
  bound := lengthBound
  stackAligned := resources.stackAligned
  inputAligned := resources.inputAligned
  inputValid := resources.inputValid
  outputValid := resources.outputValid
  stackValid := resources.stackValid
  imageValid := resources.imageValid
  inputStack := resources.inputStack
  imageStack := resources.imageStack
  stackOutput := resources.stackOutput
  imageOutput := resources.imageOutput
  inputOutput := resources.inputOutput
  imageCanonical := resources.imageCanonical
  returnCanonical := returnCanonical
  sizeWord := (byteView_read64 _ _).trans encoding.size
  offsetWord := (byteView_read64 _ _).trans encoding.offset
  countWord := by
    have count : headerLength s = BitVec.ofNat 64 message.bytes.size :=
      (byteView_read64 _ _).trans encoding.count
    have small := lengthBound
    rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  bytes := by
    intro i
    have arrayBytes (a : ByteArray) (n : Nat) : a.get! n = a.data[n]! := by cases a; rfl
    have value := encoding.bytes i
    rw [arrayBytes, getElem!_pos message.bytes.data i.val i.isLt]
    rw [byteView_read, getElem!_pos message.bytes i.val i.isLt] at value
    exact value
  canonicalData := resources.canonicalData
  readable := resources.readable
  writable := resources.writable
  executable := resources.executable

end Crypto.HMACSHA256.X86_64
