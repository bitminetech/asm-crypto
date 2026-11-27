import Proofs.HMACSHA256.EncodedByteList
import Proofs.ARM64.ImportedVerifiedCall
import Proofs.ARM64.ImportedABI

namespace Crypto.HMACSHA256.ARM64

open Crypto.Reference Crypto.ARM64.Imported

structure ShaResources (base : BitVec 64) (s : Arm64.State) (extent : Nat) : Prop where
  loaded : (program base).CodeLoaded s.mem
  messageAligned : (s.readReg64 .x0).toNat % 8 = 0
  digestAligned : (s.readReg64 .x1).toNat % 8 = 0
  stackAligned : s.sp.toNat % 16 = 0
  stackAvailable : 416 ≤ s.sp.toNat
  inputValid : (callerInput s extent).Valid
  outputValid : (callerOutput s).Valid
  stackValid : (callerStack s).Valid
  imageValid : (callerImage base).Valid
  outputInput : (callerOutput s).Disjoint (callerInput s extent)
  outputStack : (callerOutput s).Disjoint (callerStack s)
  outputImage : (callerOutput s).Disjoint (callerImage base)
  stackInput : (callerStack s).Disjoint (callerInput s extent)
  stackImage : (callerStack s).Disjoint (callerImage base)
  inputRead : ∀ p, (callerInput s extent).Contains p → s.mem.canRead p 1 = true
  stackRead : ∀ p, (callerStack s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (callerStack s).Contains p → s.mem.canWrite p 1 = true
  outputWrite : ∀ p, (callerOutput s).Contains p → s.mem.canWrite p 1 = true

theorem establish_sha_entry {base : BitVec 64} {s : Arm64.State} {message : ByteList} {extent : Nat}
    (layout : message.WellFormed) (accessible : message.size ≤ extent)
    (sizeBound : message.size < 2 ^ 64) (lengthBound : message.bytes.size < 2 ^ 61)
    (encoding : EncodedByteList s.mem (s.readReg64 .x0) message)
    (resources : ShaResources base s extent) (pc : s.pc = base) (running : s.status = .Running) :
    CallerEntry base s message extent where
  layout := layout
  size64 := sizeBound
  accessible := accessible
  headerFits := by
    have minimum := layout.1
    have within := layout.2.2.1
    omega
  length := lengthBound
  messageAligned := resources.messageAligned
  digestAligned := resources.digestAligned
  stackAligned := resources.stackAligned
  stackAvailable := resources.stackAvailable
  inputValid := resources.inputValid
  outputValid := resources.outputValid
  stackValid := resources.stackValid
  imageValid := resources.imageValid
  outputInput := resources.outputInput
  outputStack := resources.outputStack
  outputImage := resources.outputImage
  stackInput := resources.stackInput
  stackImage := resources.stackImage
  inputRead := resources.inputRead
  stackRead := resources.stackRead
  stackWrite := resources.stackWrite
  outputWrite := resources.outputWrite
  sizeValue := encoding.size
  offsetValue := encoding.offset
  countValue := encoding.count
  bytes := by
    intro i
    have arrayBytes (a : ByteArray) (n : Nat) : a.get! n = a.data[n]! := by cases a; rfl
    rw [arrayBytes, getElem!_pos message.bytes.data i.val i.isLt]
    have byte := encoding.bytes i
    rw [getElem!_pos message.bytes i.val i.isLt] at byte
    exact byte
  pc := pc
  running := running
  loaded := resources.loaded

/-- The SHA-256 theorem on the caller's actual memory, preserving the live
permissions for the HMAC code that resumes after the return. -/
structure ShaCallResult (base : BitVec 64) (s out : Arm64.State) (message : ByteList)
    (observations : List InstructionObservation) : Prop where
  caller : ∃ extent, CallerEntry base s message extent
  returned : runToReturn (program base) (512 + 4000 * ((message.bytes.size + 8) / 64 + 1)) s = some out
  steps : Arm64.Steps (program base) s out
  abi : ModeledCPUABI s out
  returnAddress : out.pc = s.readReg64 .lr
  running : out.status = .Running
  digest : memoryBytes32 out.mem (s.readReg64 .x1) = (sha256 message).2.map UInt8.toBitVec
  frame : ∀ p, 416 ≤ (p - entryStack s).toNat → 32 ≤ (p - s.readReg64 .x1).toNat →
    out.mem.cells p = s.mem.cells p
  trace : runWordsObserved (wholeCallCode (BitVec.ofNat 64 message.bytes.size)) s = some (out, observations)

theorem sha_actual_call {base : BitVec 64} {s : Arm64.State} {message : ByteList} {extent : Nat}
    (entry : CallerEntry base s message extent) :
    ∃ out observations, ShaCallResult base s out message observations := by
  obtain ⟨out, returned, steps, stable, regs, sp, address, _, live, digest, frame, _, observations, trace⟩ :=
    sha256_callable base s message extent entry
  exact ⟨out, observations, ⟨⟨extent, entry⟩, returned, steps, modeled_cpu_abi _ _ stable regs sp, address, live, digest, frame, trace⟩⟩

end Crypto.HMACSHA256.ARM64
