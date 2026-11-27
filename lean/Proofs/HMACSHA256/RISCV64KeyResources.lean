import Proofs.HMACSHA256.RISCV64Key

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64 Crypto.Reference
open Crypto.Baseline (Region)
open Crypto.ARM64.Imported (caller_region_read caller_region_write)

def keyInputRegion (s : CPU) (extent : Nat) : Region := ⟨s.reg 10#5, extent⟩
def keyBlockRegion (s : CPU) : Region := ⟨s.reg 11#5, 64⟩
def keyWorkspace (s : CPU) : Region := stackRegion (s.reg 2#5) 592

/-- Independent caller grants for the key helper and its SHA-256 callee.
The short branch uses the top 112 bytes of the shared workspace. -/
structure KeyResources (base : Addr) (s : CPU) (extent : Nat) : Prop where
  available : 592 ≤ (s.reg 2#5).toNat
  aligned : (s.reg 2#5).toNat % 16 = 0
  inputAligned : (s.reg 10#5).toNat % 8 = 0
  blockAligned : (s.reg 11#5).toNat % 8 = 0
  inputValid : (keyInputRegion s extent).Valid
  blockValid : (keyBlockRegion s).Valid
  blockInput : (keyBlockRegion s).Disjoint (keyInputRegion s extent)
  stackInput : (keyWorkspace s).Disjoint (keyInputRegion s extent)
  stackBlock : (keyWorkspace s).Disjoint (keyBlockRegion s)
  stackImage : (keyWorkspace s).Disjoint (callerImage (shaAddress base))
  blockImage : (keyBlockRegion s).Disjoint (callerImage (shaAddress base))
  inputRead : ∀ p, (keyInputRegion s extent).Contains p → s.mem.canRead p 1 = true
  blockWrite : ∀ p, (keyBlockRegion s).Contains p → s.mem.canWrite p 1 = true
  stackRead : ∀ p, (keyWorkspace s).Contains p → s.mem.canRead p 1 = true
  stackWrite : ∀ p, (keyWorkspace s).Contains p → s.mem.canWrite p 1 = true

def keyStepBound (length : Nat) : Nat :=
  if length ≤ 64 then 49 + 8 * (length / 8) + 7 * (length % 8) else 45 + callSteps length

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4400000 in
/-- The same caller grants establish the short-copy and long-hash cases.
The result is the EthLib K0 block and all bytes outside the output and
the full stack footprint are preserved. -/
theorem key_execution_from_caller (base : Addr) (s : CPU) (input : ByteList) (extent : Nat)
    (pc : s.pc = routineAddress base key)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (sizeBound : input.size < 2 ^ 64) (lengthBound : input.bytes.size < 2 ^ 61)
    (encoded : EncodedByteList s.mem (s.reg 10#5) input)
    (grants : KeyResources base s extent) (sha : ShaCode (shaAddress base) s.mem)
    (loaded : key.Loaded (routineAddress base key) s.mem.read8)
    (codeAligned : (routineAddress base key).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base key) key.image.size = true)
    (returnAligned : (s.reg 1#5).toNat % 2 = 0) :
    ∃ out events, ProgramExecution base s events out ∧ events.length ≤ keyStepBound input.bytes.size ∧
      out.pc = s.reg 1#5 ∧ out.reg 2#5 = s.reg 2#5 ∧
      (∀ i : Fin 13, out.reg (frameSlot i.val).register = s.reg (frameSlot i.val).register) ∧
      (∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (hmacKey input)[i.val].toBitVec) ∧
      (∀ p, ¬ (keyWorkspace s).Contains p → ¬ (keyBlockRegion s).Contains p →
        out.mem.cells p = s.mem.cells p) ∧ KeyTrace base s input events := by
  let work := keyWorkspace s
  let frame := regionSlice work 480 112
  let alloc := keyInputRegion s extent
  let block := keyBlockRegion s
  let subStack := regionSlice work 0 480
  let hashState := s.put 2#5 (s.reg 2#5 - 112#64)
  let shaOut := regionSlice block 0 32
  have stackValid : work.Valid := stackRegion_valid _ _ grants.available
  have frameBase : frame = ⟨s.reg 2#5 - 112#64, 112⟩ := stackRegion_slice _ 592 480 112 (by decide)
  have frameInside (p : Addr) (inside : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Contains p) :
      work.Contains p := regionSlice_inside work 480 112 stackValid
    (by change 480 + 112 ≤ 592; decide) p (by
      change frame.Contains p
      rwa [frameBase])
  have frameAligned : (s.reg 2#5 - 112#64).toNat % 16 = 0 :=
    stackRegion_aligned _ 112 grants.aligned (by decide) (by have := grants.available; omega)
  have frame8 : (s.reg 2#5 - 112#64).toNat % 8 = 0 := by omega
  have readStack : s.mem.canRead (s.reg 2#5 - 112#64) 112 = true := by
    have permitted := caller_region_read s.mem work stackValid grants.stackRead
      480 112 (by change 480 + 112 ≤ 592; decide)
    change s.mem.canRead frame.base 112 = true at permitted
    rwa [frameBase] at permitted
  have writeStack : s.mem.canWrite (s.reg 2#5 - 112#64) 112 = true := by
    have permitted := caller_region_write s.mem work stackValid grants.stackWrite
      480 112 (by change 480 + 112 ≤ 592; decide)
    change s.mem.canWrite frame.base 112 = true at permitted
    rwa [frameBase] at permitted
  have readInput : s.mem.canRead (s.reg 10#5) extent = true := by
    have permitted := caller_region_read s.mem alloc grants.inputValid grants.inputRead 0 extent (by
      change 0 + extent ≤ extent
      omega)
    change s.mem.canRead (s.reg 10#5 + 0#64) extent = true at permitted
    rwa [BitVec.add_zero] at permitted
  have writeBlock : s.mem.canWrite (s.reg 11#5) 64 = true := by
    have permitted := caller_region_write s.mem block grants.blockValid grants.blockWrite 0 64 (by
      change 0 + 64 ≤ 64
      decide)
    change s.mem.canWrite (s.reg 11#5 + 0#64) 64 = true at permitted
    rwa [BitVec.add_zero] at permitted
  have inputOffFrame : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint alloc :=
    fun p hit => grants.stackInput p ⟨frameInside p hit.1, hit.2⟩
  have blockOffFrame : (⟨s.reg 2#5 - 112#64, 112⟩ : Region).Disjoint block :=
    fun p hit => grants.stackBlock p ⟨frameInside p hit.1, hit.2⟩
  have blockValue {out : CPU}
      (value : ∀ i : Fin 64, out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) (i : Fin 64) :
      out.mem.read8 (s.reg 11#5 + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec := by
    rw [value i]
    have inside : i.val < (EthLib.Base.packBytes (hmacKey input)).size := by
      change i.val < (hmacKey input).toArray.size
      rw [Vector.size_toArray]
      exact i.isLt
    rw [getElem!_pos (EthLib.Base.packBytes (hmacKey input)) i.val inside]
    rfl
  by_cases short : input.bytes.size ≤ 64
  · obtain ⟨out, events, run, bound, link, sp, saved, value, frame, trace⟩ := short_key_return_fetched
      base s input extent pc short layout accessible returnAligned (by have := grants.available; omega)
      encoded grants.inputValid grants.inputAligned readInput grants.blockValid grants.blockInput
      blockOffFrame inputOffFrame loaded codeAligned exec frame8 readStack writeStack grants.blockAligned writeBlock
    exact ⟨out, events, run, by rw [keyStepBound, if_pos short, bound], link, sp, saved, blockValue value,
      fun p offStack offBlock => frame p offBlock (fun hit => offStack (frameInside p hit)), trace⟩
  have hashSP : hashState.reg 2#5 = s.reg 2#5 - 112#64 := by
    change (s.put 2#5 _).reg 2#5 = _
    rw [reg_put]
    rfl
  have nested : callerStack hashState = subStack := by
    change (⟨hashState.reg 2#5 - 480#64, 480⟩ : Region) = subStack
    have address : s.reg 2#5 - 112#64 - 480#64 = s.reg 2#5 - 592#64 := by
      rw [BitVec.sub_sub]
      rfl
    rw [hashSP, address]
    exact (stackRegion_slice _ 592 0 480 (by decide)).symm
  have hashInput : callerInput hashState extent = alloc := by
    simp (config := { decide := true }) only [callerInput, hashState, reg_put, if_false, alloc, keyInputRegion] <;> rfl
  have hashOutput : callerOutput hashState = shaOut := by
    simp (config := { decide := true }) only [callerOutput, hashState, reg_put, if_false]
    change (⟨s.reg 11#5, 32⟩ : Region) = ⟨s.reg 11#5 + 0#64, 32⟩
    rw [BitVec.add_zero]
  have insideShaStack (p : Addr) (inside : (callerStack hashState).Contains p) : work.Contains p := by
    rw [nested] at inside
    exact regionSlice_inside _ _ _ stackValid (by change 0 + 480 ≤ 592; decide) p inside
  have insideShaOut (p : Addr) (inside : (callerOutput hashState).Contains p) : block.Contains p := by
    rw [hashOutput] at inside
    exact regionSlice_inside _ _ _ grants.blockValid (by change 0 + 32 ≤ 64; decide) p inside
  have insideShaInput (p : Addr) (h : (callerInput hashState extent).Contains p) : alloc.Contains p := by
    rwa [hashInput] at h
  have resources : ShaResources (shaAddress base) hashState extent := {
    inputAligned := by
      simpa (config := { decide := true }) only [hashState, reg_put, if_false] using grants.inputAligned
    outputAligned := by
      simpa (config := { decide := true }) only [hashState, reg_put, if_false] using grants.blockAligned
    stackAligned := by
      simpa (config := { decide := true }) only [hashState, reg_put, if_false, if_true] using frameAligned
    stackAvailable := by
      have h := frame_base_end (s.reg 2#5) 112 (by have := grants.available; omega)
      have total := grants.available
      change 480 ≤ (hashState.reg 2#5).toNat
      rw [hashSP]
      change 480 ≤ (s.reg 2#5 - BitVec.ofNat 64 112).toNat
      omega
    inputValid := hashInput.symm ▸ grants.inputValid
    outputValid := by
      rw [hashOutput]
      exact regionSlice_valid _ _ _ grants.blockValid (by change 0 + 32 ≤ 64; decide)
    outputInput := fun p h => grants.blockInput p ⟨insideShaOut p h.1, insideShaInput p h.2⟩
    outputStack := fun p h => grants.stackBlock p ⟨insideShaStack p h.2, insideShaOut p h.1⟩
    outputImage := fun p h => grants.blockImage p ⟨insideShaOut p h.1, h.2⟩
    stackInput := fun p h => grants.stackInput p ⟨insideShaStack p h.1, insideShaInput p h.2⟩
    stackImage := fun p h => grants.stackImage p ⟨insideShaStack p h.1, h.2⟩
    inputRead := fun p h => grants.inputRead p (insideShaInput p h)
    outputWrite := fun p h => grants.blockWrite p (insideShaOut p h)
    stackRead := fun p h => grants.stackRead p (insideShaStack p h)
    stackWrite := fun p h => grants.stackWrite p (insideShaStack p h)
  }
  have countRead : (Access.read (s.reg 10#5 + 16#64) .double).permitted s.mem = true := by
    have room : 16 + 8 ≤ extent := by have := layout.1; have := layout.2.2.1; omega
    exact read_of_grant grants.inputAligned room (by decide) readInput
  have keyOffHash : (⟨s.reg 2#5 - 112#64 - 480#64, 480⟩ : Region).Disjoint block := by
    have same : (⟨s.reg 2#5 - 112#64 - 480#64, 480⟩ : Region) = callerStack hashState := by
      change _ = (⟨hashState.reg 2#5 - 480#64, 480⟩ : Region)
      rw [hashSP]
    exact fun p h => grants.stackBlock p ⟨insideShaStack p (same ▸ h.1), h.2⟩
  obtain ⟨out, events, run, bound, link, sp, saved, value, frame, trace⟩ := long_key_return_fetched
    base s input extent pc (by omega) layout accessible sizeBound lengthBound returnAligned
    grants.available encoded sha resources grants.blockValid grants.blockInput grants.blockImage keyOffHash
    blockOffFrame inputOffFrame (fun p h => grants.stackImage p ⟨frameInside p h.1, h.2⟩)
    loaded codeAligned exec frame8 readStack writeStack grants.blockAligned writeBlock countRead
  exact ⟨out, events, run, by simpa only [keyStepBound, if_neg short] using bound,
    link, sp, saved, blockValue value, frame, trace⟩

end Crypto.HMACSHA256.RISCV64
