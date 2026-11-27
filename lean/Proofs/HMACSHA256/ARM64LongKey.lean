import Proofs.HMACSHA256.ARM64CallSites
import Proofs.HMACSHA256.ARM64ShaEntry

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported
open Crypto.Reference

def longKeyCall (s : Arm64.State) : Arm64.State :=
  (s.writeReg64 .lr (s.pc + 4#64)).setPC (s.pc - 3520#64)

theorem key_call_target (base : Addr) (s : Arm64.State)
    (pc : s.pc = routineAddress base key + 0x70#64) :
    (longKeyCall s).pc = shaAddress base := by
  have relocation : BitVec.ofInt 64 key.offset + (0x70#64 + (-3520#64)) =
      BitVec.ofInt 64 sha256Offset := by decide +kernel
  change s.pc - 3520#64 = _
  rw [BitVec.sub_eq_add_neg, pc, routineAddress, shaAddress, BitVec.add_assoc, BitVec.add_assoc, relocation]

/-- The linked long-key call fills the first 32 bytes with SHA-256 and keeps
the trailing 32 zero bytes installed by the helper. The SHA-256 entry
conditions are explicit at the call boundary. -/
theorem long_key_after_clear (s : Arm64.State) (input : ByteList) (long : 64 < input.bytes.size)
    (base : Addr) (extent : Nat) (pc : s.pc = routineAddress base key + 0x70#64)
    (entry : CallerEntry (shaAddress base) (longKeyCall s) input extent)
    (zeros : ∀ i : Fin 64, 32 ≤ i.val →
      s.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) = 0#8)
    (outsideStack : ∀ i : Fin 64, 32 ≤ i.val →
      416 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack (longKeyCall s)).toNat) :
    ∃ out observations, runRange key 0x70 1 s = some (longKeyCall s) ∧
      ShaCallResult (shaAddress base) (longKeyCall s) out input observations ∧
      out.pc = routineAddress base key + 0x74#64 ∧
      (∀ i : Fin 64, out.mem.read8 (s.readReg64 .x1 + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) := by
  obtain ⟨out, observations, serial⟩ := sha_actual_call entry
  have dst : (longKeyCall s).readReg64 .x1 = s.readReg64 .x1 := by
    simp (config := { decide := true }) [longKeyCall, Arm64.Reg.x1, Arm64.Reg.lr]
  have call : runRange key 0x70 1 s = some (longKeyCall s) := by
    unfold longKeyCall
    rw [BitVec.sub_eq_add_neg]
    exact key_call s
  have link : (longKeyCall s).readReg64 .lr = s.pc + 4#64 := by
    simp [longKeyCall, Arm64.Reg.lr]
  have back : out.pc = routineAddress base key + 0x74#64 := by
    rw [serial.returnAddress, link, pc, BitVec.add_assoc]
    rfl
  refine ⟨out, observations, call, serial, back, ?_⟩
  intro i
  rw [hmacKey_long_byte input long entry.length]
  by_cases front : i.val < 32
  · rw [if_pos front]
    let j : Fin 32 := ⟨i.val, front⟩
    have value := congrArg (fun digest : Vector (BitVec 8) 32 => digest[j.val]) serial.digest
    have written : out.mem.read8 ((longKeyCall s).readReg64 .x1 + BitVec.ofNat 64 i.val) =
        ((sha256 input).2[j.val]).toBitVec := by
      simpa only [memoryBytes32, Vector.getElem_ofFn, Vector.getElem_map] using value
    have bound : j.val < (EthLib.Base.packBytes (sha256 input).2).size := by
      change j.val < (sha256 input).2.toArray.size
      rw [(sha256 input).2.size_toArray]
      exact j.isLt
    rw [getElem!_pos (EthLib.Base.packBytes (sha256 input).2) i.val bound, ← dst]
    exact written
  · rw [if_neg front]
    have address : 32 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 i.val - (longKeyCall s).readReg64 .x1).toNat := by
      rw [dst, address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      omega
    have unchanged := serial.frame _ (outsideStack i (by omega)) address
    have mem : (longKeyCall s).mem = s.mem := rfl
    rw [mem] at unchanged
    exact (read8_of_cell _ unchanged).trans (zeros i (by omega))

end Crypto.HMACSHA256.ARM64
