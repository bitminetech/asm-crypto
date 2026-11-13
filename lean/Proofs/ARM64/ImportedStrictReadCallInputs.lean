import Proofs.ARM64.ImportedStrictReadCallView

/-!
Operational inputs for the auxiliary strict-data-read execution. Pool read
permissions and explicit K/H memory values replace its unavailable full RX
CodeLoaded/read-image facts. These are not new external caller assumptions:
strict_view_raw_inputs derives every field from unchanged PermissionViewInputs
and the original loaded image's pinned words, using byte-preserving views.
Actual instructions and the reference function remain unchanged.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure RawSHAInputs (base : BitVec 64) (s : Arm64.State) (data : ByteArray) : Prop where
  bound : data.size < 2 ^ 61
  pc : s.pc = base
  running : s.status = .Running
  aligned : ((entryStack s &&& 15#64) == 0#64) = true
  offsetRead : s.mem.canRead (s.readReg64 .x0 + 8#64) 8 = true
  countRead : s.mem.canRead (s.readReg64 .x0 + 16#64) 8 = true
  countValue : s.mem.read64 (s.readReg64 .x0 + 16#64) = BitVec.ofNat 64 data.size
  stackRead : ∀ off n, off + n ≤ 416 → s.mem.canRead (entryStack s + BitVec.ofNat 64 off) n = true
  stackWrite : ∀ off n, off + n ≤ 416 → s.mem.canWrite (entryStack s + BitVec.ofNat 64 off) n = true
  inputRead : ∀ off n, off + n ≤ data.size → s.mem.canRead (inputPayload s + BitVec.ofNat 64 off) n = true
  outputWrite : ∀ off n, off + n ≤ 32 → s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 off) n = true
  poolRead : ∀ off n, 608 ≤ off → off + n ≤ 896 → s.mem.canRead (base + BitVec.ofNat 64 off) n = true
  imageOutside : ∀ i : Fin 896, 416 ≤ (base + BitVec.ofNat 64 i.val - entryStack s).toNat
  inputOutside : ∀ i : Fin data.size, 416 ≤ (inputPayload s + BitVec.ofNat 64 i.val - entryStack s).toNat
  outputOutside : ∀ i : Fin 32, 416 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 i.val - entryStack s).toNat
  inputBytes : ∀ i : Fin data.size, s.mem.read8 (inputPayload s + BitVec.ofNat 64 i.val) = (data.get! i.val).toBitVec
  initialPool : wordVector 8 s.mem (base + 864#64) = SHS.SHA256.H0_256
  roundPool : wordVector 64 s.mem (base + 608#64) = SHS.SHA256.K

theorem strict_logical_wordVector (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) (n : Nat) :
    wordVector n (strictMemory base s message) p = wordVector n (logicalMemory base s message) p := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn, Arm64.Memory.read32, strictMemory_read8, logicalMemory_read8]

theorem loaded_initial_pool_at (base : BitVec 64) (memory : Arm64.Memory)
    (loaded : (program base).CodeLoaded memory) : wordVector 8 memory (base + 864#64) = SHS.SHA256.H0_256 := by
  let state : Arm64.State := { mem := memory, pc := base + 132#64 }
  have pool := loaded_initial_pool base state loaded rfl
  change wordVector 8 memory ((base + 132#64) + 732#64) = SHS.SHA256.H0_256 at pool
  rw [BitVec.add_assoc, show 132#64 + 732#64 = 864#64 from rfl] at pool
  exact pool

theorem strict_initial_pool (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    wordVector 8 (strictMemory base s message) (base + 864#64) = SHS.SHA256.H0_256 := by
  have source := permission_view_inputs base s message extent authority entry
  exact (strict_logical_wordVector base s message _ 8).trans (loaded_initial_pool_at base _ source.loaded)

theorem strict_round_pool (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    wordVector 64 (strictMemory base s message) (base + 608#64) = SHS.SHA256.K := by
  have source := permission_view_inputs base s message extent authority entry
  exact (strict_logical_wordVector base s message _ 64).trans (loaded_round_pool base _ source.loaded)

theorem strict_view_raw_inputs (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (extent : Nat) (authority : Authority)
    (entry : PermissionViewInputs base s message extent authority) :
    RawSHAInputs base (strictState base s message) message.bytes := by
  have source := permission_view_inputs base s message extent authority entry
  have payload : inputPayload (strictState base s message) = (callerPayload s message).base := by
    change s.readReg64 .x0 + (strictMemory base s message).read64 (s.readReg64 .x0 + 8#64) =
      s.readReg64 .x0 + BitVec.ofNat 64 message.offset
    rw [strictMemory_read64, entry.offsetValue]
  have samePayload : inputPayload (strictState base s message) = inputPayload (logicalState base s message) := by
    change s.readReg64 .x0 + (strictMemory base s message).read64 (s.readReg64 .x0 + 8#64) =
      s.readReg64 .x0 + (logicalMemory base s message).read64 (s.readReg64 .x0 + 8#64)
    rw [strictMemory_read64, logicalMemory_read64]
  refine ⟨entry.length, entry.pc, entry.running, source.aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    source.imageOutside, ?_, source.outputOutside, ?_, strict_initial_pool base s message extent authority entry,
    strict_round_pool base s message extent authority entry⟩
  · exact strict_header_read base s message extent authority entry 8 8 (by decide)
  · exact strict_header_read base s message extent authority entry 16 8 (by decide)
  · change (strictMemory base s message).read64 (s.readReg64 .x0 + 16#64) = _
    rw [strictMemory_read64, entry.countValue]
  · exact strict_stack_read base s message extent authority entry
  · exact strict_stack_write base s message extent authority entry
  · intro off n bound
    rw [payload]
    exact strict_payload_read base s message extent authority entry off n bound
  · exact strict_output_write base s message extent authority entry
  · exact strict_pool_read base s message entry.imageValid
  · intro i
    rw [samePayload]
    exact source.inputOutside i
  · intro i
    rw [payload]
    change (strictMemory base s message).read8 ((s.readReg64 .x0 + BitVec.ofNat 64 message.offset) + BitVec.ofNat 64 i.val) = _
    rw [strictMemory_read8]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry.bytes i

end Crypto.ARM64.Imported
