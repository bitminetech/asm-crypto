import Proofs.ARM64.ImportedReferenceFold

/-!
Original full-input bytes and the prepared padding bytes determine exactly the
FIPS padded blocks. The combined recorded hash body through RET then produces
exactly the pinned byte-oriented SHA-256 result, under its explicit prepared-
state memory/register hypotheses. This is not the complete function-entry or
architecture equal theorem: prologue/preparation composition, fetched-path
execution, access/confidentiality bounds and baseline review remain separate.
-/
namespace Crypto.ARM64.Imported
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Padding.Layout

theorem paddingBlockCount_bytes (data : ByteArray) :
    64 * paddingBlockCount data = lengthOffset (data.size % 64) + 8 := by
  unfold paddingBlockCount lengthOffset
  split <;> rfl

theorem paddingBlockCount_bounds (data : ByteArray) :
    1 ≤ paddingBlockCount data ∧ paddingBlockCount data ≤ 2 := by
  unfold paddingBlockCount
  split <;> omega

set_option maxHeartbeats 2000000 in
theorem memoryBlock_complete_reference (s : Arm64.State) (data : ByteArray)
    (input : ∀ i : Fin data.size, s.mem.read8 (s.readReg64 .x2 + BitVec.ofNat 64 i.val) =
      (data.get! i.val).toBitVec) (i : Fin (data.size / 64)) :
    memoryBlock s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)) = paddedSpecBlock data i.val := by
  have bytes : memoryBytes64 s.mem (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val)) =
      paddedBlock data i.val := by
    rw [paddedBlock_complete data i.val i.isLt]
    apply Vector.ext
    intro j hj
    simp only [memoryBytes64, Vector.getElem_ofFn]
    apply UInt8.eq_of_toBitVec_eq
    have ih := i.isLt
    have enough : 64 * i.val + j < data.size := by omega
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, Nat.mul_comm] using input ⟨64 * i.val + j, enough⟩
  have decoded := congrArg (fun B : Vector UInt8 64 => toSpecBlock (SHS.SHA256.Impl.toU32s B)) bytes
  exact (memoryBlock_reference _ _).trans decoded

set_option maxHeartbeats 2000000 in
theorem memoryBlock_padding_reference (s : Arm64.State) (data : ByteArray)
    (padding : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
      s.mem.read8 (s.sp + 288#64 + BitVec.ofNat 64 i.val) =
        ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec)
    (i : Fin (paddingBlockCount data)) :
    memoryBlock s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) =
      paddedSpecBlock data (data.size / 64 + i.val) := by
  have bytes : memoryBytes64 s.mem (s.sp + 288#64 + BitVec.ofNat 64 (64 * i.val)) =
      paddedBlock data (data.size / 64 + i.val) := by
    apply Vector.ext
    intro j hj
    simp only [memoryBytes64, paddedBlock, Vector.getElem_ofFn]
    apply UInt8.eq_of_toBitVec_eq
    have ih := i.isLt
    have enough : 64 * i.val + j < lengthOffset (data.size % 64) + 8 := by
      rw [← paddingBlockCount_bytes]
      omega
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_assoc]
      using padding ⟨64 * i.val + j, enough⟩
  have decoded := congrArg (fun B : Vector UInt8 64 => toSpecBlock (SHS.SHA256.Impl.toU32s B)) bytes
  exact (memoryBlock_reference _ _).trans decoded

theorem phasesHash_reference_bytes (s : Arm64.State) (data : ByteArray)
    (initial : savedHash s = SHS.SHA256.H0_256)
    (input : ∀ i : Fin data.size, s.mem.read8 (s.readReg64 .x2 + BitVec.ofNat 64 i.val) =
      (data.get! i.val).toBitVec)
    (padding : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
      s.mem.read8 (s.sp + 288#64 + BitVec.ofNat 64 i.val) =
        ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec) :
    phasesHash s (data.size / 64) (paddingBlockCount data) =
      paddedSpecFold data ((implPaddedBytes data).size / 64) :=
  phasesHash_reference s data initial (memoryBlock_complete_reference s data input)
    (memoryBlock_padding_reference s data padding)

theorem hash_body_sha256 (s : Arm64.State) (data : ByteArray) (ready : BlockReady s)
    (bound : data.size < 2 ^ 61)
    (count : s.readReg64 .x3 = BitVec.ofNat 64 (data.size / 64))
    (phase : s.readReg64 .x4 = 0#64)
    (padCount : s.readReg64 .x6 = BitVec.ofNat 64 (paddingBlockCount data))
    (hr : ∀ (i : Fin (data.size / 64)) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin (data.size / 64)) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (padRead : ∀ i : Fin 32, s.mem.canRead ((s.sp + 288#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputWrite : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputOutside : ∀ (i : Fin 8) (b : Fin 4),
      288 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (initial : savedHash s = SHS.SHA256.H0_256)
    (input : ∀ i : Fin data.size, s.mem.read8 (s.readReg64 .x2 + BitVec.ofNat 64 i.val) =
      (data.get! i.val).toBitVec)
    (padding : ∀ i : Fin (lengthOffset (data.size % 64) + 8),
      s.mem.read8 (s.sp + 288#64 + BitVec.ofNat 64 i.val) =
        ((implPaddedBytes data).get! (data.size / 64 * 64 + i.val)).toBitVec) :
    ∃ out, runWords (hashBodyCode (data.size / 64) (paddingBlockCount data)) s = some out ∧
      returnStable out = returnStable s ∧ nonvolatile out = nonvolatile s ∧
      out.sp = s.sp + 416#64 ∧ out.pc = s.readReg64 .x30 ∧
      out.readReg64 .x0 = 0#64 ∧ out.readReg64 .x1 = s.readReg64 .x1 ∧
      memoryBytes32 out.mem (s.readReg64 .x1) = (SHS.SHA256.Impl.sha256 data).map UInt8.toBitVec := by
  obtain ⟨out, he, state, nv, sp, pc, status, output, bytes⟩ :=
    hash_body s ready (data.size / 64) (paddingBlockCount data) (by omega)
      (paddingBlockCount_bounds data).2 count phase padCount hr sep padRead outputWrite outputOutside
  refine ⟨out, he, state, nv, sp, pc, status, output, ?_⟩
  rw [phasesHash_reference_bytes s data initial input padding] at bytes
  exact bytes.trans (reference_digest_bytes data bound).symm

end Crypto.ARM64.Imported
