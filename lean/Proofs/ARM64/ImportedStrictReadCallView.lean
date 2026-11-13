import Proofs.ARM64.ImportedPermissionView
import Proofs.ARM64.ImportedMemoryLocality

/-!
Auxiliary byte-preserving data-permission view for the recorded SHA-256 tape.
Read grants cover the 24-byte header, used payload, private stack and only the
actual K/H constant pool at image offsets 608..895. Execute grants still cover
the image, and write grants cover output/stack. Legitimate readonly input/code
aliases keep their input-role reads; instruction bytes are not reclassified as
constant data. The actual RX loaded-image baseline remains unchanged.
This logical auxiliary view changes no physical mappings and does not itself
assert that the native tape executes; later lemmas establish that success.
-/
namespace Crypto.ARM64.Imported
open Crypto.Baseline
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
local instance (region : Region) (p : BitVec 64) : Decidable (region.Contains p) :=
  inferInstanceAs (Decidable (region.base.toNat ≤ p.toNat ∧ p.toNat < region.base.toNat + region.bytes))

def callerConstantPool (base : BitVec 64) : Region := ⟨base + 608#64, 288⟩

def strictReadFootprint (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : Prop :=
  (callerHeader s).Contains p ∨ (callerPayload s message).Contains p ∨
    (callerStack s).Contains p ∨ (callerConstantPool base).Contains p

local instance (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    Decidable (strictReadFootprint base s message p) := by unfold strictReadFootprint; infer_instance
local instance (s : Arm64.State) (p : BitVec 64) : Decidable (permissionWriteFootprint s p) := by
  unfold permissionWriteFootprint; infer_instance

def strictPermission (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : Option Arm64.Perm :=
  if strictReadFootprint base s message p ∨ permissionWriteFootprint s p ∨ (callerImage base).Contains p then
    some ⟨decide (strictReadFootprint base s message p), decide (permissionWriteFootprint s p),
      decide ((callerImage base).Contains p), false, true⟩
  else none

def strictMemory (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) : Arm64.Memory :=
  Arm64.Memory.ofFn s.mem.read8 (strictPermission base s message)

def strictState (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) : Arm64.State :=
  { s with mem := strictMemory base s message }

theorem strictMemory_read8 (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : (strictMemory base s message).read8 p = s.mem.read8 p := rfl

theorem strictMemory_read32 (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : (strictMemory base s message).read32 p = s.mem.read32 p := by
  simp only [Arm64.Memory.read32, strictMemory_read8]

theorem strictMemory_read64 (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : (strictMemory base s message).read64 p = s.mem.read64 p := by
  simp only [Arm64.Memory.read64, strictMemory_read8]

theorem strictMemory_wordVector (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) (n : Nat) :
    wordVector n (strictMemory base s message) p = wordVector n s.mem p := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn, strictMemory_read32]

theorem strictMemory_perm (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) :
    (strictMemory base s message).perm p = strictPermission base s message p := by
  by_cases present : strictReadFootprint base s message p ∨ permissionWriteFootprint s p ∨ (callerImage base).Contains p
  all_goals simp [strictMemory, Arm64.Memory.ofFn, Arm64.Memory.perm, strictPermission, present, Arm64.Perm.rwx]

theorem strictMemory_noLazy (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64) : (strictMemory base s message).isLazyFree p = false := by
  by_cases present : strictReadFootprint base s message p ∨ permissionWriteFootprint s p ∨ (callerImage base).Contains p
  all_goals simp [strictMemory, Arm64.Memory.ofFn, Arm64.Memory.isLazyFree, strictPermission, present]

theorem strictPermission_read (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (read : (strictPermission base s message p).r = true) : strictReadFootprint base s message p := by
  unfold strictPermission at read
  split at read
  · exact of_decide_eq_true read
  · contradiction

theorem strictPermission_write (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (write : ((strictPermission base s message p).w && !(strictPermission base s message p).x) = true) :
    permissionWriteFootprint s p := by
  unfold strictPermission at write
  split at write
  · simp only [Bool.and_eq_true] at write
    exact of_decide_eq_true write.1
  · contradiction

theorem strictPermission_exec (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (execute : (strictPermission base s message p).x = true) : (callerImage base).Contains p := by
  unfold strictPermission at execute
  split at execute
  · exact of_decide_eq_true execute
  · contradiction

theorem strict_read_grant (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (inside : strictReadFootprint base s message p) : (strictMemory base s message).canRead p 1 = true := by
  simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree,
    strictMemory_perm, strictMemory_noLazy, strictPermission, inside]

theorem strict_write_grant (base : BitVec 64) (s : Arm64.State)
    (message : Crypto.Reference.ByteList) (p : BitVec 64)
    (inside : permissionWriteFootprint s p) (outside : ¬(callerImage base).Contains p) :
    (strictMemory base s message).canWrite p 1 = true := by
  simp [Arm64.Memory.canWrite, Arm64.Memory.allPerm, strictMemory_perm, strictPermission, inside, outside]

theorem strict_image_offset_nat (base : BitVec 64) (valid : (callerImage base).Valid)
    (off : Nat) (bound : off < 896) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  have imageBound : base.toNat + 896 ≤ 2 ^ 64 := valid
  have off64 : off < 2 ^ 64 := by omega
  have sum64 : base.toNat + off < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt off64, Nat.mod_eq_of_lt sum64]

theorem callerConstantPool_valid (base : BitVec 64) (valid : (callerImage base).Valid) :
    (callerConstantPool base).Valid := by
  change (base + 608#64).toNat + 288 ≤ 2 ^ 64
  rw [strict_image_offset_nat base valid 608 (by decide)]
  have bound : base.toNat + 896 ≤ 2 ^ 64 := valid
  omega

theorem callerConstantPool_subset (base : BitVec 64) (valid : (callerImage base).Valid) (p : BitVec 64)
    (inside : (callerConstantPool base).Contains p) : (callerImage base).Contains p := by
  change (base + 608#64).toNat ≤ p.toNat ∧ p.toNat < (base + 608#64).toNat + 288 at inside
  rw [strict_image_offset_nat base valid 608 (by decide)] at inside
  change base.toNat ≤ p.toNat ∧ p.toNat < base.toNat + 896
  omega

theorem callerConstantPool_offset (base : BitVec 64) (valid : (callerImage base).Valid)
    (off : Nat) (lower : 608 ≤ off) (upper : off < 896) :
    (callerConstantPool base).Contains (base + BitVec.ofNat 64 off) := by
  change (base + 608#64).toNat ≤ (base + BitVec.ofNat 64 off).toNat ∧
    (base + BitVec.ofNat 64 off).toNat < (base + 608#64).toNat + 288
  rw [strict_image_offset_nat base valid 608 (by decide), strict_image_offset_nat base valid off upper]
  omega

theorem strict_pool_read (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (valid : (callerImage base).Valid) (off n : Nat) (lower : 608 ≤ off) (upper : off + n ≤ 896) :
    (strictMemory base s message).canRead (base + BitVec.ofNat 64 off) n = true := by
  apply caller_read_of_bytes
  intro i hi
  have inside := callerConstantPool_offset base valid (off + i) (by omega) (by omega)
  have grant := strict_read_grant base s message _ (Or.inr (Or.inr (Or.inr inside)))
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using grant


@[simp] theorem strictState_pc (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) :
    (strictState base s message).pc = s.pc := rfl
@[simp] theorem strictState_sp (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) :
    (strictState base s message).sp = s.sp := rfl
@[simp] theorem strictState_status (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) :
    (strictState base s message).status = s.status := rfl
@[simp] theorem strictState_readReg (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList) (r : Arm64.Reg) :
    (strictState base s message).readReg64 r = s.readReg64 r := by cases r <;> rfl

theorem strict_header_read (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (off n : Nat) (bound : off + n ≤ 24) :
    (strictMemory base s message).canRead (s.readReg64 .x0 + BitVec.ofNat 64 off) n = true := by
  apply caller_region_read _ (callerHeader s) (view_header_valid base s message extent authority entry)
    (fun p hp => strict_read_grant base s message p (Or.inl hp)) off n bound

theorem strict_payload_read (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (off n : Nat) (bound : off + n ≤ message.bytes.size) :
    (strictMemory base s message).canRead ((callerPayload s message).base + BitVec.ofNat 64 off) n = true := by
  exact caller_region_read _ (callerPayload s message) (view_payload_valid base s message extent authority entry)
    (fun p hp => strict_read_grant base s message p (Or.inr (Or.inl hp))) off n bound

theorem strict_stack_read (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (off n : Nat) (bound : off + n ≤ 416) :
    (strictMemory base s message).canRead (entryStack s + BitVec.ofNat 64 off) n = true := by
  exact caller_region_read _ (callerStack s) entry.stackValid
    (fun p hp => strict_read_grant base s message p (Or.inr (Or.inr (Or.inl hp)))) off n bound

theorem strict_stack_write (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (off n : Nat) (bound : off + n ≤ 416) :
    (strictMemory base s message).canWrite (entryStack s + BitVec.ofNat 64 off) n = true := by
  apply caller_region_write _ (callerStack s) entry.stackValid ?_ off n bound
  intro p hp
  apply strict_write_grant base s message p (Or.inr hp)
  intro image
  exact entry.stackImage p ⟨hp, image⟩

theorem strict_output_write (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (off n : Nat) (bound : off + n ≤ 32) :
    (strictMemory base s message).canWrite (s.readReg64 .x1 + BitVec.ofNat 64 off) n = true := by
  apply caller_region_write _ (callerOutput s) entry.outputValid ?_ off n bound
  intro p hp
  apply strict_write_grant base s message p (Or.inl hp)
  intro image
  exact entry.outputImage p ⟨hp, image⟩

theorem strict_read_authority (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (entry : PermissionViewInputs base s message extent authority)
    (p : BitVec 64) (inside : strictReadFootprint base s message p) : authority.readable p := by
  rcases inside with header | payload | stack | pool
  · exact entry.headerRead p header
  · exact entry.payloadRead p payload
  · exact entry.stackRead p stack
  · exact entry.imageRead p (callerConstantPool_subset base entry.imageValid p pool)

theorem strict_image_data_only_pool (base : BitVec 64) (s : Arm64.State) (message : Crypto.Reference.ByteList)
    (p : BitVec 64) (read : strictReadFootprint base s message p)
    (notHeader : ¬(callerHeader s).Contains p) (notPayload : ¬(callerPayload s message).Contains p)
    (notStack : ¬(callerStack s).Contains p) : (callerConstantPool base).Contains p := by
  rcases read with header | payload | stack | pool
  · exact False.elim (notHeader header)
  · exact False.elim (notPayload payload)
  · exact False.elim (notStack stack)
  · exact pool

end Crypto.ARM64.Imported
