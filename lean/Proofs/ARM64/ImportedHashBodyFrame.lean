import Proofs.ARM64.ImportedHashBodyFetch
import Proofs.ARM64.ImportedHashInitFrame

/-!
Final memory-cell footprint for the recorded SHA-256 body. The compression
phases preserve cells outside the 288-byte schedule/hash area, and the exit
stores preserve cells outside the 32-byte digest. Composition uses the exact
native execution results and deterministic intermediate states. These are
final-state frame results; transient accesses and the complete architecture
resource/effect baseline remain separate obligations.
-/
namespace Crypto.ARM64.Imported

attribute [local irreducible] runWords

theorem storeDigestWords_outside (s : Arm64.State) (p : BitVec 64)
    (h : 32 ≤ (p - s.readReg64 .x1).toNat) :
    (storeDigestWords s).cells p = s.mem.cells p := by
  apply fold_cells_frame
  intro m i hi
  have small : i < 8 := List.mem_range.mp hi
  apply write32_cells_outside
  exact region_store_delta (s.readReg64 .x1) p (4 * i) 32 4 (by omega) h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem hash_body_memory_frame (s : Arm64.State) (ready : BlockReady s)
    (full padding : Nat) (fullBound : full < 2 ^ 64) (paddingBound : padding ≤ 2)
    (count : s.readReg64 .x3 = BitVec.ofNat 64 full)
    (phase : s.readReg64 .x4 = 0#64) (padCount : s.readReg64 .x6 = BitVec.ofNat 64 padding)
    (hr : ∀ (i : Fin full) (j : Fin 16),
      s.mem.canRead (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val)) 4 = true)
    (sep : ∀ (i : Fin full) (j : Fin 16) (b : Fin 4),
      288 ≤ (s.readReg64 .x2 + BitVec.ofNat 64 (64 * i.val + 4 * j.val) + BitVec.ofNat 64 b.val - s.sp).toNat)
    (padRead : ∀ i : Fin 32, s.mem.canRead ((s.sp + 288#64) + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputWrite : ∀ i : Fin 8, s.mem.canWrite (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (outputOutside : ∀ (i : Fin 8) (b : Fin 4),
      288 ≤ (s.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 b.val - s.sp).toNat) (out : Arm64.State)
    (executed : runWords (hashBodyCode full padding) s = some out) :
    ∀ p : BitVec 64, 288 ≤ (p - s.sp).toNat →
      32 ≤ (p - s.readReg64 .x1).toNat → out.mem.cells p = s.mem.cells p := by
  obtain ⟨hashed, he, _, _, _, _, x1, _, _, readyHash, _, frame, _⟩ :=
    hash_phases s ready full padding fullBound paddingBound count phase padCount hr sep padRead
  have writes (i : Fin 8) : hashed.mem.canWrite (hashed.readReg64 .x1 + BitVec.ofNat 64 (4 * i.val)) 4 = true := by
    rw [x1]
    exact (canWrite32_of_cells _ (fun b => frame _ (outputOutside i b))).trans (outputWrite i)
  obtain ⟨finished, ho, post⟩ := exists_of_map_some _ _ _ (exit_stores_bytes hashed readyHash.hashRead writes)
  simp only [Prod.mk.injEq] at post
  obtain ⟨_, finalMemory, _⟩ := post
  have expanded := runWords_code_cast (hashBodyCode full padding) (hashPhasesCode full padding ++ exitCode) s out rfl executed
  have exitExec := runWords_suffix_of_prefix (hashPhasesCode full padding) exitCode s hashed out he expanded
  have same : finished = out := Option.some.inj (ho.symm.trans exitExec)
  have memory : out.mem = storeDigestWords hashed := by rw [← same]; exact finalMemory
  intro p outsideWork outsideDigest
  rw [memory]
  exact (storeDigestWords_outside hashed p (by rw [x1]; exact outsideDigest)).trans (frame p outsideWork)

end Crypto.ARM64.Imported
