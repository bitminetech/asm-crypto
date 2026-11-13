import Proofs.ARM64.ImportedBranchFetch

/-!
Control-flow certificates for recorded fragments containing an interior branch.
The proved native PC postcondition and sequential-PC rules determine the next
instruction address; branch/data arithmetic is not substituted. These helpers
support tail-copy and phase/gate integration; NativeEqual assembles the complete baseline.
-/
namespace Crypto.ARM64.Imported

theorem sequential_words_pc (words : List (BitVec 32)) (s out : Arm64.State)
    (sequential : SequentialWords words) (executed : runWords words s = some out)
    (running : out.status = .Running) : out.pc = s.pc + BitVec.ofNat 64 (4 * words.length) := by
  induction words generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    simp
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have nextRunning := runWords_running_before rest _ out sequential.tail.permitted executed running
      have nextPC := sequential_pc instruction (sequential word (by simp) instruction decoded) s nextRunning
      have lastPC := ih _ sequential.tail executed
      rw [lastPC, nextPC]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
      ac_rfl

def middleChunk (offset beforeCount afterCount : Nat) :=
  imageSlice offset beforeCount ++ ([imageWords[offset + beforeCount]!] ++ imageSlice (offset + beforeCount + 1) afterCount)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem middle_linear_path (base : BitVec 64) (offset beforeCount afterCount : Nat) (s out : Arm64.State)
    (bound : offset + beforeCount + 1 + afterCount ≤ 151)
    (beforeSequential : SequentialWords (imageSlice offset beforeCount))
    (afterSequential : SequentialWords (imageSlice (offset + beforeCount + 1) afterCount))
    (pc : s.pc = base + BitVec.ofNat 64 (4 * offset))
    (endPC : out.pc = s.pc + BitVec.ofNat 64 (4 * (beforeCount + 1 + afterCount)))
    (executed : runWords (middleChunk offset beforeCount afterCount) s = some out) (running : out.status = .Running) :
    StaticPath base (middleChunk offset beforeCount afterCount) s := by
  obtain ⟨branchBefore, beforeExec, restExec⟩ := runWords_append_split (imageSlice offset beforeCount)
    ([imageWords[offset + beforeCount]!] ++ imageSlice (offset + beforeCount + 1) afterCount) s out executed
  obtain ⟨branchAfter, branchExec, afterExec⟩ := runWords_append_split [imageWords[offset + beforeCount]!]
    (imageSlice (offset + beforeCount + 1) afterCount) branchBefore out restExec
  have afterRunning := runWords_running_before _ branchAfter out afterSequential.permitted afterExec running
  have beforeRunning := runWords_running_before _ branchBefore branchAfter
    (image_single_permitted ⟨offset + beforeCount, by omega⟩) branchExec afterRunning
  obtain ⟨beforePath, beforePC⟩ := sequential_slice_path base offset beforeCount s branchBefore
    (by omega) beforeSequential pc beforeExec beforeRunning
  have suffixPC := sequential_words_pc _ branchAfter out afterSequential afterExec running
  rw [image_slice_length _ _ (by omega)] at suffixPC
  have totalPC : out.pc = (base + BitVec.ofNat 64 (4 * (offset + beforeCount + 1))) + BitVec.ofNat 64 (4 * afterCount) := by
    rw [endPC, pc]
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  have afterPC : branchAfter.pc = base + BitVec.ofNat 64 (4 * (offset + beforeCount + 1)) := by
    have equality := suffixPC.symm.trans totalPC
    have cancelled := congrArg (fun p : BitVec 64 => p - BitVec.ofNat 64 (4 * afterCount)) equality
    simpa only [BitVec.add_sub_cancel] using cancelled
  have branchPath := image_single_path base ⟨offset + beforeCount, by omega⟩ branchBefore branchAfter beforePC branchExec
  have afterPath := (sequential_slice_path base (offset + beforeCount + 1) afterCount branchAfter out
    (by omega) afterSequential afterPC afterExec running).1
  have restPath := StaticPath.append branchExec branchPath afterPath
  exact StaticPath.append beforeExec beforePath restPath

def middleTrailingB (offset beforeCount afterCount : Nat) :=
  middleChunk offset beforeCount afterCount ++ [imageWords[offset + beforeCount + 1 + afterCount]!]

theorem single_b_pc (word : BitVec 32) (delta : BitVec 64) (s out : Arm64.State)
    (decoded : Arm64.decode word = some (.b delta)) (executed : runWords [word] s = some out) :
    out.pc = s.pc + delta := by
  simp only [runWords, decoded, Option.bind_some, Arm64.execInstWithSvc, Option.some.injEq] at executed
  subst out
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem middle_trailing_b_path (base : BitVec 64) (offset beforeCount afterCount : Nat)
    (delta : BitVec 64) (s out : Arm64.State)
    (bound : offset + beforeCount + 1 + afterCount < 151)
    (beforeSequential : SequentialWords (imageSlice offset beforeCount))
    (afterSequential : SequentialWords (imageSlice (offset + beforeCount + 1) afterCount))
    (decoded : Arm64.decode imageWords[offset + beforeCount + 1 + afterCount]! = some (.b delta))
    (pc : s.pc = base + BitVec.ofNat 64 (4 * offset))
    (endPC : out.pc = (s.pc + BitVec.ofNat 64 (4 * (beforeCount + 1 + afterCount))) + delta)
    (executed : runWords (middleTrailingB offset beforeCount afterCount) s = some out) (running : out.status = .Running) :
    StaticPath base (middleTrailingB offset beforeCount afterCount) s := by
  obtain ⟨mid, prefixExec, branchExec⟩ := runWords_append_split (middleChunk offset beforeCount afterCount)
    [imageWords[offset + beforeCount + 1 + afterCount]!] s out executed
  have midRunning := runWords_running_before _ mid out
    (image_single_permitted ⟨offset + beforeCount + 1 + afterCount, bound⟩) branchExec running
  have finalPC := single_b_pc _ delta mid out decoded branchExec
  have midPC : mid.pc = s.pc + BitVec.ofNat 64 (4 * (beforeCount + 1 + afterCount)) := by
    have equality := finalPC.symm.trans endPC
    have cancelled := congrArg (fun p : BitVec 64 => p - delta) equality
    simpa only [BitVec.add_sub_cancel] using cancelled
  have prefixPath := middle_linear_path base offset beforeCount afterCount s mid (by omega)
    beforeSequential afterSequential pc midPC prefixExec midRunning
  have address : mid.pc = base + BitVec.ofNat 64 (4 * (offset + beforeCount + 1 + afterCount)) := by
    rw [midPC, pc]
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  have branchPath := image_single_path base ⟨offset + beforeCount + 1 + afterCount, by omega⟩ mid out address branchExec
  exact StaticPath.append prefixExec prefixPath branchPath

end Crypto.ARM64.Imported
