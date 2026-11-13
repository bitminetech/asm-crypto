import Proofs.ARM64.ImportedPCChoice
import Proofs.ARM64.ImportedLabeledCode
import Proofs.ARM64.ImportedCallReturn

/-!
Connect the exact instruction-index CFG to native PCs. Distinct decoded
instructions at alternative branch successors remove ambiguity in StaticPath;
no global injectivity of the AArch64 decoder is assumed.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem image_pc_offsets_checked : ∀ i : Fin 151,
    ((Arm64.decode imageWords[i.val]!).map fun instruction =>
      (pcOffsets instruction).all fun offset => decide
        (BitVec.ofNat 64 (4 * i.val) + offset ∈
          (successorIndices i.val).map fun j => BitVec.ofNat 64 (4 * j))).getD false = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem image_successor_decodes_checked : ∀ i : Fin 151,
    (successorIndices i.val).all (fun j => (successorIndices i.val).all fun k =>
      decide (Arm64.decode imageWords[j]! = Arm64.decode imageWords[k]! → j = k)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem image_nonreturn_checked : ∀ i : Fin 151,
    ((Arm64.decode imageWords[i.val]!).map nonReturnInstruction).getD false = decide (i.val ≠ 150) := by
  decide +kernel

theorem successor_decode_injective (i : Fin 151) (j k : Nat)
    (left : j ∈ successorIndices i.val) (right : k ∈ successorIndices i.val)
    (same : Arm64.decode imageWords[j]! = Arm64.decode imageWords[k]!) : j = k := by
  have checked := List.all_eq_true.mp (image_successor_decodes_checked i) j left
  have pair := List.all_eq_true.mp checked k right
  exact (of_decide_eq_true pair) same

theorem native_pc_candidates (base : BitVec 64) (i : Fin 151) (s : Arm64.State)
    (instruction : Arm64.Instr) (nonterminal : i.val ≠ 150)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction)
    (pc : s.pc = base + BitVec.ofNat 64 (4 * i.val))
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running) :
    ∃ j ∈ successorIndices i.val,
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc = base + BitVec.ofNat 64 (4 * j) := by
  have notReturn : ∀ r, instruction ≠ .ret r := by
    intro r same
    have checked := image_nonreturn_checked i
    simp only [decoded, Option.map_some, Option.getD_some] at checked
    simp [same, nonReturnInstruction] at checked
    exact nonterminal checked
  obtain ⟨offset, member, nextPC⟩ := permitted_pc_choice instruction s (image_permitted i instruction decoded) notReturn running
  have checked := image_pc_offsets_checked i
  simp only [decoded, Option.map_some, Option.getD_some] at checked
  have good := of_decide_eq_true (List.all_eq_true.mp checked offset member)
  obtain ⟨j, present, address⟩ := List.mem_map.mp good
  refine ⟨j, present, ?_⟩
  rw [nextPC, pc, BitVec.add_assoc, ← address]

theorem native_next_label (base : BitVec 64) (i j : Fin 151) (s : Arm64.State)
    (instruction : Arm64.Instr)
    (edge : labeledSuccessor i.val (.instruction j.val) = true)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction)
    (pc : s.pc = base + BitVec.ofNat 64 (4 * i.val))
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running)
    (nextFetched : (program base).fetch (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc =
      Arm64.decode imageWords[j.val]!) :
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc = base + BitVec.ofNat 64 (4 * j.val) := by
  have nextMember := labeledSuccessor_mem i.val j.val edge
  have nonterminal : i.val ≠ 150 := by
    intro last
    rw [last] at nextMember
    simp [successorIndices] at nextMember
  obtain ⟨k, member, actualPC⟩ := native_pc_candidates base i s instruction nonterminal decoded pc running
  have bound := successorIndices_bounded i.val k i.isLt member
  rw [actualPC, image_fetch base ⟨k, by omega⟩] at nextFetched
  have same := successor_decode_injective i k j.val member nextMember nextFetched
  simpa only [same] using actualPC

end Crypto.ARM64.Imported
