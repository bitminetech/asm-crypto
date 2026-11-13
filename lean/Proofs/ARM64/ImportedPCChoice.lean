import Proofs.ARM64.ImportedCycleFetch

/-! Native next-PC alternatives for the SHA-256 instruction vocabulary. -/
namespace Crypto.ARM64.Imported

def pcOffsets : Arm64.Instr → List (BitVec 64)
  | .b offset => [offset]
  | .bCond _ offset | .cbz _ _ _ offset => [4#64, offset]
  | .ret _ => []
  | _ => [4#64]

theorem permitted_pc_choice (instruction : Arm64.Instr) (s : Arm64.State)
    (allowed : permittedInstruction instruction = true)
    (notReturn : ∀ r, instruction ≠ .ret r)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).status = .Running) :
    ∃ offset ∈ pcOffsets instruction,
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc = s.pc + offset := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at allowed
  case b offset => exact ⟨offset, by simp [pcOffsets], rfl⟩
  case bCond condition offset =>
    simp only [Arm64.execInstWithSvc]
    split
    · exact ⟨offset, by simp [pcOffsets], rfl⟩
    · exact ⟨4#64, by simp [pcOffsets], rfl⟩
  case cbz width nonzero rt offset =>
    simp only [Arm64.execInstWithSvc]
    repeat' split
    all_goals first
      | exact ⟨offset, by simp [pcOffsets], rfl⟩
      | exact ⟨4#64, by simp [pcOffsets], rfl⟩
  case ret r => exact False.elim (notReturn r rfl)
  all_goals exact ⟨4#64, by simp [pcOffsets], sequential_pc _ rfl s running⟩

end Crypto.ARM64.Imported
