import Proofs.RISCV64.Execution

namespace Crypto.RISCV64

private theorem image_size : image.size = 0x540 := by decide +kernel

theorem fetch_loaded (base : Addr) (s : CPU) (loaded : ImageLoaded base s.mem) :
    fetched base s = decodeAt (s.pc - base).toNat := by
  let off := (s.pc - base).toNat
  change decodeBytes (fun j => s.mem.read8 (base + BitVec.ofNat 64 j)) off =
    decodeBytes (fun j => image[j]!.toBitVec) off
  have limit : codeEnd = 0x416 := rfl
  unfold decodeBytes
  by_cases small : off % 2 = 0 ∧ off + 2 ≤ codeEnd
  · have b0 := loaded off (by rw [image_size]; omega)
    have b1 := loaded (off + 1) (by rw [image_size]; omega)
    by_cases full : off + 4 ≤ codeEnd
    · have b2 := loaded (off + 2) (by rw [image_size]; omega)
      have b3 := loaded (off + 3) (by rw [image_size]; omega)
      simp only [littleWord, b0, b1, b2, b3]
    · simp [small, full, guard, Bind.bind, Option.bind, b0, b1]
  · simp [small, guard, Bind.bind, Option.bind]

theorem checked_step_loaded (base : Addr) (s : CPU) (i : Instruction)
    (loaded : ImageLoaded base s.mem)
    (decoded : decodeAt (s.pc - base).toNat = some i)
    (allowed : (i.observations s).all (Access.permitted s.mem) = true) :
    checkedStep base s = some (i.step s, i.observations s, i.op == .ret) := by
  unfold checkedStep
  rw [fetch_loaded base s loaded, decoded]
  simp only [allowed, if_true]

/-- The abstract path and its permission witnesses suffice to run exactly to
the modeled return in byte memory. Each step checks its own instruction fetch
and the full width of every read or write. -/
inductive PermittedPath (base : Addr) : CPU → List Instruction → Prop where
  | nil (s : CPU) : PermittedPath base s []
  | cons {s : CPU} {i : Instruction} {tail : List Instruction}
      (loaded : ImageLoaded base s.mem)
      (allowed : (i.observations s).all (Access.permitted s.mem) = true)
      (rest : PermittedPath base (i.step s) tail) :
      PermittedPath base s (i :: tail)

theorem ImageExecution.to_first_return {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution base s code out) (permissions : PermittedPath base s code)
    (ret : ∃ i ∈ code, i.op = .ret) :
    runUntilReturn base s code.length = some out := by
  induction path with
  | nil => simp at ret
  | @cons s out i tail decoded last rest ih =>
    cases permissions with
    | cons loaded allowed next =>
      have step := checked_step_loaded base s i loaded decoded allowed
      by_cases h : i.op = .ret
      · obtain rfl := last h
        cases rest
        simp [runUntilReturn, step, h]
      · have inTail : ∃ j ∈ tail, j.op = .ret := by
          obtain ⟨j, hj, found⟩ := ret
          rcases List.mem_cons.mp hj with same | present
          · subst j
            exact (h found).elim
          · exact ⟨j, present, found⟩
        simp [runUntilReturn, step, h, ih next inTail]

end Crypto.RISCV64
