import Proofs.ARM64.ImportedBranchFetch

/-!
A static path ending at its first RET executes in the bounded memory-fetch
evaluator. This is a generic execution bridge, not the complete equal claim.
-/
namespace Crypto.ARM64.Imported

def NoReturns (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ r, Arm64.decode word ≠ some (.ret r)

theorem NoReturns.tail {word : BitVec 32} {rest : List (BitVec 32)}
    (noReturns : NoReturns (word :: rest)) : NoReturns rest := by
  intro w hw r
  exact noReturns w (by simp [hw]) r

theorem NoReturns.append {xs ys : List (BitVec 32)}
    (left : NoReturns xs) (right : NoReturns ys) : NoReturns (xs ++ ys) := by
  intro word member r
  cases List.mem_append.mp member with
  | inl h => exact left word h r
  | inr h => exact right word h r

theorem NoReturns.repeated {code : List (BitVec 32)} (noReturns : NoReturns code) (n : Nat) :
    NoReturns (List.replicate n code).flatten := by
  induction n with
  | zero => intro word member; simp at member
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    exact noReturns.append ih

theorem runToReturn_nonret (prog : Arm64.Program) (fuel : Nat) (s : Arm64.State)
    (instruction : Arm64.Instr) (running : s.status = .Running)
    (fetched : prog.fetchMem s.mem s.pc = some instruction)
    (afterRunning : (prog.evalInst instruction s).status = .Running)
    (notReturn : ∀ r, instruction ≠ .ret r) :
    runToReturn prog (fuel + 1) s = runToReturn prog fuel (prog.evalInst instruction s) := by
  cases instruction <;> simp_all [runToReturn]

theorem runToReturn_return (prog : Arm64.Program) (fuel : Nat) (s : Arm64.State)
    (r : Arm64.Reg) (running : s.status = .Running)
    (fetched : prog.fetchMem s.mem s.pc = some (.ret r))
    (afterRunning : (prog.evalInst (.ret r) s).status = .Running) :
    runToReturn prog (fuel + 1) s = some (prog.evalInst (.ret r) s) := by
  simp [runToReturn, running, fetched, afterRunning]

theorem runToReturn_of_staticPath (base : BitVec 64) (before : List (BitVec 32))
    (returnWord : BitVec 32) (returnReg : Arm64.Reg) (extra : Nat)
    (s out : Arm64.State) (decodedReturn : Arm64.decode returnWord = some (.ret returnReg))
    (noReturns : NoReturns before) (permitted : PermittedWords (before ++ [returnWord]))
    (loaded : (program base).CodeLoaded s.mem)
    (executed : runWords (before ++ [returnWord]) s = some out)
    (path : StaticPath base (before ++ [returnWord]) s) (running : out.status = .Running) :
    runToReturn (program base) (before.length + 1 + extra) s = some out := by
  induction before generalizing s with
  | nil =>
    simp only [List.nil_append, runWords, decodedReturn] at executed
    have outEq : Arm64.execInstWithSvc Arm64.noSyscalls (.ret returnReg) s = out := by
      simpa only [runWords, Option.bind_some, Option.some.injEq] using executed
    have parts : (program base).fetch s.pc = some (.ret returnReg) ∧ True := by
      simpa only [List.nil_append, StaticPath, decodedReturn] using path
    have allowed := permitted returnWord (by simp) (.ret returnReg) decodedReturn
    have afterRunning : (Arm64.execInstWithSvc Arm64.noSyscalls (.ret returnReg) s).status = .Running := by
      rw [outEq]; exact running
    have beforeRunning := permitted_running_before (.ret returnReg) allowed s afterRunning
    have result := runToReturn_return (program base) extra s returnReg beforeRunning
      (loaded_fetch_of_fetch loaded parts.1)
      (by rw [evalInst_permitted base (.ret returnReg) allowed]; exact afterRunning)
    simpa only [List.length_nil, Nat.zero_add, Nat.add_comm 1 extra,
      evalInst_permitted base (.ret returnReg) allowed, outEq] using result
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      change runWords (word :: (rest ++ [returnWord])) s = some out at executed
      rw [runWords, decoded] at executed
      change runWords (rest ++ [returnWord])
        (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have parts : (program base).fetch s.pc = some instruction ∧
          StaticPath base (rest ++ [returnWord]) (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [List.cons_append, StaticPath, decoded] using path
      have allowed := permitted word (by simp) instruction decoded
      have nextPermitted : PermittedWords (rest ++ [returnWord]) := permitted.tail
      have nextRunning := runWords_running_before _ _ out nextPermitted executed running
      have beforeRunning := permitted_running_before instruction allowed s nextRunning
      have notReturn : ∀ r, instruction ≠ .ret r := by
        intro r eq
        exact noReturns word (by simp) r (by rw [decoded, eq])
      have result := ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) noReturns.tail
        nextPermitted (permitted_codeLoaded instruction allowed s loaded) executed parts.2
      have step := runToReturn_nonret (program base) (rest.length + 1 + extra) s instruction
        beforeRunning (loaded_fetch_of_fetch loaded parts.1)
        (by rw [evalInst_permitted base instruction allowed]; exact nextRunning) notReturn
      rw [evalInst_permitted base instruction allowed] at step
      have fuelEq : (word :: rest).length + 1 + extra = (rest.length + 1 + extra) + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuelEq]
      exact step.trans result

end Crypto.ARM64.Imported
