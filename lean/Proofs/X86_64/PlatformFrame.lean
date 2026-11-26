import Proofs.X86_64.Execution

namespace Crypto.X86_64
open X86

/-- State carried by the upstream ISA beyond the GPRs, RIP, condition codes
and undefined-bit oracle used by the scalar code. -/
def platformState (s : Cpu) := (s.fsBase, s.gsBase, s.xmm, s.mxcsr, s.mmx, s.flags.df)

@[local simp] private theorem halt_frame (s : Cpu) (e : MsErr) :
    platformState (s.halt e) = platformState s := by cases h : s.ms <;> simp [Cpu.halt, h, platformState]

@[local simp] private theorem operand_frame (s : Cpu) (sz : Size) (nr : Val) (dst : Operand) (v : Val) :
    platformState (s.writeOperand sz nr dst v) = platformState s := by
  cases dst <;> first | rfl | exact halt_frame _ _

@[local simp] private theorem rip_frame (s : Cpu) (nr : Val) : platformState (s.setRip nr) = platformState s := rfl
@[local simp] private theorem checked_frame (s : Cpu) (nr : Val) : platformState (s.setRipChecked nr) = platformState s := by
  unfold Cpu.setRipChecked; split <;> first | rfl | exact halt_frame _ _
@[local simp] private theorem reg_frame (s : Cpu) (sz : Size) (r : GPR) (v : Val) (h : Bool) :
    platformState (s.setReg sz r v h) = platformState s := rfl
@[local simp] private theorem flags_frame (s : Cpu) (f : Flags) (df : f.df = s.flags.df) :
    platformState (s.setFlags f) = platformState s := by simp [platformState, Cpu.setFlags, df]
@[local simp] private theorem undef_frame (s : Cpu) : platformState s.undefBit.2 = platformState s := rfl
@[local simp] private theorem undef_df (s : Cpu) : s.undefBit.2.flags = s.flags := rfl
@[local simp] private theorem push_frame (s : Cpu) (sz : Size) (v : Val) :
    platformState (s.push sz v) = platformState s := rfl
@[local simp] private theorem pop_frame (s : Cpu) (sz : Size) :
    platformState (s.popValue sz).2 = platformState s := rfl

theorem scalar_platform_frame (i : Instr) (s : Cpu) (allowed : ScalarLeaf i) :
    platformState (X86.step i s) = platformState s := by
  rcases i with ⟨op,len⟩
  obtain ⟨form,h⟩ := allowed
  change op = form.op at h
  subst op
  by_cases stopped : s.stopped = true
  · rw [X86.step_stopped _ _ stopped]
  have live : s.stopped = false := Bool.eq_false_iff.mpr stopped
  cases form
  all_goals try cases ‹BinKind›
  all_goals try cases ‹Bool›
  all_goals simp [ScalarForm.op, X86.step, live] <;> repeat first | rfl | (split <;> try simp)

theorem Execution.platform {base s trace out} (run : Execution base s trace out) :
    platformState out = platformState s := by
  induction run with
  | nil => rfl
  | @cons s next out i trace fetched executed _ ih =>
    apply ih.trans
    cases h : s.stopped with
    | true => simp [stepLoaded, h, guard] at executed
    | false =>
      have eq : X86.step i s = next := by simpa [stepLoaded, h, guard, fetched] using executed
      rw [← eq]
      exact scalar_platform_frame i s (fetched_scalar fetched)

theorem sha256_platform_frame {base s message extent} (entry : CallerEntry base s message extent) :
    ∃ out, returnAt base (callSteps message.bytes.size) s = some out ∧
      CallResult s out message ∧ platformState out = platformState s := by
  obtain ⟨out, returned, result⟩ := sha256_serial _ _ _ _ entry
  obtain ⟨_, execution, _⟩ := returnAt_execution returned
  exact ⟨out, returned, result, execution.platform⟩

end Crypto.X86_64
