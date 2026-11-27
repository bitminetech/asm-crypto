import Proofs.HMACSHA256.X86Program
import Proofs.X86_64.PlatformFrame

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Baseline

theorem ProgramStep.platform {base : Val} {authority : Authority} {s out : Cpu} {event : Event}
    (run : ProgramStep base authority s event out) : platformState out = platformState s := by
  cases run with
  | @localStep r s i accesses _ _ known live direction _ _ =>
    cases known with
    | scalar form => exact scalar_platform_frame _ _ form
    | call disp shape =>
      rw [shape]
      simp [step, Cpu.stopped, live]
      split <;> first | rfl | simp [Cpu.halt, live, platformState]
    | copy shape =>
      rw [shape]
      by_cases empty : s.regs.get .rcx = 0
      · rw [copyByte_empty s live empty]
        rfl
      · rw [copyByte_step s live direction empty]
        rfl
    | clear shape =>
      rw [shape]
      by_cases empty : s.regs.get .rcx = 0
      · rw [storeWord_empty s live empty]
        rfl
      · rw [storeWord_step s live direction empty]
        rfl

theorem LinkedExecution.platform {base : Val} {authority : Authority} {s out : Cpu} {events : List Event}
    (run : LinkedExecution base authority s events out) : platformState out = platformState s := by
  induction run with
  | nil => rfl
  | localStep head _ ih => exact ih.trans head.platform
  | shaCall callee _ ih => exact ih.trans callee.platform

end Crypto.HMACSHA256.X86_64
