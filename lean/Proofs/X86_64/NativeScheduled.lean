import Proofs.X86_64.NativeSafety

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (memoryBytes32 disclosure_memoryBytes32_point disclosure_region_offset)

structure ScheduledResult (base : Val) (s out : Cpu) (message : Crypto.Reference.ByteList)
    (extent : Nat) (authority : Authority) (env : Environment (callBorrow base s extent)) (events : List Event) : Prop where
  execution : ScheduledExecution base env 0 s events out
  publicTrace : events = callEvents base s message
  steps : events.length = callSteps message.bytes.size
  last : events.getLast?.map (fun e => isReturn e.2.1) = some true
  first : ∀ e ∈ events.dropLast, isReturn e.2.1 = false
  live : out.ms = none
  pc : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  stack : out.regs.get .rsp = s.regs.get .rsp+8
  status : out.regs.get .rax = BitVec.ofNat 64 (Crypto.Reference.sha256 message).1
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  platform : platformState out = platformState s
  digest : memoryBytes32 (byteView out.mem) (s.regs.get .rsi) =
    (Crypto.Reference.sha256 message).2.map UInt8.toBitVec
  owned : ∀ e ∈ events, CallAccess (callBorrow base s extent) (ReportedAccess e.1 e.2.1 e.2.2)
  data : ∀ e ∈ events, ∀ a ∈ e.2.2, ∀ p, DataByte a p → canonical p = true ∧
    if a.write then authority.writable p else authority.readable p
  fetch : ∀ p, fetchByte events p → authority.executable p ∧ canonical p = true

theorem sha256_scheduled {base s message extent authority}
    (entry : PermissionEntry base s message extent authority) (env : Environment (callBorrow base s extent)) :
    ∃ out, ScheduledResult base s out message extent authority env (callEvents base s message) := by
  obtain ⟨serial,call⟩ := sha256_native_serial entry
  obtain ⟨mem,run,agree⟩ := call.execution.schedule env call.owned 0 s.mem (KeepsBorrowed.refl _ _)
  have digest : memoryBytes32 (byteView mem) (s.regs.get .rsi) =
      memoryBytes32 (byteView serial.mem) (s.regs.get .rsi) := by
    apply Vector.ext
    intro i hi
    have within := Crypto.ARM64.Imported.caller_region_contains_offset (outputRegion s) entry.outputValid i hi
    simp only [memoryBytes32,Vector.getElem_ofFn,byteView_read]
    exact agree _ (Or.inr (Or.inl within))
  refine ⟨{serial with mem := mem},⟨?_,rfl,call.steps,call.last,call.first,call.result.live,call.result.pc,
    call.result.stack,call.result.status,call.result.saved,call.platform,digest.trans call.result.digest,
    call.owned,call.data,call.fetch⟩⟩
  exact run

/-- Race freedom for the active invocation's virtual memory side. The
environment's alias-closed reporting law lifts this result to backing bytes. -/
theorem ScheduledExecution.no_races {base scope} {env : Environment scope} {tick s events out}
    (run : ScheduledExecution base env tick s events out) :
    events.length = 0 ∨ ∃ i operands, ¬ DataRace (ReportedAccess s.rip i operands) (env.event tick s) := by
  cases run with
  | nil => exact Or.inl rfl
  | cons fetch step obs frame race tail => exact Or.inr ⟨_,_,race⟩

end Crypto.X86_64
