import Proofs.HMACSHA256.X86EntryConcurrency
import Proofs.HMACSHA256.X86Timing

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Baseline Crypto.Reference

theorem entry_public_execution {base : Val} {s t : Cpu} {keyA keyB msgA msgB : ByteList}
    {keyExtentA keyExtentB msgExtentA msgExtentB capacity : Nat} {authorityA authorityB : Authority}
    (left : EntryCall base s keyA msgA keyExtentA msgExtentA capacity authorityA)
    (right : EntryCall base t keyB msgB keyExtentB msgExtentB capacity authorityB)
    (rightsA : ScopedAuthority (entryBorrow base s keyExtentA msgExtentA capacity) authorityA)
    (rightsB : ScopedAuthority (entryBorrow base t keyExtentB msgExtentB capacity) authorityB)
    (envA : Environment (entryBorrow base s keyExtentA msgExtentA capacity))
    (envB : Environment (entryBorrow base t keyExtentB msgExtentB capacity))
    (same : EntryPublic s t keyA keyB msgA msgB)
    (link : s.mem.readSize .q (s.regs.get .rsp) = t.mem.readSize .q (t.regs.get .rsp))
    (profile : LinkedTimingProfile base) :
    ∃ outA outB events cost,
      CostedLinkedSchedule profile authorityA envA 0 s events outA cost ∧
      CostedLinkedSchedule profile authorityB envB 0 t events outB cost := by
  obtain ⟨outA, runA, valA, _⟩ := entry_execution_concurrent left rightsA envA
  obtain ⟨outB, runB, valB, _⟩ := entry_execution_concurrent right rightsB envB
  have events := entry_native_events_equal (base := base) (capacity := capacity) same
  have ret := valA.link.trans (link.trans valB.link.symm)
  rw [← events] at runB
  refine ⟨outA, outB, _, _, runA.costed profile, ?_⟩
  rw [ret]
  exact runB.costed profile

theorem key_public_execution {base : Val} {s t : Cpu} {a b : ByteList}
    {n m : Nat} {authorityA authorityB : Authority}
    (left : KeyCall base s a n authorityA) (right : KeyCall base t b m authorityB)
    (rightsA : ScopedAuthority (keyBorrow base s n) authorityA)
    (rightsB : ScopedAuthority (keyBorrow base t m) authorityB)
    (envA : Environment (keyBorrow base s n)) (envB : Environment (keyBorrow base t m))
    (same : KeyPublic s t a b)
    (link : s.mem.readSize .q (s.regs.get .rsp) = t.mem.readSize .q (t.regs.get .rsp))
    (profile : LinkedTimingProfile base) :
    ∃ outA outB events cost,
      CostedLinkedSchedule profile authorityA envA 0 s events outA cost ∧
      CostedLinkedSchedule profile authorityB envB 0 t events outB cost := by
  obtain ⟨outA, runA, _, _, _, retA, _⟩ := key_execution_concurrent left rightsA envA
  obtain ⟨outB, runB, _, _, _, retB, _⟩ := key_execution_concurrent right rightsB envB
  have ret := retA.trans (link.trans retB.symm)
  rw [← key_native_events_equal (base := base) same] at runB
  refine ⟨outA, outB, _, _, runA.costed profile, ?_⟩
  rw [ret]
  exact runB.costed profile

theorem finish_public_execution {base : Val} {s t : Cpu} {a b : ByteList} {k0 k1 : HmacKeyBlock}
    {n m : Nat} {authorityA authorityB : Authority}
    (left : FinishCall base s a k0 n authorityA) (right : FinishCall base t b k1 m authorityB)
    (rightsA : ScopedAuthority (finishBorrow base s n) authorityA)
    (rightsB : ScopedAuthority (finishBorrow base t m) authorityB)
    (envA : Environment (finishBorrow base s n)) (envB : Environment (finishBorrow base t m))
    (same : FinishPublic s t a b)
    (link : s.mem.readSize .q (s.regs.get .rsp) = t.mem.readSize .q (t.regs.get .rsp))
    (profile : LinkedTimingProfile base) :
    ∃ outA outB events cost,
      CostedLinkedSchedule profile authorityA envA 0 s events outA cost ∧
      CostedLinkedSchedule profile authorityB envB 0 t events outB cost := by
  obtain ⟨outA, runA, _, _, retA, _⟩ := finish_execution_concurrent left rightsA envA
  obtain ⟨outB, runB, _, _, retB, _⟩ := finish_execution_concurrent right rightsB envB
  have ret := retA.trans (link.trans retB.symm)
  rw [← finish_native_events_equal (base := base) (k0 := k0) (k1 := k1) same] at runB
  refine ⟨outA, outB, _, _, runA.costed profile, ?_⟩
  rw [ret]
  exact runB.costed profile

end Crypto.HMACSHA256.X86_64
