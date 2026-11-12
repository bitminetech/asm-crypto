import Proofs.ARM64.ImportedCycles

/-!
One recorded schedule body plus ADD/CMP/B.LO control, over the upstream ISA.
The theorem retains the exact memory-store transition, the FIPS word-vector
update, branch destination and all state outside the declared work registers,
PC, condition flags and memory. Fetching and complete loops remain separate.
-/
namespace Crypto.ARM64.Imported

def nonMemory (s : Arm64.State) : Arm64.State := { controlStable s with mem := Arm64.Memory.empty }
@[simp] theorem nonMemory_controlStable (s : Arm64.State) : nonMemory (controlStable s) = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_stable (s : Arm64.State) : nonMemory (stable s) = nonMemory s := by cases s; rfl
@[simp] theorem nonMemory_set_mem (s : Arm64.State) (m : Arm64.Memory) : nonMemory { s with mem := m } = nonMemory s := by cases s; rfl

def DataFrame (before after : Arm64.State) : Prop :=
  nonMemory after = nonMemory before ∧ nonvolatile after = nonvolatile before ∧
  after.readReg64 .x0 = before.readReg64 .x0 ∧
  after.readReg64 .x1 = before.readReg64 .x1 ∧
  after.readReg64 .x2 = before.readReg64 .x2 ∧
  after.readReg64 .x3 = before.readReg64 .x3 ∧
  after.readReg64 .x4 = before.readReg64 .x4 ∧
  after.readReg64 .x6 = before.readReg64 .x6

def scheduleCycleCode : List (BitVec 32) := scheduleCode ++ scheduleControlCode

theorem schedule_cycle (s : Arm64.State) (M : Vector (BitVec 32) 16) (t : Fin 64)
    (ht : 16 ≤ t.val) (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    ∃ after, runWords scheduleCycleCode s = some after ∧ DataFrame s after ∧
      after.pc = (if t.val + 1 < 64 then s.pc else s.pc + 72#64) ∧
      after.readReg64 .x5 = BitVec.ofNat 64 (t.val + 1) ∧
      after.mem = s.mem.write32 (scheduleAddress s) (scheduleValue s) ∧
      wordVector 64 after.mem after.sp =
        SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M t.val (wordVector 64 s.mem s.sp) := by
  have readable (k : Nat) (hk : k ≤ t.val) :
      s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * k))) 4 = true := by
    rw [schedule_back_address s t k hc hk]
    exact hr ⟨_, by have := t.isLt; omega⟩
  have h15 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc4#64) 4 = true := by
    exact readable 15 (by omega)
  have h2 : s.mem.canRead (scheduleAddress s + 0xfffffffffffffff8#64) 4 = true := by
    exact readable 2 (by omega)
  have h16 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc0#64) 4 = true := by
    exact readable 16 ht
  have h7 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffe4#64) 4 = true := by
    exact readable 7 (by omega)
  have write : s.mem.canWrite (scheduleAddress s) 4 = true := by
    rw [schedule_address_counter s t hc]
    exact hw t
  obtain ⟨body, hb, hvector⟩ := exists_of_map_some _ _ _ (schedule_ram_step s M t ht hc hr hw)
  have frame := schedule_frame s h15 h2 h16 h7 write
  rw [hb] at frame
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at frame
  obtain ⟨hst, hpc, hnv, h0, h1, h2', h3, h4, h5, h6⟩ := frame
  obtain ⟨after, ha, post⟩ := exists_of_map_some _ _ _
    (schedule_control_step body t (h5.trans hc))
  simp only [Prod.mk.injEq] at post
  obtain ⟨hst', hpc', hnv', _hwork', h0', h1', h2'', h3', h4', h5', h6'⟩ := post
  have eraseBody : nonMemory body = nonMemory s := by
    simpa only [nonMemory_stable, nonMemory_set_mem] using congrArg nonMemory hst
  have eraseAfter : nonMemory after = nonMemory body := by
    simpa only [nonMemory_controlStable] using congrArg nonMemory hst'
  have memBody : body.mem = s.mem.write32 (scheduleAddress s) (scheduleValue s) := by
    have result := congrArg Arm64.State.mem hst
    exact result
  have memAfter : after.mem = body.mem := by
    have result := congrArg Arm64.State.mem hst'
    exact result
  have spAfter : after.sp = body.sp := by
    have result := congrArg Arm64.State.sp hst'
    exact result
  refine ⟨after, ?_, ?_, ?_, h5', memAfter.trans memBody, ?_⟩
  · simp [scheduleCycleCode, runWords_append, hb, ha]
  · exact ⟨eraseAfter.trans eraseBody, hnv'.trans hnv,
      h0'.trans h0, h1'.trans h1, h2''.trans h2', h3'.trans h3, h4'.trans h4, h6'.trans h6⟩
  · rw [hpc', hpc]
    split <;> simp_all [BitVec.add_assoc, BitVec.add_sub_cancel]
  · rw [memAfter, spAfter]
    exact hvector

end Crypto.ARM64.Imported
