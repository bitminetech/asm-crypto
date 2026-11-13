import Proofs.ARM64.ImportedMemory
import Proofs.ARM64.ImportedSchedule

/-!
Connect the executed 15-instruction schedule body and actual stack-word layout
to the unchanged imported FIPS `specScheduleStep`. The counter must be in
16..63 and the 256-byte word workspace must provide the stated permissions.
-/
namespace Crypto.ARM64.Imported

theorem index_shift_two (t : Fin 64) :
    (BitVec.ofNat 64 t.val <<< 2) = BitVec.ofNat 64 (4 * t.val) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

theorem schedule_address_counter (s : Arm64.State) (t : Fin 64)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) :
    scheduleAddress s = s.sp + BitVec.ofNat 64 (4 * t.val) := by
  simp only [scheduleAddress, hc, index_shift_two]

theorem slot_address_back (base : BitVec 64) (t k : Nat) (hk : k ≤ t) :
    (base + BitVec.ofNat 64 (4 * t)) - BitVec.ofNat 64 (4 * k) =
      base + BitVec.ofNat 64 (4 * (t - k)) := by
  have hn : 4 * t = 4 * (t - k) + 4 * k := by omega
  rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem schedule_back_address (s : Arm64.State) (t : Fin 64) (k : Nat)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) (hk : k ≤ t.val) :
    scheduleAddress s + (-BitVec.ofNat 64 (4 * k)) =
      s.sp + BitVec.ofNat 64 (4 * (t.val - k)) := by
  rw [schedule_address_counter s t hc, ← BitVec.sub_eq_add_neg, slot_address_back _ _ _ hk]

theorem schedule_source_word (s : Arm64.State) (t : Fin 64) (k : Nat)
    (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val) (hk : k ≤ t.val) :
    s.mem.read32 (scheduleAddress s + (-BitVec.ofNat 64 (4 * k))) =
      (wordVector 64 s.mem s.sp)[t.val - k]! := by
  rw [schedule_back_address s t k hc hk]
  have hb : t.val - k < 64 := by have := t.isLt; omega
  simp [wordVector, hb]

theorem schedule_ram_step (s : Arm64.State) (M : Vector (BitVec 32) 16) (t : Fin 64)
    (ht : 16 ≤ t.val) (hc : s.readReg64 .x5 = BitVec.ofNat 64 t.val)
    (hr : ∀ i : Fin 64, s.mem.canRead (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true)
    (hw : ∀ i : Fin 64, s.mem.canWrite (s.sp + BitVec.ofNat 64 (4 * i.val)) 4 = true) :
    (runWords scheduleCode s).map (fun out => wordVector 64 out.mem out.sp) =
      some (SHS.Equiv.SHA256.Foldl.Schedule.specScheduleStep M t.val
        (wordVector 64 s.mem s.sp)) := by
  have readable (k : Nat) (hk : k ≤ t.val) :
      s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * k))) 4 = true := by
    rw [schedule_back_address s t k hc hk]
    exact hr ⟨_, by have := t.isLt; omega⟩
  have h15 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc4#64) 4 = true := by
    change s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * 15))) 4 = true
    exact readable 15 (by omega)
  have h2 : s.mem.canRead (scheduleAddress s + 0xfffffffffffffff8#64) 4 = true := by
    change s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * 2))) 4 = true
    exact readable 2 (by omega)
  have h16 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffc0#64) 4 = true := by
    change s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * 16))) 4 = true
    exact readable 16 ht
  have h7 : s.mem.canRead (scheduleAddress s + 0xffffffffffffffe4#64) 4 = true := by
    change s.mem.canRead (scheduleAddress s + (-BitVec.ofNat 64 (4 * 7))) 4 = true
    exact readable 7 (by omega)
  have write : s.mem.canWrite (scheduleAddress s) 4 = true := by
    rw [schedule_address_counter s t hc]
    exact hw t
  have value15 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffc4#64) =
      (wordVector 64 s.mem s.sp)[t.val - 15]! := by
    exact schedule_source_word s t 15 hc (by omega)
  have value2 : s.mem.read32 (scheduleAddress s + 0xfffffffffffffff8#64) =
      (wordVector 64 s.mem s.sp)[t.val - 2]! := by
    exact schedule_source_word s t 2 hc (by omega)
  have value16 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffc0#64) =
      (wordVector 64 s.mem s.sp)[t.val - 16]! := by
    exact schedule_source_word s t 16 hc ht
  have value7 : s.mem.read32 (scheduleAddress s + 0xffffffffffffffe4#64) =
      (wordVector 64 s.mem s.sp)[t.val - 7]! := by
    exact schedule_source_word s t 7 hc (by omega)
  have result := congrArg
    (Option.map (fun r : Arm64.Memory × BitVec 64 × BitVec 64 × Arm64.ExecStatus =>
      wordVector 64 r.1 r.2.1)) (schedule_computes s h15 h2 h16 h7 write)
  simp only [Option.map_map, Function.comp_def, Option.map_some] at result
  rw [schedule_address_counter s t hc, wordVector_store64,
    schedule_update_matches_spec s M (wordVector 64 s.mem s.sp) t ht value15 value2 value16 value7]
    at result
  exact result

end Crypto.ARM64.Imported
