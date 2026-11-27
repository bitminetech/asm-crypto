import Proofs.HMACSHA256.ARM64ShaEntry
import Proofs.HMACSHA256.ARM64CallSites
import Proofs.HMACSHA256.LinkedExecution
import Proofs.ARM64.ImportedFetchTrace
import Proofs.ARM64.ImportedInstructionLocality

namespace Crypto.HMACSHA256.ARM64

open Crypto.ARM64.Imported

set_option maxRecDepth 8192
set_option maxHeartbeats 3600000

def hmacExtra : Arm64.Instr → Bool
  | .bl _ | .dataProc3 .. => true
  | _ => false

def hmacLocal (i : Arm64.Instr) : Bool :=
  permittedInstruction i || hmacExtra i

private def hmacSequential : Arm64.Instr → Bool
  | .dataProc3 .. => true
  | i => sequentialInstruction i

theorem local_running_before (i : Arm64.Instr) (s : Arm64.State)
    (allowed : hmacLocal i = true)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running) :
    s.status = .Running := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | extra
  · exact permitted_running_before i common s running
  · cases i <;> simp only [hmacExtra, Bool.false_eq_true] at extra
    all_goals simpa only [Arm64.execInstWithSvc, Arm64.execDataProc3, status_set_pc, status_advance,
      status_write_reg, status_write_reg64] using running

private theorem local_loaded {program : Arm64.Program} (i : Arm64.Instr) (s : Arm64.State)
    (allowed : hmacLocal i = true) (loaded : program.CodeLoaded s.mem) :
    program.CodeLoaded (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | extra
  · exact permitted_codeLoaded i common s loaded
  · cases i <;> simp only [hmacExtra, Bool.false_eq_true] at extra
    all_goals exact loaded

private theorem local_next (i : Arm64.Instr) (s : Arm64.State)
    (allowed : hmacSequential i = true)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls i s).status = .Running) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).pc = s.pc + 4#64 := by
  cases i
  case dataProc3 => rfl
  all_goals
    simp only [hmacSequential] at allowed
    apply sequential_pc
    · exact allowed
    · exact running

/-- Every local transition comes from a real fetch of the linked routine.
SHA-256 transitions are the actual-memory call theorem on the same state,
with its retired observations and return address. -/
inductive LinkedExecution (base : Addr) :
    Arm64.State → List InstructionObservation → Arm64.State → Prop where
  | nil (s : Arm64.State) : LinkedExecution base s [] s
  | localStep {r : Routine} {i : Arm64.Instr} {s out : Arm64.State} {observations}
      (body : r = entry ∨ r = key ∨ r = finish)
      (allowed : hmacLocal i = true)
      (running : s.status = .Running)
      (fetched : (programAt r (routineAddress base r)).fetchMem s.mem s.pc = some i)
      (tail : LinkedExecution base (Arm64.execInstWithSvc Arm64.noSyscalls i s) observations out) :
      LinkedExecution base s (instructionObservation i s :: observations) out
  | shaCall {s mid out : Arm64.State} {message : Crypto.Reference.ByteList} {observations rest}
      (run : ShaCallResult (shaAddress base) s mid message observations)
      (tail : LinkedExecution base mid rest out) :
      LinkedExecution base s (observations ++ rest) out

theorem LinkedExecution.append {base : Addr} {s mid out : Arm64.State} {before after}
    (front : LinkedExecution base s before mid) (back : LinkedExecution base mid after out) :
    LinkedExecution base s (before ++ after) out := by
  induction front with
  | nil => exact back
  | localStep routine allowed running fetched _ ih =>
    exact .localStep routine allowed running fetched (ih back)
  | shaCall run _ ih =>
    simpa only [List.append_assoc] using LinkedExecution.shaCall run (ih back)

theorem LinkedExecution.keeps_code {base : Addr} {s out : Arm64.State} {observations}
    (run : LinkedExecution base s observations out) (prog : Arm64.Program)
    (loaded : prog.CodeLoaded s.mem) : prog.CodeLoaded out.mem := by
  induction run with
  | nil => exact loaded
  | localStep _ allowed _ _ _ ih => exact ih (local_loaded _ _ allowed loaded)
  | shaCall called _ ih =>
    apply ih
    exact runWords_codeLoaded _ _ _ (whole_call_permitted _) loaded
      (fetch_observed_raw_execution _ _ _ _ called.trace)

private def rangeVocabulary : List Arm64.Instr → Bool
  | [] => true
  | [i] => hmacLocal i
  | i :: j :: rest => hmacLocal i && hmacSequential i && rangeVocabulary (j :: rest)

def rangeSupported (r : Routine) (off n : Nat) : Bool :=
  ((decodeRange r off n).map rangeVocabulary).getD false

private theorem decodeRange_succ (r : Routine) (off n : Nat) :
    decodeRange r off (n + 1) = do
      let i ← decodeAt r off
      let rest ← decodeRange r (off + 4) n
      return i :: rest := by
  have next (j : Nat) : off + 4 * j.succ = off + 4 + 4 * j := by omega
  simp only [decodeRange, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Function.comp_def,
    Nat.mul_zero, Nat.add_zero, next]

private theorem decoded_range_head {r : Routine} {off n : Nat} {code : List Arm64.Instr}
    (decoded : decodeRange r off (n + 1) = some code) :
    ∃ i rest, code = i :: rest ∧ decodeAt r off = some i ∧
      decodeRange r (off + 4) n = some rest := by
  rw [decodeRange_succ] at decoded
  cases head : decodeAt r off with
  | none => simp [head] at decoded
  | some i =>
    cases tail : decodeRange r (off + 4) n with
    | none => simp [head, tail] at decoded
    | some rest =>
      exact ⟨i, rest, (by simpa only [head, tail, Option.bind_some, bind, pure, Option.some.injEq] using decoded.symm),
        rfl, rfl⟩

private theorem decoded_range_length {r : Routine} {off n : Nat} {code : List Arm64.Instr}
    (decoded : decodeRange r off n = some code) : code.length = n := by
  induction n generalizing off code with
  | zero =>
    have empty : code = [] := Option.some.inj decoded.symm
    rw [empty]
    rfl
  | succ n ih =>
    obtain ⟨i, rest, rfl, _, tail⟩ := decoded_range_head decoded
    rw [List.length_cons, ih tail]

private theorem supported_running_before (code : List Arm64.Instr) (before : Arm64.State)
    (supported : rangeVocabulary code = true)
    (running : (runDecoded code before).status = .Running) : before.status = .Running := by
  induction code generalizing before with
  | nil => exact running
  | cons i rest ih =>
    cases rest with
    | nil => exact local_running_before i before supported running
    | cons j tail =>
      simp only [rangeVocabulary, Bool.and_eq_true] at supported
      exact local_running_before i before supported.1.1 (ih _ supported.2 running)

def decodedEvents : List Arm64.Instr → Arm64.State → List InstructionObservation
  | [], _ => []
  | i :: rest, s => instructionObservation i s ::
    decodedEvents rest (Arm64.execInstWithSvc Arm64.noSyscalls i s)

def rangeEvents (r : Routine) (off count : Nat) (s : Arm64.State) : List InstructionObservation :=
  decodedEvents ((decodeRange r off count).getD []) s

@[simp] theorem decodedEvents_length (code : List Arm64.Instr) (s : Arm64.State) :
    (decodedEvents code s).length = code.length := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [decodedEvents, List.length_cons, ih]

theorem decodedEvents_append (a b : List Arm64.Instr) (s : Arm64.State) :
    decodedEvents (a ++ b) s = decodedEvents a s ++ decodedEvents b (runDecoded a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change _ :: decodedEvents (rest ++ b) (Arm64.execInstWithSvc Arm64.noSyscalls i s) = _
    rw [ih]
    rfl

private theorem known_range_fetched (base : Addr) (r : Routine) (off n : Nat)
    (s : Arm64.State) (instrs : List Arm64.Instr)
    (body : r = entry ∨ r = key ∨ r = finish)
    (pc : s.pc = routineAddress base r + BitVec.ofNat 64 off)
    (fits : off + 4 * n ≤ 2 ^ 64)
    (loaded : (programAt r (routineAddress base r)).CodeLoaded s.mem)
    (decoded : decodeRange r off n = some instrs)
    (supported : rangeVocabulary instrs = true)
    (running : (runDecoded instrs s).status = .Running) :
    LinkedExecution base s (decodedEvents instrs s) (runDecoded instrs s) := by
  induction n generalizing off s instrs with
  | zero =>
    have empty : instrs = [] := Option.some.inj decoded.symm
    subst instrs
    exact .nil s
  | succ n ih =>
    obtain ⟨i, rest, rfl, instruction, tail⟩ := decoded_range_head decoded
    have allowed : hmacLocal i = true := by
      cases rest with
      | nil => exact supported
      | cons _ _ =>
        simp only [rangeVocabulary, Bool.and_eq_true] at supported
        exact supported.1.1
    have wasRunning := supported_running_before _ _ supported running
    have actual := fetch_at r (routineAddress base r) s off i loaded pc (by omega) instruction
    cases rest with
    | nil =>
      have noneLeft := decoded_range_length tail
      change 0 = n at noneLeft
      subst n
      exact .localStep body allowed wasRunning actual (.nil _)
    | cons j rest =>
      let next := Arm64.execInstWithSvc Arm64.noSyscalls i s
      obtain ⟨⟨_, sequential⟩, tailSupported⟩ := (show (hmacLocal i = true ∧ hmacSequential i = true) ∧
        rangeVocabulary (j :: rest) = true from by simpa only [rangeVocabulary, Bool.and_eq_true] using supported)
      have alive := supported_running_before _ next tailSupported running
      have nextPC : next.pc = routineAddress base r + BitVec.ofNat 64 (off + 4) := by
        rw [local_next i s sequential alive, pc, BitVec.ofNat_add, BitVec.add_assoc]
      exact .localStep body allowed wasRunning actual
        (ih _ next _ nextPC (by omega) (local_loaded i s allowed loaded) tail tailSupported running)

/-- Fetch a decoded straight-line range, allowing a control transfer in its
last instruction. Successful abstract execution establishes that every
intermediate state is running, and code loading is preserved by the stores. -/
theorem run_range_observes {base : Addr} {r : Routine} {off n : Nat} {s out : Arm64.State}
    (body : r = entry ∨ r = key ∨ r = finish)
    (pc : s.pc = routineAddress base r + BitVec.ofNat 64 off)
    (fits : off + 4 * n ≤ 2 ^ 64)
    (loaded : (programAt r (routineAddress base r)).CodeLoaded s.mem)
    (supported : rangeSupported r off n = true)
    (executed : runRange r off n s = some out) (running : out.status = .Running) :
    LinkedExecution base s (rangeEvents r off n s) out ∧ (rangeEvents r off n s).length = n := by
  cases decoded : decodeRange r off n with
  | none => simp [rangeSupported, decoded] at supported
  | some code =>
    have good : rangeVocabulary code = true := by simpa only [rangeSupported, decoded, Option.map_some, Option.getD_some] using supported
    have eq : runDecoded code s = out := by simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using executed
    simp only [rangeEvents, decoded, Option.getD_some, decodedEvents_length]
    refine ⟨?_, decoded_range_length decoded⟩
    rw [← eq]
    exact known_range_fetched base r off n s code body pc fits loaded decoded good (eq.symm ▸ running)

theorem run_range_fetched {base : Addr} {r : Routine} {off n : Nat} {s out : Arm64.State}
    (body : r = entry ∨ r = key ∨ r = finish)
    (pc : s.pc = routineAddress base r + BitVec.ofNat 64 off)
    (fits : off + 4 * n ≤ 2 ^ 64)
    (loaded : (programAt r (routineAddress base r)).CodeLoaded s.mem)
    (supported : rangeSupported r off n = true)
    (executed : runRange r off n s = some out) (running : out.status = .Running) :
    ∃ observations, LinkedExecution base s observations out ∧ observations.length = n := by
  have run := run_range_observes body pc fits loaded supported executed running
  exact ⟨_, run.1, run.2⟩

theorem run_range_running_before {r : Routine} {off n : Nat} {s out : Arm64.State}
    (supported : rangeSupported r off n = true)
    (executed : runRange r off n s = some out) (running : out.status = .Running) :
    s.status = .Running := by
  cases decoded : decodeRange r off n with
  | none => simp [rangeSupported, decoded] at supported
  | some code =>
    have good : rangeVocabulary code = true := by
      simpa only [rangeSupported, decoded, Option.map_some, Option.getD_some] using supported
    have eq : runDecoded code s = out := by
      simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using executed
    exact supported_running_before code s good (eq.symm ▸ running)

def rangeFallsThrough (r : Routine) (off n : Nat) : Bool :=
  ((decodeRange r off n).map (fun code => code.all hmacSequential)).getD false

private theorem sequential_range_pc (code : List Arm64.Instr) (s : Arm64.State)
    (supported : rangeVocabulary code = true) (straight : code.all hmacSequential = true)
    (running : (runDecoded code s).status = .Running) :
    (runDecoded code s).pc = s.pc + BitVec.ofNat 64 (4 * code.length) := by
  induction code generalizing s with
  | nil => simp [runDecoded, BitVec.add_zero]
  | cons i rest ih =>
    let mid := Arm64.execInstWithSvc Arm64.noSyscalls i s
    have tail : rangeVocabulary rest = true := by
      cases rest with
      | nil => rfl
      | cons j more =>
        simp only [rangeVocabulary, Bool.and_eq_true] at supported
        exact supported.2
    simp only [List.all_cons, Bool.and_eq_true] at straight
    have midRunning := supported_running_before rest mid tail running
    have pc := local_next i s straight.1 midRunning
    change (runDecoded rest mid).pc = s.pc + BitVec.ofNat 64 (4 * (rest.length + 1))
    rw [ih mid tail straight.2 running]
    change mid.pc = s.pc + 4#64 at pc
    rw [pc, Nat.mul_succ, Nat.add_comm (4 * rest.length) 4, BitVec.ofNat_add, BitVec.add_assoc]

theorem run_range_end {r : Routine} {off n : Nat} {s out : Arm64.State}
    (supported : rangeSupported r off n = true) (straight : rangeFallsThrough r off n = true)
    (executed : runRange r off n s = some out) (running : out.status = .Running) :
    out.pc = s.pc + BitVec.ofNat 64 (4 * n) := by
  cases decoded : decodeRange r off n with
  | none => simp [rangeSupported, decoded] at supported
  | some code =>
    have ok : rangeVocabulary code = true := by
      simpa only [rangeSupported, decoded, Option.map_some, Option.getD_some] using supported
    have seq : code.all hmacSequential = true := by
      simpa only [rangeFallsThrough, decoded, Option.map_some, Option.getD_some] using straight
    have eq : runDecoded code s = out := by
      simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using executed
    rw [← eq, ← decoded_range_length decoded]
    exact sequential_range_pc code s ok seq (eq.symm ▸ running)

theorem ShaCallResult.started {base : Addr} {s out : Arm64.State}
    {message : Crypto.Reference.ByteList} {observations} (run : ShaCallResult base s out message observations) :
    s.status = .Running :=
  runWords_running_before _ _ _ (whole_call_permitted _)
    (fetch_observed_raw_execution _ _ _ _ run.trace) run.running

structure GrantsPreserved (before after : Arm64.Memory) : Prop where
  write : ∀ p n, after.canWrite p n = before.canWrite p n
  read : ∀ p n, before.canRead p n = true → after.canRead p n = true

theorem GrantsPreserved.refl (memory : Arm64.Memory) : GrantsPreserved memory memory :=
  ⟨fun _ _ => rfl, fun _ _ readable => readable⟩

theorem GrantsPreserved.trans {a b c : Arm64.Memory}
    (first : GrantsPreserved a b) (second : GrantsPreserved b c) : GrantsPreserved a c :=
  ⟨fun p n => (second.write p n).trans (first.write p n),
    fun p n h => second.read p n (first.read p n h)⟩

private theorem write_guard_eq {before after : Arm64.Memory}
    (perm : ∀ p, after.perm p = before.perm p) (p : Addr) (n : Nat) :
    after.canWrite p n = before.canWrite p n := by
  unfold Arm64.Memory.canWrite
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [Arm64.Memory.allPerm, perm, ih]

private theorem sized_store_readable (m : Arm64.Memory) (size : Arm64.MemWidth) (dst value p : Addr)
    (n : Nat) (read : m.canRead p n = true) : (m.writeSized size dst value).canRead p n = true := by
  cases size
  · exact canRead_write8 _ _ _ _ _ read
  · exact canRead_write8 _ _ _ _ _ (canRead_write8 _ _ _ _ _ read)
  · exact canRead_write32 _ _ _ _ _ read
  · exact canRead_write64 _ _ _ _ _ read

private theorem local_readable (i : Arm64.Instr) (s : Arm64.State) (p : Addr) (n : Nat)
    (allowed : permittedInstruction i = true) (read : s.mem.canRead p n = true) :
    (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem.canRead p n = true := by
  cases i <;> simp only [permittedInstruction, Bool.false_eq_true] at allowed
  case str =>
    simp only [Arm64.execInstWithSvc, Arm64.execStr]
    repeat' split
    all_goals try simp only [mem_advance, locality_mem_writeReg64, locality_mem_status,
      locality_mem_setMem]
    all_goals first | exact read | exact sized_store_readable _ _ _ _ _ _ read
  case stp =>
    simp only [Arm64.execInstWithSvc, Arm64.execStp]
    repeat' split
    all_goals try simp only [mem_advance, locality_mem_writeReg64, locality_mem_status,
      locality_mem_setMem]
    all_goals
      first
      | exact read
      | exact sized_store_readable _ _ _ _ _ _ (sized_store_readable _ _ _ _ _ _ read)
  all_goals
    simp only [Arm64.execInstWithSvc, Arm64.execLdr, Arm64.execLdp,
      Arm64.execAddSubImm, Arm64.execLogicalImm, Arm64.execMoveWide, Arm64.execBitfield,
      Arm64.execLogicalShift, Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1]
    repeat' split
    all_goals exact read

private theorem local_grants (i : Arm64.Instr) (s : Arm64.State) (allowed : hmacLocal i = true) :
    GrantsPreserved s.mem (Arm64.execInstWithSvc Arm64.noSyscalls i s).mem := by
  simp only [hmacLocal, Bool.or_eq_true] at allowed
  rcases allowed with common | extra
  · exact ⟨write_guard_eq (permitted_preserves_permissions i common s),
      fun p n => local_readable i s p n common⟩
  · cases i <;> simp only [hmacExtra, Bool.false_eq_true] at extra
    all_goals exact GrantsPreserved.refl s.mem

private theorem word_grants (words : List (BitVec 32)) (s out : Arm64.State)
    (permitted : PermittedWords words) (executed : runWords words s = some out) :
    GrantsPreserved s.mem out.mem := by
  induction words generalizing s with
  | nil =>
    have same : s = out := Option.some.inj executed
    subst out
    exact GrantsPreserved.refl _
  | cons w words ih =>
    cases decoded : Arm64.decode w with
    | none => simp [runWords, decoded] at executed
    | some i =>
      have permit := permitted w (by simp) i decoded
      have tail := ih (Arm64.execInstWithSvc Arm64.noSyscalls i s) permitted.tail (by
        simpa only [runWords, decoded, Option.bind_some] using executed)
      exact (local_grants i s (by simp only [hmacLocal, permit, Bool.true_or])).trans tail

theorem ShaCallResult.grants {base : Addr} {s out : Arm64.State}
    {message : Crypto.Reference.ByteList} {observations} (run : ShaCallResult base s out message observations) :
    GrantsPreserved s.mem out.mem :=
  word_grants _ _ _ (whole_call_permitted _) (fetch_observed_raw_execution _ _ _ _ run.trace)

theorem LinkedExecution.grants {base : Addr} {s out : Arm64.State} {events}
    (run : LinkedExecution base s events out) : GrantsPreserved s.mem out.mem := by
  induction run with
  | nil => exact GrantsPreserved.refl _
  | localStep _ allowed _ _ _ ih => exact (local_grants _ _ allowed).trans ih
  | shaCall actual _ ih => exact actual.grants.trans ih

private theorem range_grants (code : List Arm64.Instr) (s : Arm64.State)
    (supported : rangeVocabulary code = true) :
    GrantsPreserved s.mem (runDecoded code s).mem := by
  induction code generalizing s with
  | nil => exact GrantsPreserved.refl _
  | cons i rest ih =>
    cases rest
    · exact local_grants _ _ supported
    · simp only [rangeVocabulary, Bool.and_eq_true] at supported
      exact (local_grants _ _ supported.1.1).trans (ih _ supported.2)

theorem run_range_grants {r : Routine} {off n : Nat} {s out : Arm64.State}
    (supported : rangeSupported r off n = true)
    (executed : runRange r off n s = some out) : GrantsPreserved s.mem out.mem := by
  cases decoded : decodeRange r off n with
  | none => simp [rangeSupported, decoded] at supported
  | some code =>
    have ok : rangeVocabulary code = true := by
      simpa only [rangeSupported, decoded, Option.map_some, Option.getD_some] using supported
    have eq : runDecoded code s = out := by
      simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using executed
    rw [← eq]
    exact range_grants code s ok

private theorem range_code_loaded (code : List Arm64.Instr) (s : Arm64.State) (prog : Arm64.Program)
    (supported : rangeVocabulary code = true) (loaded : prog.CodeLoaded s.mem) :
    prog.CodeLoaded (runDecoded code s).mem := by
  induction code generalizing s with
  | nil => exact loaded
  | cons i rest ih =>
    cases rest
    · exact local_loaded _ _ supported loaded
    · simp only [rangeVocabulary, Bool.and_eq_true] at supported
      exact ih _ supported.2 (local_loaded _ _ supported.1.1 loaded)

theorem run_range_keeps_code {r : Routine} {off n : Nat} {s out : Arm64.State}
    (supported : rangeSupported r off n = true)
    (executed : runRange r off n s = some out) {prog : Arm64.Program}
    (loaded : prog.CodeLoaded s.mem) : prog.CodeLoaded out.mem := by
  cases decoded : decodeRange r off n with
  | none => simp [rangeSupported, decoded] at supported
  | some code =>
    have ok : rangeVocabulary code = true := by
      simpa only [rangeSupported, decoded, Option.map_some, Option.getD_some] using supported
    have eq : runDecoded code s = out := by
      simpa only [runRange, decoded, Option.map_some, Option.some.injEq] using executed
    rw [← eq]
    exact range_code_loaded code s prog ok loaded

end Crypto.HMACSHA256.ARM64
