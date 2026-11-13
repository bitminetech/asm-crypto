import Proofs.ARM64.ImportedMemoryLocality

/-!
One-step locality for exactly the ordinary instruction families permitted by
the recorded SHA-256 image. Full-cell agreement on each serial access supplies
identical guards/load values; same-valued stores preserve protected cells.
No execution result or post-state agreement is assumed at function entry.

CPUState erases only memory and is a stricter internal foundation retaining
all other imported fields. CPUProjection instead retains architectural
regs/vregs/SP/PC/NZCV/status/FPSR/TPIDR_EL0 and clears memory/global fields.
CPUOverlay proves SHA instructions independent of filesystem, mappings,
oracle/signal bookkeeping and other global-tail fields, preserving each
side's own tail. Projected locality requires no equality between those tails,
so it does not freeze unrelated environment progress.

The complete concurrent execution fold and physical/profile correspondence
are separate from these supporting instruction-level lemmas.
-/
namespace Crypto.ARM64.Imported
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def CPUState (s : Arm64.State) : Arm64.State := s.setMem Arm64.Memory.empty

@[simp] theorem locality_setMem_self (s : Arm64.State) : s.setMem s.mem = s := by cases s; rfl
@[simp] theorem locality_setMem_twice (s : Arm64.State) (a b : Arm64.Memory) : (s.setMem a).setMem b = s.setMem b := by cases s; rfl
@[simp] theorem locality_CPU_setMem (s : Arm64.State) (m : Arm64.Memory) : CPUState (s.setMem m) = CPUState s := by cases s; rfl
@[simp] theorem locality_mem_setMem (s : Arm64.State) (m : Arm64.Memory) : (s.setMem m).mem = m := rfl
@[simp] theorem locality_read_setMem (s : Arm64.State) (m : Arm64.Memory) (r : Arm64.Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] theorem locality_address_setMem (s : Arm64.State) (m : Arm64.Memory) (addr : Arm64.AddrMode) :
    Arm64.evalAddrMode (s.setMem m) addr = Arm64.evalAddrMode s addr := by cases addr <;> rfl
@[simp] theorem locality_alignment_setMem (s : Arm64.State) (m : Arm64.Memory) (addr : Arm64.AddrMode) :
    Arm64.checkAddrSPAligned (s.setMem m) addr = Arm64.checkAddrSPAligned s addr := by cases addr <;> rfl
@[simp] theorem locality_advance_setMem (s : Arm64.State) (m : Arm64.Memory) :
    (s.setMem m).advancePC = s.advancePC.setMem m := by cases s; rfl
@[simp] theorem locality_status_setMem (s : Arm64.State) (m : Arm64.Memory) (status : Arm64.ExecStatus) :
    (s.setMem m).setStatus status = (s.setStatus status).setMem m := by cases s; rfl
@[simp] theorem locality_writeReg64_setMem (s : Arm64.State) (m : Arm64.Memory) (r : Arm64.Reg) (v : BitVec 64) :
    (s.setMem m).writeReg64 r v = (s.writeReg64 r v).setMem m := by cases s; rfl
@[simp] theorem locality_writeReg_setMem (s : Arm64.State) (m : Arm64.Memory)
    (w : Arm64.Width) (r : Arm64.Reg) (v : BitVec 64) :
    (s.setMem m).writeReg w r v = (s.writeReg w r v).setMem m := by cases s; rfl

@[simp] theorem locality_CPU_advance (s : Arm64.State) : CPUState s.advancePC = (CPUState s).advancePC := by cases s; rfl
@[simp] theorem locality_CPU_status (s : Arm64.State) (status : Arm64.ExecStatus) :
    CPUState (s.setStatus status) = (CPUState s).setStatus status := by cases s; rfl
@[simp] theorem locality_CPU_writeReg64 (s : Arm64.State) (r : Arm64.Reg) (v : BitVec 64) :
    CPUState (s.writeReg64 r v) = (CPUState s).writeReg64 r v := by cases s; rfl
@[simp] theorem locality_mem_writeReg64 (s : Arm64.State) (r : Arm64.Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; rfl
@[simp] theorem locality_mem_status (s : Arm64.State) (status : Arm64.ExecStatus) :
    (s.setStatus status).mem = s.mem := by cases s; rfl

theorem locality_state_of_CPU (left right : Arm64.State) (same : CPUState left = CPUState right) :
    right = left.setMem right.mem := by
  have restored := congrArg (fun s : Arm64.State => s.setMem right.mem) same
  simpa only [CPUState, locality_setMem_twice, locality_setMem_self] using restored.symm

def memoryFreeInstruction : Arm64.Instr → Bool
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield ..
  | .extr .. | .logicalShift .. | .addSubShift .. | .addSubExt .. | .dataProc1 ..
  | .b .. | .bCond .. | .cbz .. | .ret .. => true
  | _ => false

theorem memory_free_setMem (instruction : Arm64.Instr) (free : memoryFreeInstruction instruction = true)
    (s : Arm64.State) (m : Arm64.Memory) :
    Arm64.execInstWithSvc Arm64.noSyscalls instruction (s.setMem m) =
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).setMem m := by
  cases instruction <;> simp only [memoryFreeInstruction, Bool.false_eq_true] at free
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1,
    Arm64.State.setMem, Arm64.State.advancePC, Arm64.State.setPC,
    Arm64.State.setPState, Arm64.State.writeReg, Arm64.State.writeReg64,
    Arm64.State.readReg, Arm64.State.readReg64, Arm64.State.readReg32]
  all_goals repeat' split
  all_goals rfl

theorem locality_ldr_setMem (width : Arm64.Width) (size : Arm64.MemWidth) (signed : Bool)
    (rt : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) (m : Arm64.Memory)
    (range : CellsOnRange s.mem m (Arm64.evalAddrMode s addr).1 size.bytes) :
    Arm64.execLdr width size signed rt addr (s.setMem m) =
      (Arm64.execLdr width size signed rt addr s).setMem m := by
  have guard := (canRead_cells_eq s.mem m _ _ range).symm
  have value := (readSized_cells_eq s.mem m _ size signed range).symm
  simp only [Arm64.execLdr, locality_alignment_setMem, locality_address_setMem,
    locality_mem_setMem, guard, value]
  repeat' split
  all_goals simp only [locality_status_setMem, locality_writeReg64_setMem,
    locality_writeReg_setMem, locality_advance_setMem]

def pairSize (width : Arm64.Width) (signed : Bool) : Arm64.MemWidth :=
  if signed then .W32 else match width with | .W32 => .W32 | .W64 => .X64

def pairStep (width : Arm64.Width) (signed : Bool) : BitVec 64 :=
  if signed then 4#64 else match width with | .W32 => 4#64 | .W64 => 8#64

theorem locality_ldp_setMem (width : Arm64.Width) (signed : Bool) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) (m : Arm64.Memory)
    (first : CellsOnRange s.mem m (Arm64.evalAddrMode s addr).1 (pairSize width signed).bytes)
    (second : CellsOnRange s.mem m ((Arm64.evalAddrMode s addr).1 + pairStep width signed) (pairSize width signed).bytes) :
    Arm64.execLdp width signed rt1 rt2 addr (s.setMem m) =
      (Arm64.execLdp width signed rt1 rt2 addr s).setMem m := by
  cases width <;> cases signed
  all_goals dsimp only [pairSize, pairStep] at first second
  case W32.false =>
    have guard1 := (canRead_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 4 first).symm
    have guard2 := (canRead_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) 4 second).symm
    have value1 := (readSized_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 .W32 false first).symm
    have value2 := (readSized_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) .W32 false second).symm
    simp only [Arm64.execLdp, locality_alignment_setMem, locality_address_setMem, locality_mem_setMem]
    try simp only [guard1, guard2, value1, value2]
    repeat' split
    all_goals simp_all [locality_status_setMem, locality_writeReg64_setMem,
      locality_writeReg_setMem, locality_advance_setMem, Arm64.MemWidth.bytes]
  case W32.true =>
    have guard1 := (canRead_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 4 first).symm
    have guard2 := (canRead_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) 4 second).symm
    have value1 := (readSized_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 .W32 true first).symm
    have value2 := (readSized_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) .W32 true second).symm
    simp only [Arm64.execLdp, locality_alignment_setMem, locality_address_setMem, locality_mem_setMem]
    try simp only [guard1, guard2, value1, value2]
    repeat' split
    all_goals simp_all [locality_status_setMem, locality_writeReg64_setMem,
      locality_writeReg_setMem, locality_advance_setMem, Arm64.MemWidth.bytes]
  case W64.false =>
    have guard1 := (canRead_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 8 first).symm
    have guard2 := (canRead_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 8#64) 8 second).symm
    have value1 := (readSized_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 .X64 false first).symm
    have value2 := (readSized_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 8#64) .X64 false second).symm
    simp only [Arm64.execLdp, locality_alignment_setMem, locality_address_setMem, locality_mem_setMem]
    try simp only [guard1, guard2, value1, value2]
    repeat' split
    all_goals simp_all [locality_status_setMem, locality_writeReg64_setMem,
      locality_writeReg_setMem, locality_advance_setMem, Arm64.MemWidth.bytes]
  case W64.true =>
    have guard1 := (canRead_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 4 first).symm
    have guard2 := (canRead_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) 4 second).symm
    have value1 := (readSized_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 .W32 true first).symm
    have value2 := (readSized_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) .W32 true second).symm
    simp only [Arm64.execLdp, locality_alignment_setMem, locality_address_setMem, locality_mem_setMem]
    try simp only [guard1, guard2, value1, value2]
    repeat' split
    all_goals simp_all [locality_status_setMem, locality_writeReg64_setMem,
      locality_writeReg_setMem, locality_advance_setMem, Arm64.MemWidth.bytes]

@[simp] theorem locality_mem_writeReg (s : Arm64.State) (w : Arm64.Width) (r : Arm64.Reg) (value : BitVec 64) :
    (s.writeReg w r value).mem = s.mem := by cases s; rfl

theorem locality_ldr_mem (width : Arm64.Width) (size : Arm64.MemWidth) (signed : Bool)
    (rt : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) :
    (Arm64.execLdr width size signed rt addr s).mem = s.mem := by
  simp only [Arm64.execLdr]
  repeat' split
  all_goals simp only [mem_advance, locality_mem_writeReg, locality_mem_writeReg64, locality_mem_status]

theorem locality_ldp_mem (width : Arm64.Width) (signed : Bool) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) :
    (Arm64.execLdp width signed rt1 rt2 addr s).mem = s.mem := by
  simp only [Arm64.execLdp]
  repeat' split
  all_goals simp only [mem_advance, locality_mem_writeReg, locality_mem_writeReg64, locality_mem_status]

theorem locality_str (footprint : BitVec 64 → Prop) (size : Arm64.MemWidth)
    (rt : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) (m : Arm64.Memory)
    (same : SameCellsOn footprint s.mem m)
    (range : CellsOnRange s.mem m (Arm64.evalAddrMode s addr).1 size.bytes) :
    CPUState (Arm64.execStr size rt addr s) = CPUState (Arm64.execStr size rt addr (s.setMem m)) ∧
    SameCellsOn footprint (Arm64.execStr size rt addr s).mem (Arm64.execStr size rt addr (s.setMem m)).mem := by
  have guard := (canWrite_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 size.bytes range).symm
  constructor
  · simp only [Arm64.execStr, locality_alignment_setMem, locality_address_setMem,
      locality_mem_setMem, locality_read_setMem, guard]
    repeat' split
    all_goals simp only [locality_CPU_advance, locality_CPU_status,
      locality_CPU_writeReg64, locality_CPU_setMem]
  · simp only [Arm64.execStr, locality_alignment_setMem, locality_address_setMem,
      locality_mem_setMem, locality_read_setMem, guard]
    repeat' split
    all_goals simp only [mem_advance, locality_mem_writeReg64, locality_mem_status, locality_mem_setMem]
    all_goals first
      | exact same
      | exact @sameCells_writeSized footprint s.mem m same size (Arm64.evalAddrMode s addr).1 (s.readReg64 rt)

theorem locality_stp (footprint : BitVec 64 → Prop) (width : Arm64.Width)
    (rt1 rt2 : Arm64.Reg) (addr : Arm64.AddrMode) (s : Arm64.State) (m : Arm64.Memory)
    (same : SameCellsOn footprint s.mem m)
    (first : CellsOnRange s.mem m (Arm64.evalAddrMode s addr).1 (pairSize width false).bytes)
    (second : CellsOnRange s.mem m ((Arm64.evalAddrMode s addr).1 + pairStep width false) (pairSize width false).bytes) :
    CPUState (Arm64.execStp width rt1 rt2 addr s) = CPUState (Arm64.execStp width rt1 rt2 addr (s.setMem m)) ∧
    SameCellsOn footprint (Arm64.execStp width rt1 rt2 addr s).mem (Arm64.execStp width rt1 rt2 addr (s.setMem m)).mem := by
  cases width
  case W32 =>
    have guard1 := (canWrite_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 4 first).symm
    have guard2 := (canWrite_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 4#64) 4 second).symm
    constructor
    · simp only [Arm64.execStp, locality_alignment_setMem, locality_address_setMem,
        locality_mem_setMem, locality_read_setMem]
      try simp only [guard1, guard2]
      repeat' split
      all_goals simp only [locality_CPU_advance, locality_CPU_status,
        locality_CPU_writeReg64, locality_CPU_setMem]
    · simp only [Arm64.execStp, locality_alignment_setMem, locality_address_setMem,
        locality_mem_setMem, locality_read_setMem]
      try simp only [guard1, guard2]
      repeat' split
      all_goals simp only [mem_advance, locality_mem_writeReg64, locality_mem_status, locality_mem_setMem]
      all_goals first
        | exact same
        | exact @sameCells_writeSized footprint
            (s.mem.writeSized .W32 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            (m.writeSized .W32 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            (@sameCells_writeSized footprint s.mem m same .W32 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            .W32 ((Arm64.evalAddrMode s addr).1 + 4#64) (s.readReg64 rt2)
  case W64 =>
    have guard1 := (canWrite_cells_eq s.mem m (Arm64.evalAddrMode s addr).1 8 first).symm
    have guard2 := (canWrite_cells_eq s.mem m ((Arm64.evalAddrMode s addr).1 + 8#64) 8 second).symm
    constructor
    · simp only [Arm64.execStp, locality_alignment_setMem, locality_address_setMem,
        locality_mem_setMem, locality_read_setMem]
      try simp only [guard1, guard2]
      repeat' split
      all_goals simp only [locality_CPU_advance, locality_CPU_status,
        locality_CPU_writeReg64, locality_CPU_setMem]
    · simp only [Arm64.execStp, locality_alignment_setMem, locality_address_setMem,
        locality_mem_setMem, locality_read_setMem]
      try simp only [guard1, guard2]
      repeat' split
      all_goals simp only [mem_advance, locality_mem_writeReg64, locality_mem_status, locality_mem_setMem]
      all_goals first
        | exact same
        | exact @sameCells_writeSized footprint
            (s.mem.writeSized .X64 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            (m.writeSized .X64 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            (@sameCells_writeSized footprint s.mem m same .X64 (Arm64.evalAddrMode s addr).1 (s.readReg64 rt1))
            .X64 ((Arm64.evalAddrMode s addr).1 + 8#64) (s.readReg64 rt2)

theorem locality_of_readonly (footprint : BitVec 64 → Prop) (s : Arm64.State) (m : Arm64.Memory)
    (same : SameCellsOn footprint s.mem m) (step : Arm64.State → Arm64.State)
    (commute : step (s.setMem m) = (step s).setMem m)
    (unchanged : (step s).mem = s.mem) :
    CPUState (step s) = CPUState (step (s.setMem m)) ∧
    SameCellsOn footprint (step s).mem (step (s.setMem m)).mem := by
  have cpu := congrArg CPUState commute
  have erased : CPUState (step (s.setMem m)) = CPUState (step s) := by
    simpa only [locality_CPU_setMem] using cpu
  have memory := congrArg Arm64.State.mem commute
  change (step (s.setMem m)).mem = m at memory
  refine ⟨erased.symm, ?_⟩
  intro p hp
  rw [unchanged, memory]
  exact same p hp

theorem locality_memory_free (footprint : BitVec 64 → Prop) (instruction : Arm64.Instr)
    (free : memoryFreeInstruction instruction = true) (s : Arm64.State) (m : Arm64.Memory)
    (same : SameCellsOn footprint s.mem m) :
    CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) =
      CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction (s.setMem m)) ∧
    SameCellsOn footprint (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).mem
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction (s.setMem m)).mem := by
  have self := memory_free_setMem instruction free s s.mem
  have memory := congrArg Arm64.State.mem self
  have unchanged : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).mem = s.mem := by
    simpa only [locality_setMem_self, locality_mem_setMem] using memory
  exact locality_of_readonly footprint s m same (Arm64.execInstWithSvc Arm64.noSyscalls instruction)
    (memory_free_setMem instruction free s m) unchanged

def ProtectedAccesses (footprint : BitVec 64 → Prop) (instruction : Arm64.Instr) (s : Arm64.State) : Prop :=
  ∀ access ∈ dataAccesses instruction s, ∀ i, i < access.bytes → footprint (access.address + BitVec.ofNat 64 i)

theorem locality_range (footprint : BitVec 64 → Prop) (left right : Arm64.Memory)
    (same : SameCellsOn footprint left right) (access : DataAccess)
    (inside : ∀ i, i < access.bytes → footprint (access.address + BitVec.ofNat 64 i)) :
    CellsOnRange left right access.address access.bytes := by
  intro i hi
  exact same _ (inside i hi)

theorem locality_ldp_first_member (width : Arm64.Width) (signed : Bool) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) :
    ({ write := false, address := (Arm64.evalAddrMode s addr).1, bytes := (pairSize width signed).bytes } : DataAccess) ∈
      dataAccesses (.ldp width signed rt1 rt2 addr) s := by
  cases width <;> cases signed <;> simp [dataAccesses, pairSize]

theorem locality_ldp_second_member (width : Arm64.Width) (signed : Bool) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) :
    ({ write := false, address := (Arm64.evalAddrMode s addr).1 + pairStep width signed, bytes := (pairSize width signed).bytes } : DataAccess) ∈
      dataAccesses (.ldp width signed rt1 rt2 addr) s := by
  cases width <;> cases signed <;> simp [dataAccesses, pairSize, pairStep]

theorem locality_stp_first_member (width : Arm64.Width) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) :
    ({ write := true, address := (Arm64.evalAddrMode s addr).1, bytes := (pairSize width false).bytes } : DataAccess) ∈
      dataAccesses (.stp width rt1 rt2 addr) s := by
  cases width <;> simp [dataAccesses, pairSize]

theorem locality_stp_second_member (width : Arm64.Width) (rt1 rt2 : Arm64.Reg)
    (addr : Arm64.AddrMode) (s : Arm64.State) :
    ({ write := true, address := (Arm64.evalAddrMode s addr).1 + pairStep width false, bytes := (pairSize width false).bytes } : DataAccess) ∈
      dataAccesses (.stp width rt1 rt2 addr) s := by
  cases width <;> simp [dataAccesses, pairSize, pairStep]

theorem permitted_memory_locality (footprint : BitVec 64 → Prop) (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (s : Arm64.State) (m : Arm64.Memory)
    (same : SameCellsOn footprint s.mem m) (accessesProtected : ProtectedAccesses footprint instruction s) :
    CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) =
      CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction (s.setMem m)) ∧
    SameCellsOn footprint (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).mem
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction (s.setMem m)).mem := by
  let concrete := instruction
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at permitted
  case ldr width size signed rt addr =>
    let access : DataAccess := ⟨false, (Arm64.evalAddrMode s addr).1, size.bytes⟩
    have range := locality_range footprint s.mem m same access (accessesProtected access (by simp [access, dataAccesses]))
    exact locality_of_readonly footprint s m same (Arm64.execLdr width size signed rt addr)
      (locality_ldr_setMem width size signed rt addr s m range) (locality_ldr_mem width size signed rt addr s)
  case ldp width signed rt1 rt2 addr =>
    let firstAccess : DataAccess := ⟨false, (Arm64.evalAddrMode s addr).1, (pairSize width signed).bytes⟩
    let secondAccess : DataAccess := ⟨false, (Arm64.evalAddrMode s addr).1 + pairStep width signed, (pairSize width signed).bytes⟩
    have first := locality_range footprint s.mem m same firstAccess
      (accessesProtected firstAccess (locality_ldp_first_member width signed rt1 rt2 addr s))
    have second := locality_range footprint s.mem m same secondAccess
      (accessesProtected secondAccess (locality_ldp_second_member width signed rt1 rt2 addr s))
    exact locality_of_readonly footprint s m same (Arm64.execLdp width signed rt1 rt2 addr)
      (locality_ldp_setMem width signed rt1 rt2 addr s m first second) (locality_ldp_mem width signed rt1 rt2 addr s)
  case str size rt addr =>
    let access : DataAccess := ⟨true, (Arm64.evalAddrMode s addr).1, size.bytes⟩
    have range := locality_range footprint s.mem m same access (accessesProtected access (by simp [access, dataAccesses]))
    exact locality_str footprint size rt addr s m same range
  case stp width rt1 rt2 addr =>
    let firstAccess : DataAccess := ⟨true, (Arm64.evalAddrMode s addr).1, (pairSize width false).bytes⟩
    let secondAccess : DataAccess := ⟨true, (Arm64.evalAddrMode s addr).1 + pairStep width false, (pairSize width false).bytes⟩
    have first := locality_range footprint s.mem m same firstAccess
      (accessesProtected firstAccess (locality_stp_first_member width rt1 rt2 addr s))
    have second := locality_range footprint s.mem m same secondAccess
      (accessesProtected secondAccess (locality_stp_second_member width rt1 rt2 addr s))
    exact locality_stp footprint width rt1 rt2 addr s m same first second
  all_goals exact locality_memory_free footprint concrete (by rfl) s m same

theorem permitted_instruction_locality (footprint : BitVec 64 → Prop) (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (serial other : Arm64.State)
    (cpu : CPUState serial = CPUState other) (same : SameCellsOn footprint serial.mem other.mem)
    (accessesProtected : ProtectedAccesses footprint instruction serial)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).status = .Running) :
    CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) =
      CPUState (Arm64.execInstWithSvc Arm64.noSyscalls instruction other) ∧
    SameCellsOn footprint (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).mem
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).mem ∧
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).status = .Running := by
  have state := locality_state_of_CPU serial other cpu
  have core := permitted_memory_locality footprint instruction permitted serial other.mem same accessesProtected
  have after := congrArg (Arm64.execInstWithSvc Arm64.noSyscalls instruction) state
  have erased := core.1.trans (congrArg CPUState after).symm
  have status := congrArg Arm64.State.status erased
  change (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).status =
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).status at status
  refine ⟨erased, ?_, status.symm.trans running⟩
  intro p hp
  have memory := congrArg Arm64.State.mem after
  exact (core.2 p hp).trans (congrArg (fun m : Arm64.Memory => m.cells p) memory).symm

/-- Copy just architectural CPU fields and memory while retaining the other
state's filesystem, mappings, oracle/signal bookkeeping and other global tail. -/
def CPUOverlay (cpu globals : Arm64.State) : Arm64.State :=
  { globals with
    regs := cpu.regs
    vregs := cpu.vregs
    sp := cpu.sp
    pc := cpu.pc
    pstate := cpu.pstate
    status := cpu.status
    fpsr := cpu.fpsr
    tpidrEl0 := cpu.tpidrEl0
    mem := cpu.mem }

def GlobalTail (s : Arm64.State) : Arm64.State := CPUOverlay ({} : Arm64.State) s

@[simp] theorem locality_overlay_self (s : Arm64.State) : CPUOverlay s s = s := by cases s; rfl
@[simp] theorem locality_global_overlay (s g : Arm64.State) : GlobalTail (CPUOverlay s g) = GlobalTail g := by cases s; cases g; rfl

@[simp] theorem locality_overlay_read64 (s g : Arm64.State) (r : Arm64.Reg) :
    (CPUOverlay s g).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] theorem locality_overlay_read32 (s g : Arm64.State) (r : Arm64.Reg) :
    (CPUOverlay s g).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[simp] theorem locality_overlay_read (s g : Arm64.State) (w : Arm64.Width) (r : Arm64.Reg) :
    (CPUOverlay s g).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[simp] theorem locality_overlay_pc (s g : Arm64.State) : (CPUOverlay s g).pc = s.pc := rfl
@[simp] theorem locality_overlay_sp (s g : Arm64.State) : (CPUOverlay s g).sp = s.sp := rfl
@[simp] theorem locality_overlay_pstate (s g : Arm64.State) : (CPUOverlay s g).pstate = s.pstate := rfl
@[simp] theorem locality_overlay_mem (s g : Arm64.State) : (CPUOverlay s g).mem = s.mem := rfl
@[simp] theorem locality_overlay_address (s g : Arm64.State) (addr : Arm64.AddrMode) :
    Arm64.evalAddrMode (CPUOverlay s g) addr = Arm64.evalAddrMode s addr := by cases addr <;> rfl
@[simp] theorem locality_overlay_alignment (s g : Arm64.State) (addr : Arm64.AddrMode) :
    Arm64.checkAddrSPAligned (CPUOverlay s g) addr = Arm64.checkAddrSPAligned s addr := by cases addr <;> rfl
@[simp] theorem locality_overlay_write64 (s g : Arm64.State) (r : Arm64.Reg) (value : BitVec 64) :
    CPUOverlay (s.writeReg64 r value) g = (CPUOverlay s g).writeReg64 r value := by cases s; cases g; rfl
@[simp] theorem locality_overlay_write (s g : Arm64.State) (w : Arm64.Width) (r : Arm64.Reg) (value : BitVec 64) :
    CPUOverlay (s.writeReg w r value) g = (CPUOverlay s g).writeReg w r value := by cases s; cases g; rfl
@[simp] theorem locality_overlay_setMem (s g : Arm64.State) (m : Arm64.Memory) :
    CPUOverlay (s.setMem m) g = (CPUOverlay s g).setMem m := by cases s; cases g; rfl
@[simp] theorem locality_overlay_setPC (s g : Arm64.State) (pc : BitVec 64) :
    CPUOverlay (s.setPC pc) g = (CPUOverlay s g).setPC pc := by cases s; cases g; rfl
@[simp] theorem locality_overlay_advance (s g : Arm64.State) :
    CPUOverlay s.advancePC g = (CPUOverlay s g).advancePC := by cases s; cases g; rfl
@[simp] theorem locality_overlay_setPState (s g : Arm64.State) (pstate : Arm64.PState) :
    CPUOverlay (s.setPState pstate) g = (CPUOverlay s g).setPState pstate := by cases s; cases g; rfl
@[simp] theorem locality_overlay_setStatus (s g : Arm64.State) (status : Arm64.ExecStatus) :
    CPUOverlay (s.setStatus status) g = (CPUOverlay s g).setStatus status := by cases s; cases g; rfl
@[simp] theorem locality_overlay_if (condition : Prop) [Decidable condition] (left right g : Arm64.State) :
    CPUOverlay (if condition then left else right) g =
      if condition then CPUOverlay left g else CPUOverlay right g := by
  by_cases holds : condition <;> simp only [holds, ↓reduceIte]

theorem permitted_global_overlay (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (s globals : Arm64.State) :
    Arm64.execInstWithSvc Arm64.noSyscalls instruction (CPUOverlay s globals) =
      CPUOverlay (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) globals := by
  cases instruction <;> simp only [permittedInstruction, Bool.false_eq_true] at permitted
  all_goals simp only [Arm64.execInstWithSvc, Arm64.execAddSubImm, Arm64.execLogicalImm,
    Arm64.execMoveWide, Arm64.execBitfield, Arm64.execLogicalShift,
    Arm64.execAddSubShift, Arm64.execAddSubExt, Arm64.execDataProc1,
    Arm64.execLdr, Arm64.execStr, Arm64.execLdp, Arm64.execStp,
    locality_overlay_read64, locality_overlay_read32, locality_overlay_read,
    locality_overlay_pc, locality_overlay_pstate, locality_overlay_mem,
    locality_overlay_address, locality_overlay_alignment]
  all_goals repeat' split
  all_goals simp_all only [locality_overlay_write64, locality_overlay_write, locality_overlay_setMem,
    locality_overlay_setPC, locality_overlay_advance, locality_overlay_setPState, locality_overlay_setStatus,
    Bool.false_eq_true, ↓reduceIte]

theorem permitted_global_tail (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (s : Arm64.State) :
    GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = GlobalTail s := by
  have commute := permitted_global_overlay instruction permitted s s
  have tail := congrArg GlobalTail commute
  simpa only [locality_overlay_self, locality_global_overlay] using tail

def CPUProjection (s : Arm64.State) : Arm64.State := CPUOverlay (s.setMem Arm64.Memory.empty) ({} : Arm64.State)

@[simp] theorem locality_projection_CPUState (s : Arm64.State) : CPUProjection (CPUState s) = CPUProjection s := by cases s; rfl
@[simp] theorem locality_projection_overlay (s g : Arm64.State) : CPUProjection (CPUOverlay s g) = CPUProjection s := by cases s; cases g; rfl
@[simp] theorem locality_overlay_restore_projection (s g : Arm64.State) (m : Arm64.Memory) :
    CPUOverlay ((CPUProjection s).setMem m) g = CPUOverlay (s.setMem m) g := by cases s; cases g; rfl

theorem locality_state_of_projection (serial other : Arm64.State)
    (same : CPUProjection serial = CPUProjection other) :
    other = CPUOverlay (serial.setMem other.mem) other := by
  have restored := congrArg (fun cpu : Arm64.State => CPUOverlay (cpu.setMem other.mem) other) same
  simpa only [locality_overlay_restore_projection, locality_setMem_self, locality_overlay_self] using restored.symm

theorem permitted_projected_instruction_locality (footprint : BitVec 64 → Prop) (instruction : Arm64.Instr)
    (permitted : permittedInstruction instruction = true) (serial other : Arm64.State)
    (cpu : CPUProjection serial = CPUProjection other) (same : SameCellsOn footprint serial.mem other.mem)
    (accessesProtected : ProtectedAccesses footprint instruction serial)
    (running : (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).status = .Running) :
    CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) =
      CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction other) ∧
    SameCellsOn footprint (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).mem
      (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).mem ∧
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).status = .Running ∧
    GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) = GlobalTail serial ∧
    GlobalTail (Arm64.execInstWithSvc Arm64.noSyscalls instruction other) = GlobalTail other := by
  have state := locality_state_of_projection serial other cpu
  have core := permitted_memory_locality footprint instruction permitted serial other.mem same accessesProtected
  have actual := congrArg (Arm64.execInstWithSvc Arm64.noSyscalls instruction) state
  have after : Arm64.execInstWithSvc Arm64.noSyscalls instruction other =
      CPUOverlay (Arm64.execInstWithSvc Arm64.noSyscalls instruction (serial.setMem other.mem)) other :=
    actual.trans (permitted_global_overlay instruction permitted (serial.setMem other.mem) other)
  have projectedCore := congrArg CPUProjection core.1
  have projected : CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial) =
      CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction (serial.setMem other.mem)) := by
    simpa only [locality_projection_CPUState] using projectedCore
  have projectedActual := congrArg CPUProjection after
  have projectOther : CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction other) =
      CPUProjection (Arm64.execInstWithSvc Arm64.noSyscalls instruction (serial.setMem other.mem)) := by
    simpa only [locality_projection_overlay] using projectedActual
  have paired := projected.trans projectOther.symm
  have statuses := congrArg Arm64.State.status paired
  change (Arm64.execInstWithSvc Arm64.noSyscalls instruction serial).status =
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).status at statuses
  refine ⟨paired, ?_, statuses.symm.trans running, permitted_global_tail instruction permitted serial,
    permitted_global_tail instruction permitted other⟩
  intro p hp
  have memory := congrArg Arm64.State.mem after
  change (Arm64.execInstWithSvc Arm64.noSyscalls instruction other).mem =
    (Arm64.execInstWithSvc Arm64.noSyscalls instruction (serial.setMem other.mem)).mem at memory
  exact (core.2 p hp).trans (congrArg (fun m : Arm64.Memory => m.cells p) memory).symm

end Crypto.ARM64.Imported
