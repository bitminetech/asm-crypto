import Proofs.RISCV64.FixedAccess

namespace Crypto.RISCV64

private def addressRegisters : List Reg := [2, 10, 11, 12]

private def noDestination (code : List Instruction) (regs : List Reg) : Bool :=
  code.all fun i => regs.all fun r => i.op.destination != some r

private theorem keeps_register {s : CPU} {code : List Instruction} {regs : List Reg}
    (check : noDestination code regs = true) (r : Reg) (member : r ∈ regs) :
    (run code s).reg r = s.reg r := by
  apply run_reg_unchanged
  intro i found
  have one := List.all_eq_true.mp check i found
  simpa using List.all_eq_true.mp one r member

private theorem cycle_index (s : CPU) (body : List Instruction) (limit : Nat) (back : Addr)
    (preserved : noDestination body [15] = true)
    (index : Nat) (indexBounds : index + 1 < 2^64) (limitBounds : limit < 2^64)
    (counter : s.reg 15 = BitVec.ofNat 64 index) :
    (run (body ++ latch (BitVec.ofNat 64 limit) back) s).reg 15 = BitVec.ofNat 64 (index+1) := by
  rw [run_append]
  have updated := keeps_register (s := s) preserved 15 (by simp)
  exact (latch_state (run body s) limit back index indexBounds limitBounds (updated.trans counter)).2.1

private theorem indexed_accesses (loop : Nat → List Instruction) (body : List Instruction)
    (limit : Nat) (back : Addr) (first count : Nat)
    (zero : loop 0 = [])
    (succ : ∀ n, loop (n+1) = loop n ++ (body ++ latch (BitVec.ofNat 64 limit) back))
    (stable : noDestination (body ++ latch (BitVec.ofNat 64 limit) back) addressRegisters = true)
    (keepsIndex : noDestination body [15] = true) (indices : first+count < 2^64)
    (limitFits : limit < 2^64)
    (accessRule : ∀ (s : CPU) (i : Nat), first ≤ i → i < first+count →
      s.reg 15 = BitVec.ofNat 64 i → ∀ access ∈ dataTrace (body ++ latch (BitVec.ofNat 64 limit) back) s,
        BlockData (s.reg 2) (s.reg 12) (s.reg 10) access)
    (s : CPU) (index : s.reg 15 = BitVec.ofNat 64 first) :
    let out := run (loop count) s
    (∀ r ∈ addressRegisters, out.reg r = s.reg r) ∧ out.reg 15 = BitVec.ofNat 64 (first+count) ∧
    (∀ access ∈ dataTrace (loop count) s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
  have prefixProof (n : Nat) (fits : n ≤ count) :
      let out := run (loop n) s
      (∀ r ∈ addressRegisters, out.reg r = s.reg r) ∧ out.reg 15 = BitVec.ofNat 64 (first+n) ∧
        (∀ access ∈ dataTrace (loop n) s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
    induction n with
    | zero => simpa only [zero, Nat.add_zero, run, List.foldl_nil, dataTrace, List.not_mem_nil,
        false_implies, implies_true, and_true] using
        (show (∀ r ∈ addressRegisters, s.reg r = s.reg r) ∧ s.reg 15 = BitVec.ofNat 64 first from
          ⟨fun _ _ => rfl, index⟩)
    | succ n ih =>
      obtain ⟨same, counter, bounded⟩ := ih (by omega)
      rw [succ, run_append, dataTrace_append]
      refine ⟨fun r hr => (keeps_register stable r hr).trans (same r hr), ?_, ?_⟩
      · exact cycle_index _ body limit back keepsIndex (first+n) (by omega) limitFits counter
      · intro access found
        rcases List.mem_append.mp found with early | late
        · exact bounded access early
        · have h := accessRule (run (loop n) s) (first+n) (by omega) (by omega) counter access late
          simpa only [same 2 (by decide), same 12 (by decide), same 10 (by decide)] using h
  exact prefixProof count (Nat.le_refl _)

theorem load_accesses (s : CPU) (first : s.reg 15 = 0) :
    let out := run (loadCode 16) s
    (∀ r ∈ addressRegisters, out.reg r = s.reg r) ∧ out.reg 15 = 16 ∧
    (∀ access ∈ dataTrace (loadCode 16) s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
  apply indexed_accesses loadCode inputWordBody 16 (-56) 0 16 rfl (fun _ => rfl)
    (by decide) (by decide) (by decide) (by decide) _ s first
  intro t j _ hj counter a ha
  exact load_cycle_within t ⟨j, hj⟩ counter a ha

theorem expansion_accesses (s : CPU) (first : s.reg 15 = 16) :
    let out := run (expansionCode 48) s
    (∀ r ∈ addressRegisters, out.reg r = s.reg r) ∧ out.reg 15 = 64 ∧
    (∀ access ∈ dataTrace (expansionCode 48) s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
  apply indexed_accesses expansionCode expansionBody 64 (-118) 16 48 rfl (fun _ => rfl)
    (by decide) (by decide) (by decide) (by decide) _ s first
  intro t j hlo hhi counter a ha
  exact expand_cycle_within t ⟨j, hhi⟩ hlo counter a ha

theorem round_accesses (s : CPU) (first : s.reg 15 = 0) :
    let out := run (roundCode 64) s
    (∀ r ∈ addressRegisters, out.reg r = s.reg r) ∧ out.reg 15 = 64 ∧
    (∀ access ∈ dataTrace (roundCode 64) s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
  apply indexed_accesses roundCode roundBody 64 (-186) 0 64 rfl (fun _ => rfl)
    (by decide) (by decide) (by decide) (by decide) _ s first
  intro t j _ hj counter a ha
  exact round_cycle_within t ⟨j, hj⟩ counter a ha

private structure BlockSegment (code : List Instruction) (s : CPU) : Prop where
  stable : ∀ r ∈ addressRegisters, (run code s).reg r = s.reg r
  within : ∀ access ∈ dataTrace code s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access

private theorem BlockSegment.append {a b : List Instruction} {s : CPU}
    (left : BlockSegment a s) (right : BlockSegment b (run a s)) : BlockSegment (a ++ b) s := by
  constructor
  · intro r hr; rw [run_append, right.stable r hr, left.stable r hr]
  · intro access found
    rw [dataTrace_append] at found
    rcases List.mem_append.mp found with early | late
    · exact left.within access early
    · simpa only [left.stable 2 (by decide), left.stable 12 (by decide), left.stable 10 (by decide)] using
        right.within access late

private theorem block_start_index (s : CPU) : (run [blockGuard, startWords] s).reg 15 = 0 := by
  let mid := blockGuard.step s
  change ((mid.advance 2).put 15 (mid.reg 0 + 0)).reg 15 = 0
  simp (config := { decide := true })
  exact reg_zero mid

private theorem load_hash_index (s : CPU) : (run loadHashBody s).reg 15 = 0 := by
  simp (config := { decide := true }) [run, loadHashBody, Instruction.step]

private theorem hash_load_within (s : CPU) : BlockSegment loadHashBody s := by
  refine ⟨keeps_register (by decide), ?_⟩
  intro access found
  obtain ⟨region, belongs, granted⟩ := fixed_accesses
    (show checkedFixedAccess loadHashBody [⟨false, 2, 288⟩] = true by decide) found
  have same : region = ⟨false, 2, 288⟩ := List.mem_singleton.mp belongs
  subst region
  cases access with
  | fetch => exact granted.elim
  | write => exact (Bool.false_ne_true granted.1).elim
  | read => exact .inl granted.2

set_option maxRecDepth 10000 in
private theorem feed_within (s : CPU) : BlockSegment feedForward s := by
  refine ⟨keeps_register (by decide), ?_⟩
  intro access found
  have fixed := show checkedFixedAccess feedForward [⟨false, 2, 288⟩, ⟨true, 2, 288⟩] = true by decide
  obtain ⟨region, belongs, granted⟩ := fixed_accesses fixed found
  cases access with
  | fetch => exact granted.elim
  | read =>
    rcases List.mem_cons.mp belongs with eq | eq
    · subst region; exact .inl granted.2
    · have same : region = ⟨true, 2, 288⟩ := List.mem_singleton.mp eq
      subst region; exact (Bool.false_ne_true granted.1.symm).elim
  | write =>
    rcases List.mem_cons.mp belongs with eq | eq
    · subst region; exact (Bool.false_ne_true granted.1).elim
    · have same : region = ⟨true, 2, 288⟩ := List.mem_singleton.mp eq
      subst region; exact granted.2

attribute [local irreducible] run loadCode expansionCode roundCode

theorem block_accesses (s : CPU) :
    let out := run blockCode s
    out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧ out.reg 11 = s.reg 11 ∧ out.reg 12 = s.reg 12 + 64 ∧
    (∀ access ∈ dataTrace blockCode s, BlockData (s.reg 2) (s.reg 12) (s.reg 10) access) := by
  let start := run [blockGuard, startWords] s
  let loaded := run (loadCode 16) start
  let expanded := run (expansionCode 48) loaded
  let working := run loadHashBody expanded
  let rounded := run (roundCode 64) working
  have first : BlockSegment [blockGuard, startWords] s := ⟨keeps_register (by decide), by
    intro a ha
    rw [empty_dataTrace (by decide)] at ha
    exact (List.not_mem_nil ha).elim⟩
  have ⟨loadKeep, expansionIndex, loadWithin⟩ := load_accesses start (block_start_index s)
  have ⟨expandKeep, _, expandWithin⟩ := expansion_accesses loaded expansionIndex
  have ⟨roundKeep, _, roundWithin⟩ := round_accesses working (load_hash_index expanded)
  have input : BlockSegment (loadCode 16) start := ⟨loadKeep, loadWithin⟩
  have schedule : BlockSegment (expansionCode 48) loaded := ⟨expandKeep, expandWithin⟩
  have rounds : BlockSegment (roundCode 64) working := ⟨roundKeep, roundWithin⟩
  have done := first.append (input.append (schedule.append
    ((hash_load_within expanded).append (rounds.append (feed_within rounded)))))
  have through (t : CPU) : (run advanceBlock t).reg 2 = t.reg 2 ∧
      (run advanceBlock t).reg 10 = t.reg 10 ∧ (run advanceBlock t).reg 11 = t.reg 11 ∧
      (run advanceBlock t).reg 12 = t.reg 12 + 64 := by
    simp (config := { decide := true }) [run, advanceBlock, Instruction.step, CPU.reg, CPU.put, CPU.advance]
  have stable (r : Reg) :
      (run blockCode s).reg r = (run advanceBlock
        (run ([blockGuard, startWords] ++ (loadCode 16 ++ (expansionCode 48 ++
        (loadHashBody ++ (roundCode 64 ++ feedForward))))) s)).reg r := by
    simp only [blockCode, run_append, List.append_assoc]
  refine ⟨(stable 2).trans ((through _).1.trans (done.stable 2 (by decide))),
    (stable 10).trans ((through _).2.1.trans (done.stable 10 (by decide))),
    (stable 11).trans ((through _).2.2.1.trans (done.stable 11 (by decide))), ?_, ?_⟩
  · exact (stable 12).trans ((through _).2.2.2.trans
      (congrArg (· + 64) (done.stable 12 (by decide))))
  · intro access found
    unfold blockCode at found
    rw [dataTrace_append, empty_dataTrace (code := advanceBlock) (by decide), List.append_nil] at found
    apply done.within access
    simpa only [List.append_assoc] using found

def BlockLoopData (stack payload constants : Addr) (blocks : Nat) : Access → Prop
  | .read addr w => InRegion stack 288 addr w ∨ InRegion payload (64*blocks) addr w ∨
      InRegion constants 256 addr w
  | .write addr w => InRegion stack 288 addr w
  | .fetch .. => False

private theorem BlockLoopData.widen {stack payload constants : Addr} {a : Access} {n m : Nat}
    (access : BlockLoopData stack payload constants n a) (size : n ≤ m) :
    BlockLoopData stack payload constants m a := by
  cases a with
  | fetch => exact access
  | write => exact access
  | read =>
    rcases access with h | ⟨off, fit, aligned, addr⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨off, by omega, aligned, addr⟩)
    · exact .inr (.inr h)

private theorem block_within_loop {stack payload constants : Addr} {a : Access} {n : Nat}
    (access : BlockData stack (payload + BitVec.ofNat 64 (64*n)) constants a) :
    BlockLoopData stack payload constants (n+1) a := by
  cases a with
  | fetch => exact access
  | write => exact access
  | read p w =>
    rcases access with h | h | h
    · exact .inl h
    · exact .inr (.inl (h.enclose (by omega) (by cases w <;> simp [Width.bytes, Nat.mul_mod])))
    · exact .inr (.inr h)

theorem block_loop_accesses (s : CPU) (n : Nat) :
    let out := run (blockLoop n) s
    out.reg 2 = s.reg 2 ∧ out.reg 10 = s.reg 10 ∧ out.reg 11 = s.reg 11 ∧
      out.reg 12 = s.reg 12 + BitVec.ofNat 64 (64*n) ∧
    (∀ access ∈ dataTrace (blockLoop n) s, BlockLoopData (s.reg 2) (s.reg 12) (s.reg 10) n access) := by
  induction n with
  | zero =>
    simp [blockLoop, run, dataTrace]
  | succ n ih =>
    obtain ⟨stack, constants, output, input, before⟩ := ih
    obtain ⟨stack', constants', output', input', next⟩ := block_accesses (run (blockLoop n) s)
    simp only [blockLoop, run_append, dataTrace_append]
    refine ⟨stack'.trans stack, constants'.trans constants, output'.trans output, ?_, ?_⟩
    · rw [input', input, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · intro access found
      rcases List.mem_append.mp found with early | late
      · exact (before access early).widen (by omega)
      · have h := next access late
        rw [stack, constants, input] at h
        exact block_within_loop h

end Crypto.RISCV64
