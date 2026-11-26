import Proofs.X86_64.Compression

namespace Crypto.X86_64
open X86

/-- One memory operand of a word instruction, including its full byte width. -/
structure WordAccess where
  write : Bool
  address : Val
  deriving DecidableEq

/-- These three forms are the only word operations that touch data memory.
Each access has width four, as in `WordInst.op` and the upstream step. -/
def WordInst.access (i : WordInst) (s : DataState) : Option WordAccess :=
  match i with
  | .rm _ _ src => some ⟨false, src.addr s⟩
  | .loadStack _ disp => some ⟨false, s.regs.get .rsp + disp⟩
  | .store dst _ => some ⟨true, dst.addr s⟩
  | _ => none

/-- Compare successive observations at actual ISA pre-states. The next
observation depends on the state returned by the preceding upstream step. -/
def wordTrace : WordBlock → Cpu → List (Val × Option WordAccess)
  | [], _ => []
  | (i,len)::rest, s =>
    (s.rip, i.access (project s)) :: wordTrace rest (X86.step ⟨i.op,len⟩ s)

/-- Public register values sufficing for the table and frame addressing
in the SHA-256 schedule and round bodies. -/
def wordBases (s : DataState) := (s.regs.get .rsp, s.regs.get .rbp, s.regs.get .rdi, s.regs.get .rbx)

private def tableBase (r : GPR) : Bool := decide (r = .rsp ∨ r = .rbp ∨ r = .rdi)
private def fixedReg (r : GPR) : Bool := tableBase r || decide (r = .rbx)

private def tracedWord : WordInst → Bool
  | .rr _ dst _ | .ror dst _ | .shr dst _ | .bswap dst | .loadStack dst _ => !fixedReg dst
  | .rm _ dst src => !fixedReg dst && tableBase src.base
  | .store dst _ => tableBase dst.base

private theorem stable (i : WordInst) (s : DataState) (ok : tracedWord i = true) :
    wordBases (i.eval s) = wordBases s := by
  cases i <;> simp [tracedWord, fixedReg, tableBase] at ok
  all_goals simp_all [WordInst.eval, DataState.put, wordBases, Regs.get_set_ne]

private theorem access_eq (i : WordInst) (s t : DataState) (ok : tracedWord i = true)
    (same : wordBases s = wordBases t) : i.access s = i.access t := by
  simp only [wordBases, Prod.mk.injEq] at same
  obtain ⟨sp,bp,di,bx⟩ := same
  have indexed (src : Indexed) (allowed : tableBase src.base = true) :
      src.addr s = src.addr t := by
    simp only [tableBase, decide_eq_true_eq] at allowed
    rcases allowed with h|h|h <;> simp [Indexed.addr, h, sp, bp, di, bx]
  cases i <;> simp_all [WordInst.access, tracedWord]

private theorem word_trace_eq (block : WordBlock) (s t : Cpu) (live : s.ms = none) (live' : t.ms = none)
    (pc : s.rip = t.rip) (bases : wordBases (project s) = wordBases (project t))
    (ok : block.all (fun p => tracedWord p.1) = true) :
    wordTrace block s = wordTrace block t := by
  induction block generalizing s t with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨i,len⟩ := pair
    obtain ⟨first,later⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨left,hl,pl⟩ := word_step i s len live
    obtain ⟨right,hr,pr⟩ := word_step i t len live'
    simp only [wordTrace, pc, access_eq i _ _ first bases]
    rw [ih _ _ hl hr (pl.trans (by rw [pr,pc])) (by rw [left,right,stable i _ first,stable i _ first,bases]) later]

/-- Independent initial message words, hash words, scratch bytes, arithmetic
flags and undefined-bit oracles give identical fetch and operand addresses. -/
theorem compression_word_traces (s t : Cpu) (live : s.ms = none) (live' : t.ms = none)
    (pc : s.rip = t.rip) (bases : wordBases (project s) = wordBases (project t)) :
    wordTrace inputBody s = wordTrace inputBody t ∧
    wordTrace expansionBody s = wordTrace expansionBody t ∧
    wordTrace roundBody s = wordTrace roundBody t :=
  ⟨word_trace_eq _ _ _ live live' pc bases (by decide +kernel),
   word_trace_eq _ _ _ live live' pc bases (by decide +kernel),
   word_trace_eq _ _ _ live live' pc bases (by decide +kernel)⟩

/-- Byte offsets relative to the live input block, schedule or constants. -/
private structure RelativeAccess where
  write : Bool
  base : GPR
  offset : Val

private def relativeAccess (idx : Val) : WordInst → Option RelativeAccess
  | .rm _ _ x => some ⟨false, x.base, idx * 4 + x.disp⟩
  | .store x _ => some ⟨true, x.base, idx * 4 + x.disp⟩
  | .loadStack _ disp => some ⟨false, .rsp, disp⟩
  | _ => none

private theorem relative_access (i : WordInst) (s : DataState) : i.access s =
    (relativeAccess (s.regs.get .rbx) i).map (fun a => ⟨a.write,s.regs.get a.base + a.offset⟩) := by
  cases i <;> simp [WordInst.access, relativeAccess, Indexed.addr, BitVec.add_assoc]

def tableBytes : GPR → Nat
  | .rbp => 64
  | .rsp | .rdi => 256
  | _ => 0

private def boundWord (idx : Nat) (i : WordInst) : Bool :=
  match relativeAccess (BitVec.ofNat 64 idx) i with
  | none => true
  | some a => decide (a.offset.toNat + 4 ≤ tableBytes a.base ∧ (a.write = true → a.base = .rsp))

private theorem table_bounds :
    (∀ i : Fin 16, inputBody.all (fun p => boundWord i.val p.1) = true) ∧
    (∀ i : Fin 48, expansionBody.all (fun p => boundWord (16+i.val) p.1) = true) ∧
    (∀ i : Fin 64, roundBody.all (fun p => boundWord i.val p.1) = true) := by
  decide +kernel

private theorem word_member (block : WordBlock) (s : Cpu) (live : s.ms = none)
    (ok : block.all (fun p => tracedWord p.1) = true)
    (e : Val × Option WordAccess) (member : e ∈ wordTrace block s) :
    ∃ p ∈ block, p.1.access (project s) = e.2 := by
  induction block generalizing s with
  | nil => simp [wordTrace] at member
  | cons pair tail ih =>
    obtain ⟨i,len⟩ := pair
    obtain ⟨first,later⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨step,valid,_⟩ := word_step i s len live
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self,rfl⟩
    · obtain ⟨p,hp,ea⟩ := ih _ valid later member
      refine ⟨p,List.mem_cons_of_mem _ hp,?_⟩
      rw [← ea, step]
      exact access_eq _ _ _ (List.all_eq_true.mp later p hp) (stable i _ first).symm

/-- All four bytes of the operand fit, and only the schedule can be written.
RBP names the current 64-byte input block, RSP the 256-byte schedule, and
RDI the 256-byte constant table. -/
def InWordWindow (s : Cpu) (a : WordAccess) : Prop :=
  ∃ (r : GPR) (offset : Nat), offset+4 ≤ tableBytes r ∧
    a.address = s.regs.get r + BitVec.ofNat 64 offset ∧ (a.write = true → r = .rsp)

private theorem safe_words (block : WordBlock) (idx : Nat) (s : Cpu) (live : s.ms = none)
    (index : s.regs.get .rbx = BitVec.ofNat 64 idx)
    (fixed : block.all (fun p => tracedWord p.1) = true)
    (safe : block.all (fun p => boundWord idx p.1) = true)
    (pc : Val) (a : WordAccess) (member : (pc,some a) ∈ wordTrace block s) : InWordWindow s a := by
  obtain ⟨p,hp,ha⟩ := word_member block s live fixed _ member
  have bound := List.all_eq_true.mp safe p hp
  rw [relative_access] at ha
  change (relativeAccess (s.regs.get .rbx) p.1).map _ = some a at ha
  rw [index] at ha
  cases off : relativeAccess (BitVec.ofNat 64 idx) p.1 with
  | none => simp [off] at ha
  | some x =>
    simp only [off,Option.map_some,Option.some.injEq] at ha
    subst a
    simp only [boundWord, off, decide_eq_true_eq] at bound
    exact ⟨x.base,x.offset.toNat,bound.1,by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq];rfl,bound.2⟩

theorem compression_word_bounds (s : Cpu) (live : s.ms = none) (pc : Val) (a : WordAccess) :
    (∀ i : Fin 16, s.regs.get .rbx = BitVec.ofNat 64 i.val →
      (pc,some a) ∈ wordTrace inputBody s → InWordWindow s a) ∧
    (∀ i : Fin 48, s.regs.get .rbx = BitVec.ofNat 64 (16+i.val) →
      (pc,some a) ∈ wordTrace expansionBody s → InWordWindow s a) ∧
    (∀ i : Fin 64, s.regs.get .rbx = BitVec.ofNat 64 i.val →
      (pc,some a) ∈ wordTrace roundBody s → InWordWindow s a) :=
  ⟨fun i hi => safe_words _ _ _ live hi (by decide +kernel) (table_bounds.1 i) _ _,
   fun i hi => safe_words _ _ _ live hi (by decide +kernel) (table_bounds.2.1 i) _ _,
   fun i hi => safe_words _ _ _ live hi (by decide +kernel) (table_bounds.2.2 i) _ _⟩

end Crypto.X86_64
