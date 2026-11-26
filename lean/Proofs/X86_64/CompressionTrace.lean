import Proofs.X86_64.WordTrace
import Proofs.X86_64.TracePaths
import Proofs.X86_64.Counter

namespace Crypto.X86_64
open X86

inductive WordLoop
  | input
  | expansion
  | round
  deriving DecidableEq

def WordLoop.body : WordLoop → WordBlock
  | .input => inputBody
  | .expansion => expansionBody
  | .round => roundBody

def WordLoop.start : WordLoop → Nat
  | .input => 0x16d
  | .expansion => 0x17f
  | .round => 0x204

def WordLoop.latch : WordLoop → Nat
  | .input => 0x176
  | .expansion => 0x1b9
  | .round => 0x279

def WordLoop.displacement : WordLoop → Val
  | .input => -18
  | .expansion => -67
  | .round => -126

def WordLoop.limit : WordLoop → Val
  | .input => 16
  | _ => 64

def WordLoop.initialIndex : WordLoop → Nat
  | .expansion => 16
  | _ => 0

private theorem body_decoded (loop : WordLoop) :
    decodeSeq loop.start loop.body.length = some (instructions loop.body) := by
  cases loop <;> decide +kernel

private theorem body_linear (loop : WordLoop) :
    (instructions loop.body).dropLast.all linear = true := by
  cases loop <;> decide +kernel

private theorem latch_decoded (loop : WordLoop) :
    decodeSeq loop.latch 3 = some (countCode loop.limit loop.displacement) := by
  cases loop <;> decide +kernel

private theorem latch_linear (loop : WordLoop) :
    (countCode loop.limit loop.displacement).dropLast.all linear = true := by
  cases loop <;> decide +kernel

def WordLoop.withInputs (loop : WordLoop) (base sp ptr k : Val) (index : Nat) : Cpu :=
  {rip := base + BitVec.ofNat 64 loop.start,
   regs := ((Regs.set {} .rsp sp).set .rbp ptr |>.set .rdi k).set .rbx (BitVec.ofNat 64 index)}

private def combineWordEvents (block : WordBlock) (seen : List (Val × Option WordAccess)) :
    List Event := List.zipWith (fun i (pc, access) =>
      (pc, i, access.toList.map (fun a => ⟨a.write,a.address,4⟩))) (instructions block) seen

theorem word_events (block : WordBlock) (s : Cpu) :
    observeCode (instructions block) s = combineWordEvents block (wordTrace block s) := by
  have operand (i : WordInst) (len : Nat) (st : Cpu) :
      (dataAccesses ⟨i.op,len⟩ st).getD [] =
        (i.access (project st)).toList.map (fun a => ⟨a.write,a.address,4⟩) := by
    cases i
    all_goals try cases ‹WordOp›
    all_goals simp [dataAccesses, WordInst.op, WordOp.opcode, operandAccess, WordInst.access,
      Indexed.ea, Indexed.addr, Ea.addr, Ea.offset, Scale.toVal, project, Size.bytes]
  induction block generalizing s with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨i,n⟩ := i
    show (s.rip,⟨i.op,n⟩,(dataAccesses ⟨i.op,n⟩ s).getD []) ::
        observeCode (instructions rest) (X86.step ⟨i.op,n⟩ s) =
      (s.rip,⟨i.op,n⟩,(i.access (project s)).toList.map (fun a => ⟨a.write,a.address,4⟩)) ::
        combineWordEvents rest (wordTrace rest (X86.step ⟨i.op,n⟩ s))
    rw [operand, ih]

theorem word_event_access (block : WordBlock) (s : Cpu) (event : Event)
    (present : event ∈ observeCode (instructions block) s)
    (access : Crypto.ARM64.Imported.DataAccess) (observed : access ∈ event.2.2) :
    ∃ word, (event.1,some word) ∈ wordTrace block s ∧ access = ⟨word.write,word.address,4⟩ := by
  rw [word_events] at present
  induction block generalizing s with
  | nil => simp [combineWordEvents,instructions] at present
  | cons h rest ih =>
    obtain ⟨i,len⟩ := h
    change event ∈ (s.rip,⟨i.op,len⟩,(i.access (project s)).toList.map
      (fun a => ⟨a.write,a.address,4⟩)) :: combineWordEvents rest (wordTrace rest (X86.step ⟨i.op,len⟩ s)) at present
    rcases List.mem_cons.mp present with rfl | later
    · cases datum : i.access (project s) with
      | none => simp [datum] at observed
      | some word =>
        refine ⟨word, ?_, ?_⟩
        · simp [wordTrace,datum]
        · simpa [datum] using observed
    · obtain ⟨word, occurs, value⟩ := ih _ later
      exact ⟨word,List.mem_cons_of_mem _ occurs,value⟩

def latchEvents (pc : Val) (limit disp : Val) : List Event :=
  [(pc,incIndex,[]),(pc+3,cmpLimit limit,[]),(pc+7,branchBelow disp,[])]

private theorem latch_events (s : Cpu) (limit disp : Val) (live : s.ms = none) :
    observeCode (countCode limit disp) s = latchEvents s.rip limit disp := by
  have one : (X86.step incIndex s).ms = none := by rw [inc_step _ live]; exact live
  have first : (X86.step incIndex s).rip = s.rip+3 := by rw [inc_step _ live]
  have second : (X86.step (cmpLimit limit) (X86.step incIndex s)).rip = s.rip+7 := by
    rw [index_cmp_step _ _ one]
    change (X86.step incIndex s).rip + 4 = _
    rw [first, BitVec.add_assoc]
    rfl
  simp only [countCode,observeCode,latchEvents,first,second]
  rfl

def WordLoop.iteration (loop : WordLoop) (base sp ptr k : Val) (index : Nat) : List Event :=
  observeCode (instructions loop.body) (loop.withInputs base sp ptr k index) ++
    latchEvents (base+BitVec.ofNat 64 loop.latch) loop.limit loop.displacement

def WordLoop.prefix (loop : WordLoop) (base sp ptr k : Val) : Nat → List Event
  | 0 => []
  | n+1 => loop.prefix base sp ptr k n ++ loop.iteration base sp ptr k (loop.initialIndex+n)

attribute [local irreducible] X86.step decodeSeq observeCode

/-- The body and its latch have exactly this trace for any values of the
working registers, input words, flags, memory and undefined-bit oracle. -/
theorem WordLoop.observed_iteration (loop : WordLoop) {base : Val} {s mid out : Cpu} {idx : Nat}
    (live : s.ms = none) (bodyLive : mid.ms = none)
    (pc : s.rip = base+BitVec.ofNat 64 loop.start) (midPc : mid.rip = base+BitVec.ofNat 64 loop.latch)
    (index : s.regs.get .rbx = BitVec.ofNat 64 idx)
    (body : steps base loop.body.length s = some mid) (tail : steps base 3 mid = some out) :
    ObservedExecution base s (loop.iteration base (s.regs.get .rsp) (s.regs.get .rbp) (s.regs.get .rdi) idx) out := by
  let publicCpu := loop.withInputs base (s.regs.get .rsp) (s.regs.get .rbp) (s.regs.get .rdi) idx
  have publicPc : s.rip = publicCpu.rip := pc
  have bases : wordBases (project s) = wordBases (project publicCpu) := by
    simp (config := {decide := true}) [publicCpu, WordLoop.withInputs, project, wordBases, Regs.get_set_ne, index]
  have sameWords := compression_word_traces s publicCpu live rfl publicPc bases
  have words : wordTrace loop.body s = wordTrace loop.body publicCpu := by
    cases loop
    · exact sameWords.1
    · exact sameWords.2.1
    · exact sameWords.2.2
  have first : ObservedExecution base s (observeCode (instructions loop.body) s) mid := by
    apply steps_observe_linear _ pc (by simpa [instructions] using body_decoded loop) (body_linear loop)
    simpa [instructions] using body
  have last : ObservedExecution base mid (observeCode (countCode loop.limit loop.displacement) mid) out :=
    steps_observe_linear tail midPc (latch_decoded loop) (latch_linear loop)
  rw [latch_events _ _ _ bodyLive, midPc] at last
  have sameEvents : observeCode (instructions loop.body) s = observeCode (instructions loop.body) publicCpu := by
    rw [word_events, word_events, words]
  exact (sameEvents ▸ first).append last

end Crypto.X86_64
