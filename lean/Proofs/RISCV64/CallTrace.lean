import Proofs.RISCV64.CallCode
import Proofs.RISCV64.TraceRelation

namespace Crypto.RISCV64

def entryPublicRegs : List Reg := [1, 2, 10, 11]
private def tailRegs : List Reg := [1, 2, 6, 7, 11, 12, 13, 28, 29, 30]
private def paddingRegs : List Reg := [1, 2, 6, 11, 12, 13, 16, 29]
private def blockRegs : List Reg := [1, 2, 10, 11, 12, 13, 14, 16]
private def indexedRegs : List Reg := 15 :: blockRegs
private def digestRegs : List Reg := [1, 2, 11]

private theorem repeat_public (loop : Nat → List Instruction) (cycle : List Instruction)
    (nil : loop 0 = []) (step : ∀ n, loop (n+1) = loop n ++ cycle) (regs : List Reg)
    (one : PublicFragment cycle regs regs) (n : Nat) : PublicFragment (loop n) regs regs := by
  induction n with
  | zero => rw [nil]; intro s t agree; exact ⟨rfl, agree⟩
  | succ n ih => rw [step]; exact ih.append one

private theorem tail_public (n : Nat) : PublicFragment (tailCode n) tailRegs tailRegs := by
  have prefixProof := repeat_public tailPrefix tailCycle rfl (fun _ => rfl) tailRegs
    (checked_public_fragment _ _ _ (by decide)) n
  exact prefixProof.append (checked_public_fragment (tailCode 0) _ _ (by decide))

private theorem marker_public (n : Nat) : PublicFragment (markerCode n) tailRegs paddingRegs := by
  by_cases small : n < 56
  · simpa only [markerCode, if_pos small, if_pos (show 0 < 56 by decide)] using
      checked_public_fragment (markerCode 0) tailRegs paddingRegs (by decide)
  · simpa only [markerCode, if_neg small, if_neg (show ¬56 < 56 by decide)] using
      checked_public_fragment (markerCode 56) tailRegs paddingRegs (by decide)

private theorem load_public (n : Nat) : PublicFragment (loadCode n) indexedRegs indexedRegs :=
  repeat_public loadCode loadCycle rfl (fun _ => rfl) indexedRegs
    (checked_public_fragment _ _ _ (by decide)) n

private theorem expansion_public (n : Nat) : PublicFragment (expansionCode n) indexedRegs indexedRegs :=
  repeat_public expansionCode expansionCycle rfl (fun _ => rfl) indexedRegs
    (checked_public_fragment _ _ _ (by decide)) n

private theorem rounds_public (n : Nat) : PublicFragment (roundCode n) indexedRegs indexedRegs :=
  repeat_public roundCode roundCycle rfl (fun _ => rfl) indexedRegs
    (checked_public_fragment _ _ _ (by decide)) n

attribute [local irreducible] loadCode expansionCode roundCode

private theorem block_public : PublicFragment blockCode blockRegs blockRegs := by
  simp only [blockCode, List.append_assoc]
  have start := checked_public_fragment [blockGuard, startWords] blockRegs indexedRegs (by decide)
  have hash := checked_public_fragment loadHashBody indexedRegs indexedRegs (by decide)
  have feed := checked_public_fragment feedForward indexedRegs indexedRegs (by decide)
  have advance := checked_public_fragment advanceBlock indexedRegs blockRegs (by decide)
  exact start.append ((load_public 16).append ((expansion_public 48).append
    (hash.append ((rounds_public 64).append (feed.append advance)))))

private theorem block_loop_public (n : Nat) : PublicFragment (blockLoop n) blockRegs blockRegs :=
  repeat_public blockLoop blockCode rfl (fun _ => rfl) blockRegs block_public n

private def preparationCode : List Instruction := saveFrame ++ headerBody ++ zeroPadding ++ lengthBody

private def afterLengthCode (size : Nat) : List Instruction := tailCode (size % 64) ++
  markerCode (size % 64) ++ lengthSuffix ++ initialHashCode ++ blockLoop (size / 64) ++
  [blockGuard] ++ [phaseGuard] ++ paddingPhase ++
  blockLoop (if size % 64 < 56 then 1 else 2) ++ [blockGuard] ++ [phaseGuard] ++ digestCode ++ returnCode

private theorem after_length_public (size : Nat) : PublicFragment (afterLengthCode size) tailRegs [] := by
  simp only [afterLengthCode, List.append_assoc]
  have suffix := checked_public_fragment lengthSuffix paddingRegs paddingRegs (by decide)
  have iv := checked_public_fragment initialHashCode paddingRegs blockRegs (by decide)
  have guard := checked_public_fragment [blockGuard] blockRegs blockRegs (by decide)
  have phase := checked_public_fragment [phaseGuard] blockRegs blockRegs (by decide)
  have pad := checked_public_fragment paddingPhase blockRegs blockRegs (by decide)
  have emit := checked_public_fragment digestCode blockRegs digestRegs (by decide +kernel)
  have ret := checked_public_fragment returnCode digestRegs [] (by decide)
  have padding := (block_loop_public (if size % 64 < 56 then 1 else 2)).append
    (guard.append (phase.append (emit.append ret)))
  exact (tail_public _).append ((marker_public _).append (suffix.append (iv.append
    ((block_loop_public _).append (guard.append (phase.append (pad.append padding)))))))

theorem ImageExecution.result {base : Addr} {s out : CPU} {code : List Instruction}
    (path : ImageExecution base s code out) : out = run code s := by
  induction path with
  | nil => rfl
  | cons _ _ _ ih => exact ih

private theorem preparation_result (base : Addr) (s : CPU) (data : ByteArray)
    (entry : CallEntry base s data) : InputPrepared base s data (run preparationCode s) := by
  obtain ⟨frame, header, clear, prepared, a, b, c, d, args⟩ := input_prepared base s data entry
  simpa only [d.result, c.result, b.result, a.result,
    preparationCode, run, List.foldl_append] using args

private theorem preparation_public {base : Addr} {s t : CPU} {a b : ByteArray}
    (entry : PublicAgreement (publicRegs entryPublicRegs) s t)
    (sameSize : a.size = b.size) (samePayload : inputPayload s = inputPayload t)
    {p q : CPU} (left : InputPrepared base s a p) (right : InputPrepared base t b q) :
    PublicAgreement (publicRegs tailRegs) p q := by
  refine ⟨left.pc.trans right.pc.symm, ?_⟩
  intro r known
  simp only [publicRegs, tailRegs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq <;> subst r
  · rw [reg_zero, reg_zero]
  · exact left.ret.trans ((entry.reg 1 (by decide)).trans right.ret.symm)
  · exact left.sp.trans ((congrArg (· - 480) (entry.reg 2 (by decide))).trans right.sp.symm)
  · exact left.count.trans (by rw [sameSize, right.count])
  · exact left.rem.trans (by rw [sameSize, right.rem])
  · exact left.output.trans ((entry.reg 11 (by decide)).trans right.output.symm)
  · exact left.source.trans (samePayload.trans right.source.symm)
  · exact left.blocks.trans (by rw [sameSize, right.blocks])
  · rw [left.tail, right.tail]
    simp only [inputTail, samePayload, sameSize]
  · rw [left.pad, right.pad]
    simp only [entryStack, entry.reg 2 (by decide)]
  · exact left.cursor.trans right.cursor.symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- With the same public length, addresses, and return target, the complete
decoded call has the same instruction-fetch, read, and write addresses. -/
theorem call_public_execution (base : Addr) (s t : CPU) (a b : ByteArray)
    (left : CallEntry base s a) (right : CallEntry base t b)
    (entry : PublicAgreement (publicRegs entryPublicRegs) s t)
    (sameSize : a.size = b.size) (samePayload : inputPayload s = inputPayload t) :
    accessTrace (callCode a.size) s = accessTrace (callCode b.size) t ∧
      (run (callCode a.size) s).pc = (run (callCode b.size) t).pc := by
  have split (size : Nat) : callCode size = preparationCode ++ afterLengthCode size := by
    simp only [callCode, callBeforeReturn, preparationCode, afterLengthCode, List.append_assoc]
  have front := checked_public_fragment preparationCode entryPublicRegs [] (by decide +kernel) entry
  have agree := preparation_public entry sameSize samePayload
    (preparation_result base s a left) (preparation_result base t b right)
  have back := after_length_public a.size agree
  refine ⟨?_, ?_⟩
  · simp only [split, accessTrace_append, ← sameSize, front.1, back.1]
  · simpa only [split, run_append, ← sameSize] using back.2.pc

theorem call_public_accesses (base : Addr) (s t : CPU) (a b : ByteArray)
    (left : CallEntry base s a) (right : CallEntry base t b)
    (entry : PublicAgreement (publicRegs entryPublicRegs) s t)
    (sameSize : a.size = b.size) (samePayload : inputPayload s = inputPayload t) :
    accessTrace (callCode a.size) s = accessTrace (callCode b.size) t :=
  (call_public_execution base s t a b left right entry sameSize samePayload).1

end Crypto.RISCV64
