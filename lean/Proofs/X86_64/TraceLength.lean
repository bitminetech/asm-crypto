import Proofs.X86_64.Caller

namespace Crypto.X86_64
open X86

private theorem observe_length (code : List Instr) (s : Cpu) :
    (observeCode code s).length = code.length := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [observeCode, List.length_cons, ih]

private theorem frame_length (sp pc : Val) (code : List Instr) :
    (frameEvents sp pc code).length = code.length := by
  induction code generalizing pc with
  | nil => rfl
  | cons i rest ih => simp only [frameEvents,List.length_cons,ih]

private theorem fragment_length (base sp : Val) (off count : Nat)
    (valid : frameFragmentValid off count = true) :
    (frameFragment base sp off count).length = count := by
  unfold frameFragment frameFragmentValid at *
  cases decoded : decodeSeq off count with
  | none => simp [decoded] at valid
  | some code =>
    simp only [decoded, Option.getD_some, frame_length, Bool.and_eq_true,decide_eq_true_eq] at valid ⊢
    exact valid.1.1

private theorem loop_length (loop : WordLoop) (base sp ptr k : Val) (n : Nat) :
    (loop.prefix base sp ptr k n).length = n*(loop.body.length+3) := by
  induction n with
  | zero => simp [WordLoop.prefix]
  | succ n ih =>
    simp only [WordLoop.prefix, WordLoop.iteration, List.length_append, observe_length, ih]
    rw [show (instructions loop.body).length = loop.body.length by simp [instructions]]
    change n*(loop.body.length+3) + (loop.body.length+3) = _
    rw [Nat.succ_mul]

private theorem cycle_length (base sp ptr k : Val) : (cycleEvents base sp ptr k).length = 3975 := by
  unfold cycleEvents blockGuardEvents blockEvents
  simp only [List.length_append, loop_length]
  rw [fragment_length base sp 0x15c 2 (by decide +kernel), fragment_length base sp 0x16b 1 (by decide +kernel),
    fragment_length base sp 0x1c2 9 (by decide +kernel), fragment_length base sp 0x282 8 (by decide +kernel),
    fragment_length base sp 0x2c2 3 (by decide +kernel)]
  rfl

private theorem phase_length (base sp ptr k : Val) (n : Nat) :
    (phaseEvents base sp k n ptr).length = 3975*n+2 := by
  induction n generalizing ptr with
  | zero => exact fragment_length _ _ _ _ (by decide +kernel)
  | succ n ih =>
    simp only [phaseEvents, List.length_append, cycle_length, ih]
    omega

private theorem copy_length (base sp ptr : Val) (n : Nat) :
    (copyPrefixEvents base sp ptr n).length = 6*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copyPrefixEvents, List.length_append, ih]
    rw [show (copyTestEvents base sp).length = 2 from fragment_length _ _ _ _ (by decide +kernel)]
    change 6*n+2+4 = _
    omega

private theorem chosen_length (base sp : Val) (r : Nat) :
    (choosePaddingEvents base sp r).length = 3+optionalMove r := by
  unfold choosePaddingEvents optionalMove
  simp only [List.length_append, fragment_length base sp 0xe8 3 (by decide +kernel)]
  split
  · rfl
  · rw [fragment_length _ _ _ _ (by decide +kernel)]

private theorem iv_length (base sp : Val) (n : Nat) (bound : n ≤ 4) :
    (ivPrefixEvents base sp n).length = 1+2*n := by
  induction n with
  | zero => exact fragment_length _ _ _ _ (by decide +kernel)
  | succ n ih =>
    have h : n < 4 := by omega
    simp only [ivPrefixEvents, dif_pos h, List.length_append, ih (by omega : n ≤ 4)]
    change 1+2*n+2 = 1+2*(n+1)
    omega

private theorem digest_length (base sp dst : Val) (n : Nat) (bound : n ≤ 8) :
    (digestPrefixEvents base sp dst n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : n < 8 := by omega
    have valid : ∀ i : Fin 8, frameFragmentValid (digestPC i.val) 2 = true := by decide +kernel
    rw [digestPrefixEvents, dif_pos h, List.length_append, ih (by omega), digestWordEvents, List.length_append,
      fragment_length _ _ _ _ (valid ⟨n,h⟩)]
    change 3*n+(2+1) = 3*(n+1)
    omega

attribute [local irreducible] blockEvents cycleEvents frameFragment WordLoop.prefix observeCode

theorem callEvents_length (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) :
    (callEvents base s message).length = callSteps message.bytes.size := by
  let sp := frameBase s
  simp only [callEvents, bodyEvents, prepareEvents, prepareTailEvents, tailCopyEvents, copy_length,
    suffixEvents, chosen_length, initialHashEvents, prepareTailEvents, preparedCallEvents, hashPhasesEvents,
    phase_length, phaseTestEvents, digestReturnEvents, digestEvents, List.length_append,
    iv_length _ _ 4 (by decide), digest_length _ _ _ 8 (by decide)]
  rw [fragment_length _ _ 0x25 17 (by decide +kernel),fragment_length _ _ 0xa7 9 (by decide +kernel),
    show (copyTestEvents base sp).length = 2 from fragment_length _ _ _ _ (by decide +kernel),
    fragment_length _ _ 0xf8 4 (by decide +kernel),fragment_length _ _ 0x149 2 (by decide +kernel),
    fragment_length _ _ 0x2d3 2 (by decide +kernel),fragment_length _ _ 0x2de 5 (by decide +kernel),
    fragment_length _ _ 0x307 1 (by decide +kernel)]
  have pro : (entryEvents base (s.regs.get .rsp)).length = 7 := rfl
  have hdr : (headerEvents base sp (s.regs.get .rdi)).length = 4 := rfl
  have epilogue : (returnEvents base sp).length = 9 := rfl
  rw [pro,hdr,epilogue]
  simp only [List.length_cons,List.length_nil]
  unfold callSteps bodySteps Crypto.ARM64.Imported.paddingBlockCount
  omega

end Crypto.X86_64
