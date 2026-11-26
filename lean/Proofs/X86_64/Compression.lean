import Proofs.X86_64.WordExecution
import equiv.SHA256.Foldl.Sequential
import Mathlib.Tactic.IntervalCases

namespace Crypto.X86_64
open X86

def inputBody : WordBlock := [(.rm .mov .rcx ⟨.rbp,0⟩, 4), (.bswap .rcx, 2),
  (.store ⟨.rsp,0⟩ .rcx, 3)]

/-- Each pair records an operation and its encoded length. The decoding
identities below are checked against the bytes in the archive image. -/
def expansionBody : List (WordInst × Nat) := [
  (.rm .mov .rcx ({ base := .rsp, disp := -0x3c }), 4),
  (.rr .mov .rax .rcx, 2),
  (.ror .rax 7, 3),
  (.rr .mov .rdx .rcx, 2),
  (.ror .rdx 18, 3),
  (.rr .xor .rax .rdx, 2),
  (.shr .rcx 3, 3),
  (.rr .xor .rax .rcx, 2),
  (.rm .mov .rcx ({ base := .rsp, disp := -0x8 }), 4),
  (.rr .mov .rdx .rcx, 2),
  (.ror .rdx 17, 3),
  (.rr .mov .r8 .rcx, 3),
  (.ror .r8 19, 4),
  (.rr .xor .rdx .r8, 3),
  (.shr .rcx 10, 3),
  (.rr .xor .rdx .rcx, 2),
  (.rm .add .rax ({ base := .rsp, disp := -0x40 }), 4),
  (.rm .add .rax ({ base := .rsp, disp := -0x1c }), 4),
  (.rr .add .rax .rdx, 2),
  (.store ({ base := .rsp }) .rax, 3)
]

def roundBody : List (WordInst × Nat) := [
  (.rr .mov .rcx .r12, 3),
  (.ror .rcx 6, 3),
  (.rr .mov .rdx .r12, 3),
  (.ror .rdx 11, 3),
  (.rr .xor .rcx .rdx, 2),
  (.ror .rdx 14, 3),
  (.rr .xor .rcx .rdx, 2),
  (.rr .add .r15 .rcx, 3),
  (.rr .mov .rcx .r13, 3),
  (.rr .xor .rcx .r14, 3),
  (.rr .and .rcx .r12, 3),
  (.rr .xor .rcx .r14, 3),
  (.rr .add .r15 .rcx, 3),
  (.rm .add .r15 ({ base := .rdi }), 4),
  (.rm .add .r15 ({ base := .rsp }), 4),
  (.rr .add .r11 .r15, 3),
  (.rr .mov .rcx .r8, 3),
  (.ror .rcx 2, 3),
  (.rr .mov .rdx .r8, 3),
  (.ror .rdx 13, 3),
  (.rr .xor .rcx .rdx, 2),
  (.ror .rdx 9, 3),
  (.rr .xor .rcx .rdx, 2),
  (.rr .add .r15 .rcx, 3),
  (.rr .mov .rcx .r8, 3),
  (.rr .or .rcx .r9, 3),
  (.rr .and .rcx .r10, 3),
  (.rr .mov .rdx .r8, 3),
  (.rr .and .rdx .r9, 3),
  (.rr .or .rcx .rdx, 2),
  (.rr .add .r15 .rcx, 3),
  (.rr .mov .rcx .r15, 3),
  (.rr .mov .r15 .r14, 3),
  (.rr .mov .r14 .r13, 3),
  (.rr .mov .r13 .r12, 3),
  (.rr .mov .r12 .r11, 3),
  (.rr .mov .r11 .r10, 3),
  (.rr .mov .r10 .r9, 3),
  (.rr .mov .r9 .r8, 3),
  (.rr .mov .r8 .rcx, 3)
]

def working (s : DataState) : Vector Word 8 :=
  #v[s.word .r8, s.word .r9, s.word .r10, s.word .r11,
     s.word .r12, s.word .r13, s.word .r14, s.word .r15]

def tableWord (s : DataState) (base : GPR) (disp : Val := 0) : Word :=
  Indexed.read ⟨base, disp⟩ s

set_option maxRecDepth 8000 in
theorem round_decoded :
    decodeSeq 0x204 roundBody.length = some (instructions roundBody) := by decide +kernel

set_option maxRecDepth 8000 in
theorem expansion_decoded :
    decodeSeq 0x17f expansionBody.length = some (instructions expansionBody) := by decide +kernel

private theorem choose (x y z : Word) :
    ((y ^^^ z) &&& x) ^^^ z = SHS.SHA256.Ch x y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [SHS.SHA256.Ch, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

private theorem rotate_e (x : Word) : (x.rotateRight 11).rotateRight 14 = x.rotateRight 25 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_rotateRight] <;> rfl

private theorem rotate_a (x : Word) : (x.rotateRight 13).rotateRight 9 = x.rotateRight 22 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_rotateRight] <;> rfl

private theorem read_put (s : DataState) (d r : GPR) (v : Word) :
    (s.put d v).word r = if d = r then v else s.word r := by
  by_cases h : d = r <;> simp [DataState.put, DataState.word, Regs.get_set_ne, h]

private theorem addr_put (a : Indexed) (s : DataState) (dst : GPR) (v : Word)
    (base : dst ≠ a.base) (index : dst ≠ .rbx) :
    a.addr (s.put dst v) = a.addr s := by
  simp [Indexed.addr, DataState.put, Regs.get_set_ne, base, index]

private theorem load_put (a : Indexed) (s : DataState) (dst : GPR) (v : Word)
    (base : dst ≠ a.base) (index : dst ≠ .rbx) :
    a.read (s.put dst v) = a.read s := by
  unfold Indexed.read
  rw [addr_put _ _ _ _ base index]
  rfl

private theorem put_mem (s : DataState) (d : GPR) (v : Word) : (s.put d v).mem = s.mem := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem round_value (s : DataState) :
    working (evalBlock roundBody s) =
      Crypto.ARM64.Round.fipsRound (working s) (tableWord s .rdi) (tableWord s .rsp) := by
  simp (config := { decide := true }) [evalBlock, roundBody, working, WordInst.eval,
    WordOp.apply, read_put, tableWord, load_put, Crypto.ARM64.Round.fipsRound,
    choose, Crypto.ARM64.Round.maj_factored, rotate_e, rotate_a]
  simp [SHS.SHA256.bigSigma0, SHS.SHA256.bigSigma1, SHS.SHA256.Maj, SHS.ROTR,
    BitVec.rotateRight_def, BitVec.add_assoc, BitVec.xor_assoc]

/-- W[t] in terms of the four earlier words in the x86 stack workspace. -/
def expandedWord (s : DataState) : Word :=
  SHS.SHA256.smallSigma1 (tableWord s .rsp (-8)) + tableWord s .rsp (-28) +
  SHS.SHA256.smallSigma0 (tableWord s .rsp (-60)) + tableWord s .rsp (-64)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem expansion_memory (s : DataState) :
    (evalBlock expansionBody s).mem =
      s.mem.writeSize .d (Indexed.addr ⟨.rsp, 0⟩ s) ((expandedWord s).setWidth 64) := by
  simp (config := { decide := true }) [evalBlock, expansionBody, WordInst.eval,
    WordOp.apply, read_put, tableWord, load_put, addr_put, put_mem, expandedWord,
    SHS.SHA256.smallSigma0, SHS.SHA256.smallSigma1, SHS.ROTR, SHS.SHR,
    BitVec.rotateRight_def, BitVec.add_assoc, BitVec.add_comm, BitVec.xor_assoc]

end Crypto.X86_64
