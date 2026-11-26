import Proofs.X86_64.WordExecution

namespace Crypto.X86_64
open X86

def ImageLoaded (base : Val) (mem : Mem) : Prop :=
  ∀ i, i < image.size → mem.read (base + BitVec.ofNat 64 i) = image[i]!.toBitVec

def isReturn (i : Instr) : Bool := match i.op with
  | .ret => true
  | _ => false

def stepInside (base : Val) (s : Cpu) : Option Cpu := do
  guard (!s.stopped)
  let i ← fetch base s
  guard (!isReturn i)
  return X86.step i s

/-- Check the first return is executed on precisely the given instruction.
An early return, exhaustion before RET or failed fetch has no result. -/
def returnAt (base : Val) : Nat → Cpu → Option Cpu
  | 0, _ => none
  | n+1, s => do
    guard (!s.stopped)
    let i ← fetch base s
    if isReturn i then
      guard (n = 0)
      return X86.step i s
    returnAt base n (X86.step i s)

/-- Execute a prefix containing no return. -/
def steps (base : Val) : Nat → Cpu → Option Cpu
  | 0, s => some s
  | n + 1, s => (stepInside base s).bind (steps base n)

private theorem code_extent : codeEnd ≤ image.size := by decide +kernel

theorem fetch_at (base : Val) (s : Cpu) (off : Nat) (i : Instr)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + BitVec.ofNat 64 off)
    (h : decodeAt image off = some i) (start : off < codeEnd)
    (stop : off + i.len ≤ codeEnd) : fetch base s = some i := by
  have small : off < 2^64 := Nat.lt_trans start (by decide)
  have bytes : (List.range i.len).all (fun j =>
      s.mem.read (s.rip + BitVec.ofNat 64 j) == image[off + j]!.toBitVec) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    have := List.mem_range.mp hj
    have bound : off + j < image.size := by
      have := code_extent
      omega
    rw [pc, BitVec.add_assoc, ← BitVec.ofNat_add, loaded _ bound]
    simp
  have delta : (s.rip - base).toNat = off := by
    rw [pc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  unfold fetch
  rw [delta]
  simp only [start, stop, h, bytes, guard, if_true, pure, bind, Option.bind]

/-- Both arithmetic fragments are read-only until their final instruction.
The schedule fragment can store its new word there. -/
def WordInst.writes : WordInst → Bool
  | .store .. => true
  | _ => false

def storesLast : WordBlock → Bool
  | [] => true
  | (i, _) :: rest => (rest.isEmpty || !i.writes) && storesLast rest

theorem eval_mem (i : WordInst) (s : DataState) (h : i.writes = false) :
    (i.eval s).mem = s.mem := by
  cases i <;> simp_all [WordInst.writes, WordInst.eval, DataState.put]

theorem fetch_word_block (block : WordBlock) (base : Val) (s : Cpu) (off : Nat)
    (live : s.ms = none) (loaded : ImageLoaded base s.mem)
    (pc : s.rip = base + BitVec.ofNat 64 off) (stores : storesLast block = true)
    (decoded : decodeSeq off block.length = some (instructions block)) :
    steps base block.length s = some (X86.run (instructions block) s) := by
  induction block generalizing s off with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨i, n⟩ := head
    simp only [decodeSeq, List.length_cons] at decoded
    cases hd : decodeAt image off with
    | none => simp [hd] at decoded
    | some ins =>
      by_cases bound : off < codeEnd ∧ off + ins.len ≤ codeEnd
      · cases more : decodeSeq (off + ins.len) tail.length with
        | none => simp [hd, guard, bound, more] at decoded
        | some ops =>
          simp [hd, guard, bound, more, instructions] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          let inst : Instr := ⟨i.op, n⟩
          have fetched := fetch_at base s off inst loaded pc hd bound.1 bound.2
          have regular : isReturn inst = false := by
            cases i <;> first | rfl | rename_i op _ _; cases op <;> rfl
          have one : stepInside base s = some (X86.step inst s) := by
            simp [stepInside, guard, Cpu.stopped, live, fetched, regular]
          simp only [List.length_cons, steps, one, Option.bind_some]
          cases tail with
          | nil => rfl
          | cons next moreTail =>
            have info := word_step i s n live
            have readonly : i.writes = false := by simpa [storesLast] using
                (Bool.and_eq_true_iff.mp stores).1
            apply ih
            · exact info.2.1
            · have mem := congrArg DataState.mem info.1
              rw [eval_mem _ _ readonly] at mem
              simpa only [show (X86.step inst s).mem = s.mem from mem] using loaded
            · exact (info.2.2.trans (by rw [pc, BitVec.ofNat_add, BitVec.add_assoc]))
            · exact (Bool.and_eq_true_iff.mp stores).2
            · exact more
      · simp [hd, guard, bound] at decoded

end Crypto.X86_64
