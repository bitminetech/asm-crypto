import Proofs.ARM64.ImportedFetchExecution

/-!
Lift sequential recorded image spans to imported memory-fetched Steps, and
compose their StaticPath certificates. The header span is the first concrete
fragment lifted here. Full-loop/control certificates and equal remain separate.
-/
namespace Crypto.ARM64.Imported

def SequentialWords (words : List (BitVec 32)) : Prop :=
  ∀ word ∈ words, ∀ instruction, Arm64.decode word = some instruction → sequentialInstruction instruction = true

theorem SequentialWords.permitted {words : List (BitVec 32)} (sequential : SequentialWords words) :
    PermittedWords words := by
  intro word member instruction decoded
  exact sequential_permitted instruction (sequential word member instruction decoded)

theorem SequentialWords.tail {word : BitVec 32} {rest : List (BitVec 32)}
    (sequential : SequentialWords (word :: rest)) : SequentialWords rest := by
  intro w member instruction decoded
  exact sequential w (by simp [member]) instruction decoded

theorem runWords_append_split (xs ys : List (BitVec 32)) (s out : Arm64.State)
    (executed : runWords (xs ++ ys) s = some out) :
    ∃ mid, runWords xs s = some mid ∧ runWords ys mid = some out := by
  rw [runWords_append] at executed
  cases hx : runWords xs s with
  | none => simp [hx] at executed
  | some mid =>
    refine ⟨mid, rfl, ?_⟩
    simpa only [hx, Option.bind_some] using executed

theorem StaticPath.append {base : BitVec 64} {xs ys : List (BitVec 32)} {s mid : Arm64.State}
    (executed : runWords xs s = some mid) (left : StaticPath base xs s) (right : StaticPath base ys mid) :
    StaticPath base (xs ++ ys) s := by
  induction xs generalizing s with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst mid
    exact right
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some mid at executed
      have parts : (program base).fetch s.pc = some instruction ∧
          StaticPath base rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) := by
        simpa only [StaticPath, decoded] using left
      simp only [List.cons_append, StaticPath, decoded]
      exact ⟨parts.1, ih executed parts.2⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem sequential_image_path (base : BitVec 64) (words : List (BitVec 32))
    (s out : Arm64.State) (offset : Nat)
    (sequential : SequentialWords words)
    (bound : offset + words.length ≤ 224)
    (identity : ∀ (i : Nat) (hi : i < words.length), words[i] = imageWords[offset + i]!)
    (pc : s.pc = base + BitVec.ofNat 64 (4 * offset))
    (executed : runWords words s = some out) (running : out.status = .Running) :
    StaticPath base words s ∧ out.pc = base + BitVec.ofNat 64 (4 * (offset + words.length)) := by
  induction words generalizing s offset with
  | nil =>
    simp only [runWords, Option.some.injEq] at executed
    subst out
    exact ⟨True.intro, by simpa using pc⟩
  | cons word rest ih =>
    cases decoded : Arm64.decode word with
    | none => simp [runWords, decoded] at executed
    | some instruction =>
      rw [runWords, decoded] at executed
      change runWords rest (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) = some out at executed
      have stepSequential := sequential word (by simp) instruction decoded
      have nextRunning := runWords_running_before rest _ out sequential.tail.permitted executed running
      have nextPC := sequential_pc instruction stepSequential s nextRunning
      have nextAddress : (Arm64.execInstWithSvc Arm64.noSyscalls instruction s).pc =
          base + BitVec.ofNat 64 (4 * (offset + 1)) := by
        rw [nextPC, pc]
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
      have tailIdentity (i : Nat) (hi : i < rest.length) : rest[i] = imageWords[(offset + 1) + i]! := by
        have before := identity (i + 1) (by simp only [List.length_cons]; omega)
        have add : offset + (i + 1) = (offset + 1) + i := by omega
        simpa only [List.getElem_cons_succ, add] using before
      obtain ⟨tailPath, finalPC⟩ := ih (Arm64.execInstWithSvc Arm64.noSyscalls instruction s) (offset + 1)
        sequential.tail (by simp only [List.length_cons] at bound; omega) tailIdentity nextAddress executed
      have headWord : word = imageWords[offset]! := by
        simpa only [List.getElem_cons_zero, Nat.add_zero] using identity 0 (by simp)
      have fetched : (program base).fetch s.pc = some instruction := by
        rw [pc, image_fetch base ⟨offset, by simp only [List.length_cons] at bound; omega⟩, ← headWord, decoded]
      refine ⟨?_, ?_⟩
      · simp only [StaticPath, decoded]
        exact ⟨fetched, tailPath⟩
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC

theorem image_word_count : imageWords.size = 224 := by decide +kernel

def imageSlice (offset count : Nat) : List (BitVec 32) := (imageWords.toList.drop offset).take count

theorem image_slice_length (offset count : Nat) (bound : offset + count ≤ 224) :
    (imageSlice offset count).length = count := by
  simp only [imageSlice, List.length_take, List.length_drop, Array.length_toList, image_word_count]
  omega

theorem image_slice_word (offset count : Nat) (bound : offset + count ≤ 224)
    (i : Nat) (hi : i < (imageSlice offset count).length) :
    (imageSlice offset count)[i] = imageWords[offset + i]! := by
  have small : offset + i < imageWords.size := by
    rw [image_word_count]
    rw [image_slice_length offset count bound] at hi
    omega
  simp only [imageSlice, List.getElem_take, List.getElem_drop, Array.getElem_toList]
  exact (getElem!_pos imageWords (offset + i) small).symm

theorem sequentialWords_of_all (words : List (BitVec 32))
    (all : (words.all fun word => ((Arm64.decode word).map sequentialInstruction).getD false) = true) :
    SequentialWords words := by
  intro word member instruction decoded
  have good := List.all_eq_true.mp all word member
  simpa only [decoded, Option.map_some, Option.getD_some] using good

theorem sequential_slice_path (base : BitVec 64) (offset count : Nat) (s out : Arm64.State)
    (bound : offset + count ≤ 224)
    (sequential : SequentialWords (imageSlice offset count))
    (pc : s.pc = base + BitVec.ofNat 64 (4 * offset))
    (executed : runWords (imageSlice offset count) s = some out) (running : out.status = .Running) :
    StaticPath base (imageSlice offset count) s ∧ out.pc = base + BitVec.ofNat 64 (4 * (offset + count)) := by
  have result := sequential_image_path base (imageSlice offset count) s out offset sequential
    (by rw [image_slice_length offset count bound]; exact bound)
    (image_slice_word offset count bound) pc executed running
  simpa only [image_slice_length offset count bound] using result

set_option maxRecDepth 16384 in
theorem header_fetched_steps (base : BitVec 64) (s out : Arm64.State)
    (loaded : (program base).CodeLoaded s.mem) (pc : s.pc = base)
    (executed : runWords headerCode s = some out) (running : out.status = .Running) :
    Arm64.Steps (program base) s out := by
  have sequential : SequentialWords (imageSlice 0 4) := sequentialWords_of_all _ (by decide +kernel)
  have path := (sequential_slice_path base 0 4 s out (by decide) sequential
    (by simpa using pc) executed running).1
  exact staticPath_steps base headerCode s out sequential.permitted loaded executed path running

end Crypto.ARM64.Imported
