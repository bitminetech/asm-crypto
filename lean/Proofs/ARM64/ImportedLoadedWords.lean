import Proofs.ARM64.ImportedFetchBinding
import Proofs.ARM64.ImportedHashInitWords

/-!
The imported CodeLoaded predicate binds all 224 words to the recorded 896-byte
image, including both FIPS constant pools. Static instruction fetches agree
with the recorded decoder; loaded_initial_pool and loaded_round_pool bind the
actual memory reads. Full-path fetched execution and equal remain separate.
-/
namespace Crypto.ARM64.Imported

theorem loaded_readWord {prog : Arm64.Program} {m : Arm64.Memory} {off : Nat} {w : BitVec 32}
    (loaded : prog.CodeLoaded m) (word : prog.readWordOff off = some w) :
    m.read32 (prog.base + BitVec.ofNat 64 off) = w := by
  obtain ⟨_, _, hcode⟩ := codeLoaded_iff.mp loaded
  unfold Arm64.Program.readWordOff at word
  split at word
  · contradiction
  split at word
  rotate_left
  · contradiction
  rename_i b0 b1 b2 b3 tl hdrop
  have bound : off + 4 ≤ prog.code.length := by
    have := congrArg List.length hdrop
    simp at this
    omega
  have hb : ∀ k (hk : k < 4),
      m.read8 ((prog.base + BitVec.ofNat 64 off) + BitVec.ofNat 64 k) = prog.code[off + k] := by
    intro k hk
    have address : (prog.base + BitVec.ofNat 64 off) + BitVec.ofNat 64 k =
        prog.base + BitVec.ofNat 64 (off + k) := by rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    exact (hcode _ (by omega)).1
  have hget : ∀ k (hk : k < 4), prog.code[off + k] =
      (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
    intro k hk
    simp only [← hdrop, List.getElem_drop]
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have g0 := hget 0 (by decide)
  have g1 := hget 1 (by decide)
  have g2 := hget 2 (by decide)
  have g3 := hget 3 (by decide)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
  simp only [Arm64.Memory.read32]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0, g0,
    show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1, g1,
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2, g2,
    show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3, g3]
  exact Option.some.inj word

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_word_offsets : ∀ i : Fin 224,
    (program 0#64).readWordOff (4 * i.val) = some imageWords[i.val]! := by
  decide +kernel

theorem loaded_image_word (base : BitVec 64) (m : Arm64.Memory)
    (loaded : (program base).CodeLoaded m) (i : Fin 224) :
    m.read32 (base + BitVec.ofNat 64 (4 * i.val)) = imageWords[i.val]! := by
  apply loaded_readWord loaded
  change (program 0#64).readWordOff (4 * i.val) = _
  exact image_word_offsets i

set_option maxRecDepth 16384 in
theorem image_fetch (base : BitVec 64) (i : Fin 224) :
    (program base).fetch (base + BitVec.ofNat 64 (4 * i.val)) = Arm64.decode imageWords[i.val]! := by
  have ih := i.isLt
  have bound : 4 * i.val < 2 ^ 64 := by omega
  have pbase : (program base).base = base := rfl
  simp only [Arm64.Program.fetch, program_no_hooks, pbase, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    address_delta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have word : (program base).readWordOff (4 * i.val) = some imageWords[i.val]! := image_word_offsets i
  rw [word]
  rfl

theorem image_initial_spec :
    (Vector.ofFn fun i : Fin 8 => imageWords[216 + i.val]!) = SHS.SHA256.H0_256 := by
  decide +kernel

theorem image_round_spec :
    (Vector.ofFn fun i : Fin 64 => imageWords[152 + i.val]!) = SHS.SHA256.K := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem loaded_initial_pool (base : BitVec 64) (s : Arm64.State)
    (loaded : (program base).CodeLoaded s.mem) (pc : s.pc = base + 132#64) :
    wordVector 8 s.mem (s.pc + 732#64) = SHS.SHA256.H0_256 := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn]
  have word := loaded_image_word base s.mem loaded ⟨216 + i, by omega⟩
  have address : s.pc + 732#64 + BitVec.ofNat 64 (4 * i) =
      base + BitVec.ofNat 64 (4 * (216 + i)) := by
    rw [pc]
    simp (config := { decide := true }) [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  rw [← address] at word
  have initial := congrArg (fun H : Vector (BitVec 32) 8 => H[i]) image_initial_spec
  simp only [Vector.getElem_ofFn] at initial
  exact word.trans initial

theorem initialHashMemory_fips (base : BitVec 64) (s : Arm64.State)
    (loaded : (program base).CodeLoaded s.mem) (pc : s.pc = base + 132#64) :
    wordVector 8 (initialHashMemory s) (s.sp + 256#64) = SHS.SHA256.H0_256 :=
  (initialHashMemory_words s).trans (loaded_initial_pool base s loaded pc)

set_option maxRecDepth 16384 in
theorem loaded_round_pool (base : BitVec 64) (m : Arm64.Memory)
    (loaded : (program base).CodeLoaded m) :
    wordVector 64 m (base + 608#64) = SHS.SHA256.K := by
  apply Vector.ext
  intro i hi
  simp only [wordVector, Vector.getElem_ofFn]
  have word := loaded_image_word base m loaded ⟨152 + i, by omega⟩
  have address : base + 608#64 + BitVec.ofNat 64 (4 * i) =
      base + BitVec.ofNat 64 (4 * (152 + i)) := by
    simp (config := { decide := true }) [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  rw [← address] at word
  have constant := congrArg (fun W : Vector (BitVec 32) 64 => W[i]) image_round_spec
  simp only [Vector.getElem_ofFn] at constant
  exact word.trans constant

end Crypto.ARM64.Imported
