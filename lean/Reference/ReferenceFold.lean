import Reference.ByteLayout
import Reference.WordModel

namespace Crypto.Reference.WordModel

open EthLib.Cryptography.Hash.Sha256
open Crypto.Reference.ByteLayout (implPaddedBytes paddedBlock)

def blockWords (block : Vector UInt8 64) : Block :=
  Vector.ofFn fun i =>
    (block[4 * i.val]'(by omega)).toBitVec ++
    (block[4 * i.val + 1]'(by omega)).toBitVec ++
    (block[4 * i.val + 2]'(by omega)).toBitVec ++
    (block[4 * i.val + 3]'(by omega)).toBitVec

def paddedSpecBlock (data : ByteArray) (i : Nat) : Block := blockWords (paddedBlock data i)

def paddedSpecFold (data : ByteArray) (count : Nat) : Hash :=
  Fin.foldl count (fun state i => compress state (paddedSpecBlock data i.val)) H0_256

def digestBytes (state : Hash) : Vector (BitVec 8) 32 :=
  Vector.ofFn (fun i => (state[i.val / 4]!).extractLsb' (8 * (3 - i.val % 4)) 8)

private theorem byte_get (bytes : ByteArray) (i : Nat) : bytes.get! i = bytes[i]! := by
  rcases bytes with ⟨a⟩
  by_cases h : i < a.size
  · rw [ByteArray.get!, getElem!_pos a i h, getElem!_pos _ i h]
    rfl
  · rw [ByteArray.get!, getElem!_neg a i h, getElem!_neg _ i h]

private theorem fourBytes (a b c d : UInt8) :
    a.toBitVec ++ b.toBitVec ++ c.toBitVec ++ d.toBitVec =
      BitVec.ofNat 32 a.toNat <<< 24 ||| BitVec.ofNat 32 b.toNat <<< 16 |||
      BitVec.ofNat 32 c.toNat <<< 8 ||| BitVec.ofNat 32 d.toNat := by
  have widen (x : UInt8) : BitVec.ofNat 32 x.toNat = x.toBitVec.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.toNat_toBitVec]
  simp only [widen]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  interval_cases i <;> simp (config := { decide := true })

attribute [local irreducible] pad Spec.padded Spec.inputWord Spec.digest

theorem block_agrees (data : ByteArray) (i : Nat) (bound : data.size < 2^61) :
    paddedSpecBlock data i = Spec.inputWords (Spec.padded data) (64 * i) := by
  apply Vector.ext
  intro j hj
  simp only [paddedSpecBlock, blockWords, paddedBlock, Vector.getElem_ofFn,
    implPaddedBytes, Spec.inputWords, Spec.inputWord, pad_eq_spec data bound,
    byte_get, Nat.mul_comm i 64, Nat.add_assoc]
  apply fourBytes

theorem fold_agrees (data : ByteArray) (bound : data.size < 2^61) (n : Nat) :
    toState (paddedSpecFold data n) = Spec.blocks (Spec.padded data) Spec.initial n := by
  induction n with
  | zero => simp only [paddedSpecFold, Fin.foldl_zero, Spec.blocks, H0_256, toState_words]
  | succ n ih =>
    have next : paddedSpecFold data (n+1) = compress (paddedSpecFold data n) (paddedSpecBlock data n) := by
      unfold paddedSpecFold
      rw [Fin.foldl_succ_last]
      rfl
    rw [next, compress, toState_words, block_agrees data n bound, ih, Spec.blocks]

private theorem digest_size (s : Hash) : ((Spec.digest (toState s)).data.map UInt8.toBitVec).size = 32 := by
  simp only [Spec.digest, Array.size_map, Array.size_ofFn]

private theorem digest_agrees (s : Hash) :
    (Spec.digest (toState s)).data.map UInt8.toBitVec = (digestBytes s).toArray := by
  apply Array.ext
  · rw [digest_size, Vector.size_toArray]
  · intro i hi _
    have bound : i < 32 := digest_size s ▸ hi
    rw [show ((Spec.digest (toState s)).data.map UInt8.toBitVec)[i]'hi =
      (UInt8.ofNat ((s[i / 4]'(by omega)).toNat / 2 ^ (24 - 8 * (i % 4)) % 256)).toBitVec by
        simp only [Spec.digest, Array.getElem_map, Array.getElem_ofFn, words_toState]]
    simp only [Vector.getElem_toArray, digestBytes, Vector.getElem_ofFn]
    apply BitVec.eq_of_toNat_eq
    rw [UInt8.toNat_toBitVec, BitVec.extractLsb'_toNat, getElem!_pos s (i / 4) (by omega)]
    change (s[i / 4]'(by omega)).toNat / 2 ^ (24 - 8 * (i % 4)) % 256 % 256 = _
    rw [Nat.mod_mod, show 24 - 8 * (i % 4) = 8 * (3 - i % 4) by omega, Nat.shiftRight_eq_div_pow]

theorem reference_digest_bytes (data : ByteArray) (bound : data.size < 2 ^ 61) :
    (hash32 data).map UInt8.toBitVec = digestBytes (paddedSpecFold data ((implPaddedBytes data).size / 64)) := by
  have eth := congrArg ByteArray.data (hash32_eq_spec data bound)
  change (hash32 data).toArray = (Spec.hash data).data at eth
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_map, eth, ← digest_agrees, fold_agrees data bound, implPaddedBytes,
    pad_eq_spec data bound, Spec.hash]

end Crypto.Reference.WordModel
