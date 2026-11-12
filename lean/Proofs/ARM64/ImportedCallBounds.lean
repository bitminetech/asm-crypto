import Proofs.ARM64.ImportedHeader
import Proofs.ARM64.ImportedHashInit
import Proofs.ARM64.ImportedPreparePadding
import Proofs.ARM64.ImportedHashBody

/-!
The complete proposed recorded-word path has the stated exact length and
fits the architecture instruction budget for every count. This counts the
word-list path; whole-call existence and memory-fetched execution must be
connected before claiming a bound on the callable implementation.
-/
namespace Crypto.ARM64.Imported

theorem tail_copy_code_length (rem : Nat) : (tailCopyCode rem).length = 6 * rem + 2 := by
  have cycle : tailCopyCycleCode.length = 6 := by decide +kernel
  have ending : tailCopyEndCode.length = 2 := by decide +kernel
  simp only [tailCopyCode, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate_nat, cycle, ending, Nat.mul_comm]

theorem prepare_tail_code_length (rem : Nat) : (prepareTailCode rem).length = 6 * rem + 15 := by
  have zero : zeroPadCode.length = 9 := by decide +kernel
  have setup : paddingSetupCode.length = 4 := by decide +kernel
  simp only [prepareTailCode, List.length_append, zero, setup, tail_copy_code_length]
  omega

theorem padding_count_code_length (small : Bool) :
    (paddingCountCode small).length = 3 + if small then 0 else 1 := by
  cases small <;> decide +kernel

theorem padding_suffix_code_length (rem : Nat) :
    (paddingSuffixCode rem).length = 9 + if rem < 56 then 0 else 1 := by
  have marker : markerCode.length = 2 := by decide +kernel
  have length : lengthCode.length = 4 := by decide +kernel
  simp only [paddingSuffixCode, List.length_append, marker, length, padding_count_code_length]
  by_cases h : rem < 56 <;> simp [h]

theorem prepare_padding_code_length (count : BitVec 64) :
    (preparePaddingCode count).length =
      6 * (count.toNat % 64) + 24 + if count.toNat % 64 < 56 then 0 else 1 := by
  simp only [preparePaddingCode, List.length_append, prepare_tail_code_length, padding_suffix_code_length]
  omega

theorem hash_phases_code_length (full padding : Nat) :
    (hashPhasesCode full padding).length = 3100 * (full + padding) + 8 := by
  have phase : paddingPhaseCode.length = 5 := by decide +kernel
  have gate : digestGateCode.length = 1 := by decide +kernel
  simp only [hashPhasesCode, List.length_append, outer_loop_code_length, phase, gate]
  omega

theorem hash_body_code_length (full padding : Nat) :
    (hashBodyCode full padding).length = 3100 * (full + padding) + 28 := by
  have exit : exitCode.length = 20 := by decide +kernel
  simp only [hashBodyCode, List.length_append, hash_phases_code_length, exit]

def wholeCallCode (count : BitVec 64) :=
  headerCode ++ (preparePaddingCode count ++ (hashInitCode ++
    hashBodyCode (count.toNat / 64) (if count.toNat % 64 < 56 then 1 else 2)))

theorem whole_call_code_length (count : BitVec 64) :
    (wholeCallCode count).length = 64 + 6 * (count.toNat % 64) +
      3100 * (count.toNat / 64 + if count.toNat % 64 < 56 then 1 else 2) +
      if count.toNat % 64 < 56 then 0 else 1 := by
  have header : headerCode.length = 4 := by decide +kernel
  have initial : hashInitCode.length = 8 := by decide +kernel
  simp only [wholeCallCode, List.length_append, header, initial,
    prepare_padding_code_length, hash_body_code_length]
  omega

theorem instruction_budget (n : Nat) :
    64 + 6 * (n % 64) + 3100 * (n / 64 + if n % 64 < 56 then 1 else 2) +
      (if n % 64 < 56 then 0 else 1) ≤ 512 + 4000 * ((n + 8) / 64 + 1) := by
  by_cases h : n % 64 < 56 <;> simp only [h, if_true, if_false] <;> omega

theorem whole_call_code_bound (count : BitVec 64) :
    (wholeCallCode count).length ≤ 512 + 4000 * ((count.toNat + 8) / 64 + 1) := by
  rw [whole_call_code_length]
  exact instruction_budget count.toNat

end Crypto.ARM64.Imported
