import EthLib.Cryptography.Hash.Hmac

namespace Crypto.HMACSHA256

open EthLib.Cryptography.Hash

private theorem ipad_lane (i : Fin 8) :
    (0x3636363636363636#64).extractLsb' (8 * i.val) 8 = Hmac.IPAD.toBitVec := by
  have lanes : ∀ j : Fin 8,
      (0x3636363636363636#64).extractLsb' (8 * j.val) 8 = Hmac.IPAD.toBitVec := by
    decide +kernel
  exact lanes i

private theorem opad_lane (i : Fin 8) :
    (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * i.val) 8 = Hmac.OPAD.toBitVec := by
  have lanes : ∀ j : Fin 8,
      (0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * j.val) 8 = Hmac.OPAD.toBitVec := by
    decide +kernel
  exact lanes i

/-- Each little-endian byte written by a 64-bit inner pad XOR. -/
theorem ipad_word (word : BitVec 64) (i : Fin 8) :
    (word ^^^ 0x3636363636363636#64).extractLsb' (8 * i.val) 8 =
      word.extractLsb' (8 * i.val) 8 ^^^ Hmac.IPAD.toBitVec := by
  rw [BitVec.extractLsb'_xor, ipad_lane i]

/-- Each little-endian byte written by a 64-bit outer pad XOR. -/
theorem opad_word (word : BitVec 64) (i : Fin 8) :
    (word ^^^ 0x5c5c5c5c5c5c5c5c#64).extractLsb' (8 * i.val) 8 =
      word.extractLsb' (8 * i.val) 8 ^^^ Hmac.OPAD.toBitVec := by
  rw [BitVec.extractLsb'_xor, opad_lane i]

end Crypto.HMACSHA256
