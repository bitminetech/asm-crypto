import Proofs.HMACSHA256.RISCV64Ranges
import Proofs.HMACSHA256.RISCV64OuterSetup

namespace Crypto.HMACSHA256.RISCV64

open Crypto.RISCV64

set_option maxRecDepth 8192
set_option maxHeartbeats 4500000
set_option linter.unusedSimpArgs false

theorem finish_inner_call_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0x1c#64)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true) :
    RangeAllowed finish base 0x1c 4 s := by
  refine ⟨_, finish_first_decoded, ?_⟩
  hmac_range_permissions pc codeAligned exec pc pc pc pc

theorem finish_header_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0x26#64)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true)
    (writeAligned : (s.reg 2#5).toNat % 8 = 0)
    (writable : s.mem.canWrite (s.reg 2#5) 24 = true) :
    RangeAllowed finish base 0x26 6 s := by
  refine ⟨_, finish_header_decoded, ?_⟩
  have byte0 : (Access.write (s.reg 2#5) .double).permitted s.mem = true := by
    simpa only [BitVec.add_zero] using write_of_grant writeAligned (by decide) (by decide) writable (off := 0)
  have byte8 : (Access.write (s.reg 2#5 + 8#64) .double).permitted s.mem = true :=
    write_of_grant writeAligned (by decide) (by decide) writable (off := 8)
  have byte16 : (Access.write (s.reg 2#5 + 16#64) .double).permitted s.mem = true :=
    write_of_grant writeAligned (by decide) (by decide) writable (off := 16)
  hmac_range_permissions pc codeAligned exec pc pc pc pc

theorem finish_mask_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0x36#64)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true) :
    RangeAllowed finish base 0x36 9 s := by
  refine ⟨_, outer_mask_decoded, ?_⟩
  hmac_range_permissions pc codeAligned exec pc pc pc pc

theorem finish_outer_call_allowed (base : Addr) (s : CPU)
    (pc : s.pc = routineAddress base finish + 0xb4#64)
    (codeAligned : (routineAddress base finish).toNat % 2 = 0)
    (exec : s.mem.canExec (routineAddress base finish) finish.image.size = true) :
    RangeAllowed finish base 0xb4 3 s := by
  refine ⟨_, outer_call_decoded, ?_⟩
  hmac_range_permissions pc codeAligned exec pc pc pc pc

end Crypto.HMACSHA256.RISCV64
