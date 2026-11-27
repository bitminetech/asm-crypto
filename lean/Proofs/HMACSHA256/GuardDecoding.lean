import Proofs.HMACSHA256.ARM64Code
import Proofs.HMACSHA256.X86Code
import Proofs.HMACSHA256.RISCV64Code

/-! The unsigned capacity checks decoded from the linked Linux entry code. -/
namespace Crypto.HMACSHA256

theorem ARM64.guard_decoded :
    ARM64.decodeAt ARM64.entry 0x38 = some (.addSubImm .W64 .SUBS .x4 .x4 96 false) ∧
    ARM64.decodeAt ARM64.entry 0x3c = some (.bCond .CC 0xd8) ∧
    ARM64.decodeAt ARM64.entry 0x40 = some (.addSubShift .W64 .SUBS .xzr .x4 .x5 .LSL 0) ∧
    ARM64.decodeAt ARM64.entry 0x44 = some (.bCond .CC 0xd0) := by
  decide +kernel

theorem X86_64.guard_decoded :
    X86_64.decodeAt X86_64.entry 0x27 = some ⟨.bin .sub .q (.reg .rcx) (.imm 96), 4⟩ ∧
    X86_64.decodeAt X86_64.entry 0x2b = some ⟨.jcc .b 0xcf, 6⟩ ∧
    X86_64.decodeAt X86_64.entry 0x31 = some ⟨.bin .cmp .q (.reg .rcx) (.reg .rdx), 3⟩ ∧
    X86_64.decodeAt X86_64.entry 0x34 = some ⟨.jcc .b 0xc6, 6⟩ := by
  decide +kernel

theorem RISCV64.guard_decoded :
    RISCV64.decodeAt RISCV64.entry 0x2e = some (.scalar ⟨.addi 7 0 96, 4⟩) ∧
    RISCV64.decodeAt RISCV64.entry 0x32 = some (.scalar ⟨.branch .ltu 5 7 0xe0, 4⟩) ∧
    RISCV64.decodeAt RISCV64.entry 0x36 = some (.sub 5#5 5#5 7#5) ∧
    RISCV64.decodeAt RISCV64.entry 0x3a = some (.scalar ⟨.branch .ltu 5 6 0xd8, 4⟩) := by
  decide +kernel

end Crypto.HMACSHA256
