import Proofs.X86_64.Fragments
import Proofs.X86_64.Memory
import Proofs.ARM64.ImportedInitialLoad

namespace Crypto.X86_64
open X86

def hashWords (s : DataState) := Crypto.ARM64.Imported.wordVector 8 (byteView s.mem) (s.regs.get .rsp + 256)

def loadHash : WordBlock := [
  (.loadStack .r8 256, 8), (.loadStack .r9 260, 8),
  (.loadStack .r10 264, 8), (.loadStack .r11 268, 8),
  (.loadStack .r12 272, 8), (.loadStack .r13 276, 8),
  (.loadStack .r14 280, 8), (.loadStack .r15 284, 8), (.rr .xor .rbx .rbx, 2)]

private theorem load_decoded : decodeSeq 0x1c2 loadHash.length = some (instructions loadHash) := by
  decide +kernel

private theorem load_value (s : DataState) :
    let out := evalBlock loadHash s
    working out = hashWords s ∧ out.mem = s.mem ∧ out.regs.get .rbx = 0 ∧
    out.regs.get .rsp = s.regs.get .rsp ∧ out.regs.get .rdi = s.regs.get .rdi ∧
    out.regs.get .rbp = s.regs.get .rbp := by
  simp (config := { decide := true }) [working, evalBlock, loadHash, WordInst.eval, WordOp.apply,
    DataState.word, DataState.put, Regs.get_set_ne, hashWords, Crypto.ARM64.Imported.wordVector_eight,
    BitVec.add_assoc, byteView_read32]

theorem hash_loaded (base : Val) (s : Cpu) (live : s.ms = none)
    (loaded : ImageLoaded base s.mem) (pc : s.rip = base + 0x1c2) :
    ∃ out, steps base 9 s = some out ∧ out.ms = none ∧ out.rip = base + 0x204 ∧
      working (project out) = hashWords (project s) ∧ out.mem = s.mem ∧
      out.regs.get .rbx = 0 ∧ out.regs.get .rsp = s.regs.get .rsp ∧
      out.regs.get .rdi = s.regs.get .rdi ∧ out.regs.get .rbp = s.regs.get .rbp := by
  obtain ⟨proj, ok, rip⟩ := word_block loadHash s live
  have post := load_value (project s)
  rw [← proj] at post
  exact ⟨_, fetch_word_block _ _ _ _ live loaded pc (by decide) load_decoded, ok,
    rip.trans (by rw [pc, BitVec.add_assoc]; rfl), post⟩

end Crypto.X86_64
