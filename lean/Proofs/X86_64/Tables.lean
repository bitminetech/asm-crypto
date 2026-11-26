import Proofs.X86_64.Image
import Proofs.X86_64.Memory
import Proofs.X86_64.RoundLoop
import Proofs.ARM64.ImportedCompression

namespace Crypto.X86_64
open X86 Crypto.Reference.WordModel

theorem loaded_word (base : Val) (m : Mem) (loaded : ImageLoaded base m) (off : Nat)
    (bound : off + 4 ≤ image.size) :
    (m.readSize .d (base + BitVec.ofNat 64 off)).setWidth 32 = imageWord off := by
  have read (i : Nat) (h : i < 4) :
      m.read (base + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = image[off+i]!.toBitVec := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact loaded _ (by omega)
  rw [byteView_read32]
  unfold Arm64.Memory.read32 imageWord
  simp only [byteView_read]
  exact congrArg₂ BitVec.append
    (congrArg₂ BitVec.append (congrArg₂ BitVec.append (read 3 (by decide)) (read 2 (by decide)))
      (read 1 (by decide))) (read 0 (by decide))

private theorem scaled (i : Nat) : BitVec.ofNat 64 i * 4 = BitVec.ofNat 64 (4*i) := by
  rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl

private theorem image_size : image.size = 1200 := by decide +kernel

attribute [local irreducible] image EthLib.Cryptography.Hash.Sha256.K Crypto.Reference.WordModel.compress Crypto.Reference.WordModel.schedule
  steps working addH imageWord

theorem loaded_constant (base : Val) (s : Cpu) (loaded : ImageLoaded base s.mem)
    (address : s.regs.get .rdi = base + 0x390) (i : Fin 64) :
    wordsAt s .rdi i.val = Crypto.Reference.WordModel.K[i.val]! := by
  unfold wordsAt
  rw [address, scaled, BitVec.add_assoc]
  change (s.mem.readSize .d (base + (BitVec.ofNat 64 0x390 + BitVec.ofNat 64 (4*i.val)))).setWidth 32 = _
  rw [← BitVec.ofNat_add, loaded_word _ _ loaded]
  · have eq := congrArg (fun v : Vector Word 64 => v[i.val]) image_constants.1
    rw [Crypto.Reference.WordModel.getElem_bang_eq_getElem _ _ i.isLt]
    simpa only [Vector.getElem_ofFn] using eq
  · rw [image_size]
    have := i.isLt
    omega

/-- The FIPS feed-forward of the eight registers at the round-loop exit
equals compression of this block. The premises identify the loaded tables by
their actual addresses and the 16-word block by its expanded schedule. -/
theorem rounds_compress (base : Val) (s : Cpu) (M : Vector Word 16)
    (live : s.ms = none) (pc : s.rip = base + 0x204) (index : s.regs.get .rbx = 0)
    (loaded : ImageLoaded base s.mem) (target : canonical (base + 0x204) = true)
    (constants : s.regs.get .rdi = base + 0x390)
    (schedule : Crypto.ARM64.Imported.wordVector 64 (byteView s.mem) (s.regs.get .rsp) =
      Crypto.Reference.WordModel.schedule M) :
    ∃ out, steps base 2752 s = some out ∧ RoundState base s out (Crypto.Reference.WordModel.schedule M) 64 ∧
      addH (working (project s)) (working (project out)) = Crypto.Reference.WordModel.compress (working (project s)) M := by
  have table (i : Fin 64) : wordsAt s .rsp i.val = (Crypto.Reference.WordModel.schedule M)[i.val]! := by
    have eq := congrArg (fun v : Vector Word 64 => v[i.val]) schedule
    rw [wordsAt, scaled, byteView_read32, Crypto.Reference.WordModel.getElem_bang_eq_getElem _ _ i.isLt]
    simpa only [Crypto.ARM64.Imported.wordVector, Vector.getElem_ofFn] using eq
  obtain ⟨out, run, post⟩ := rounds_loaded base s _ live pc index loaded target
    (loaded_constant _ _ loaded constants) table
  refine ⟨out, run, post, ?_⟩
  rw [post.hash]
  exact Crypto.ARM64.Imported.compress_eq_rounds _ _

end Crypto.X86_64
