import Proofs.RISCV64.Fragments
import Proofs.ARM64.ImportedHashFrame

namespace Crypto.RISCV64

open Crypto.ARM64.Imported (wordVector wordVector_eight bv_add_sub_add_left
  read32_write32_disjoint read32_write32)
open SHS.Equiv.SHA256.Foldl.Sequential (addH)

private def feedWord (r : Reg) (offset : Addr) : List Instruction :=
  [⟨.load .word 5 2 offset, 4⟩, ⟨.addw 5 5 r, 4⟩, ⟨.store .word 5 2 offset, 4⟩]

def feedForward : List Instruction :=
  feedWord 8 256 ++ feedWord 9 260 ++ feedWord 18 264 ++ feedWord 19 268 ++
    feedWord 20 272 ++ feedWord 21 276 ++ feedWord 22 280 ++ feedWord 23 284

theorem feedForward_decoded : decodeSeq 0x28e 24 = some feedForward := by decide +kernel

def storedHash (s : CPU) : Vector Word 8 := wordVector 8 s.mem (s.reg 2 + 256)

theorem load_hash_value (s : CPU) :
    working (run loadHashBody s) = storedHash s := by
  rw [load_hash, storedHash, wordVector_eight]
  simp [BitVec.add_assoc]

private theorem read32_store_other (m : Memory) (sp a b : Addr) (v : Word)
    (apart : 4 ≤ (b-a).toNat ∧ (b-a).toNat ≤ 2^64 - 4) :
    (m.write32 (sp + a) v).read32 (sp+b) = m.read32 (sp+b) := by
  apply read32_write32_disjoint
  rwa [bv_add_sub_add_left]

private theorem wordAddComm (x y : Word) : x + y = y + x := BitVec.add_comm _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem feed_forward_value (s : CPU) :
    storedHash (run feedForward s) = addH (storedHash s) (working s) := by
  simp (config := { decide := true, maxDischargeDepth := 64 }) [storedHash, wordVector_eight,
    run, feedForward, feedWord, Instruction.step, Width.load, Width.store, addH, working,
    BitVec.add_assoc, read32_store_other, read32_write32, narrow_sign, wordAddComm]

private theorem feedWord_frame (s : CPU) (r : Reg) (offset : Nat) (p : Addr)
    (inside : offset + 4 ≤ 288) (outside : 288 ≤ (p - s.reg 2).toNat) :
    let out := run (feedWord r (BitVec.ofNat 64 offset)) s
    out.reg 2 = s.reg 2 ∧ out.mem.cells p = s.mem.cells p := by
  have dist := Crypto.ARM64.Imported.region_word_store_delta (s.reg 2) p offset 288 inside outside
  change 4 ≤ (p - (s.reg 2 + BitVec.ofNat 64 offset)).toNat at dist
  simp (config := { decide := true }) [run, feedWord, Instruction.step, Width.store]
  exact Crypto.ARM64.Imported.write32_cells_outside _ _ _ _ dist

private theorem feed_append_frame (body later : List Instruction) (s : CPU) (p : Addr)
    (outside : 288 ≤ (p - s.reg 2).toNat)
    (frame : let out := run body s
      out.reg 2 = s.reg 2 ∧ out.mem.cells p = s.mem.cells p)
    (rest : ∀ (u : CPU), 288 ≤ (p - u.reg 2).toNat →
      let out := run later u
      out.reg 2 = u.reg 2 ∧ out.mem.cells p = u.mem.cells p) :
    let out := run (body ++ later) s
    out.reg 2 = s.reg 2 ∧ out.mem.cells p = s.mem.cells p := by
  rw [run_append]
  have after := rest (run body s) (by rw [frame.1]; exact outside)
  exact ⟨after.1.trans frame.1, after.2.trans frame.2⟩

attribute [local irreducible] run Arm64.Memory.write32

set_option maxHeartbeats 3000000 in
theorem feed_forward_frame (s : CPU) (p : Addr) (outside : 288 ≤ (p - s.reg 2).toNat) :
    let out := run feedForward s
    out.reg 2 = s.reg 2 ∧ out.mem.cells p = s.mem.cells p := by
  unfold feedForward
  apply feed_append_frame _ _ s p outside (feedWord_frame s 8 256 p (by decide) outside)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 9 260 p (by decide) h)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 18 264 p (by decide) h)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 19 268 p (by decide) h)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 20 272 p (by decide) h)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 21 276 p (by decide) h)
  intro u h
  apply feed_append_frame _ _ u p h (feedWord_frame u 22 280 p (by decide) h)
  intro u h
  exact feedWord_frame u 23 284 p (by decide) h

end Crypto.RISCV64
