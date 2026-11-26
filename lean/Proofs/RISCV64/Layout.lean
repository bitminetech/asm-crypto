import Models.RISCV64SHA256Decode

namespace Crypto.RISCV64

def jumpTargets : List Nat := [0x52, 0x6a, 0x82, 0xf2, 0xf8, 0x134, 0x1d0, 0x2f6, 0x300]

private def validEdge (off : Nat) (i : Instruction) : Bool :=
  let target := fun disp => jumpTargets.contains ((BitVec.ofNat 64 off + disp).toNat)
  match i.op with
  | .ret => off == 0x414
  | .branch _ _ _ disp | .jump disp => target disp
  | _ => true

/-- Walk complete instructions in the image and check the target of each jump.
The endpoints in the segment list are all reached by successive decodes. -/
def walk (off : Nat) : Nat → Option Nat
  | 0 => some off
  | n+1 => (decodeAt off).bind fun i =>
    if validEdge off i then walk (off + i.bytes) n else none

theorem walk_add (off left right : Nat) :
    walk off (left + right) = (walk off left).bind (walk · right) := by
  induction left generalizing off with
  | zero => simp [walk]
  | succ left ih =>
    rw [Nat.succ_add]
    simp only [walk]
    cases decoded : decodeAt off with
    | none => rfl
    | some i =>
      simp only [Option.bind_some]
      split <;> simp_all

/-- Counts and endpoints are kept in short segments so the kernel replays each
part independently. Every direct jump target is one of these boundaries. -/
def segments : List (Nat × Nat × Nat) := [
  (0x0, 25, 0x38),
  (0x38, 9, 0x52),
  (0x52, 7, 0x6a),
  (0x6a, 7, 0x82),
  (0x82, 2, 0x8a),
  (0x8a, 25, 0xe6),
  (0xe6, 4, 0xf2),
  (0xf2, 2, 0xf8),
  (0xf8, 17, 0x134),
  (0x134, 2, 0x13c),
  (0x13c, 25, 0x1a0),
  (0x1a0, 13, 0x1d0),
  (0x1d0, 12, 0x200),
  (0x200, 25, 0x264),
  (0x264, 25, 0x2b6),
  (0x2b6, 17, 0x2f6),
  (0x2f6, 5, 0x300),
  (0x300, 3, 0x30c),
  (0x30c, 25, 0x370),
  (0x370, 25, 0x3d4),
  (0x3d4, 21, 0x414),
  (0x414, 1, 0x416)
]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 12000 in
private theorem segments_checked : ∀ part ∈ segments, walk part.1 part.2.1 = some part.2.2 := by
  intro part member
  simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

private def join (parts : List (Nat × Nat × Nat)) (start : Nat) : Option Nat :=
  match parts with
  | [] => some start
  | (first, _, last) :: rest => if first = start then join rest last else none

private def count (parts : List (Nat × Nat × Nat)) : Nat :=
  (parts.map (fun part => part.2.1)).sum

private theorem walk_join (parts : List (Nat × Nat × Nat)) (start finish : Nat)
    (adjacent : join parts start = some finish)
    (checks : ∀ part ∈ parts, walk part.1 part.2.1 = some part.2.2) :
    walk start (count parts) = some finish := by
  induction parts generalizing start with
  | nil => simpa [join, count, walk] using adjacent
  | cons part rest ih =>
    rcases part with ⟨first, n, last⟩
    simp only [join] at adjacent
    split at adjacent
    · next equal =>
      subst first
      simp only [count, List.map_cons, List.sum_cons]
      rw [walk_add, checks _ List.mem_cons_self]
      exact ih _ adjacent (fun part h => checks part (List.mem_cons_of_mem _ h))
    · contradiction

theorem complete_layout : walk 0 297 = some codeEnd :=
  walk_join segments 0 codeEnd (by decide +kernel) segments_checked

theorem jumpTargets_are_boundaries :
    ∀ target ∈ jumpTargets, target ∈ segments.map (fun part => part.1) := by
  decide +kernel

end Crypto.RISCV64
