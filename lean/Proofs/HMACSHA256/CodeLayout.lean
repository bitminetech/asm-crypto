import Models.HMACSHA256Image

/-! The linked routines have contiguous executable bodies. The layout check
admits only decoded instruction starts as local branch destinations, and
matches every decoded call and return against the recorded sites. -/
namespace Crypto.HMACSHA256

inductive Flow where
  | next
  | repeat
  | branch (target : Int)
  | jump (target : Int)
  | call (target : Int)
  | ret
  deriving DecidableEq

structure Site where
  offset : Nat
  width : Nat
  flow : Flow
  deriving DecidableEq

def scan (decode : Nat → Option (Nat × Flow)) (limit pc : Nat) : Nat → Option (List Site)
  | 0 => if pc = limit then some [] else none
  | fuel + 1 => do
    if pc = limit then return []
    let (width, flow) ← decode pc
    guard (0 < width ∧ pc + width ≤ limit)
    let rest ← scan decode limit (pc + width) fuel
    return ⟨pc, width, flow⟩ :: rest

def checkedLayout (routine : Routine) (decode : Nat → Option (Nat × Flow))
    (calls : List (Nat × Int)) (returnOffset : Nat) : Bool :=
  match scan decode routine.image.size 0 routine.image.size with
  | none => false
  | some sites =>
    let hasLocalTarget (target : Int) : Bool :=
      sites.any fun i => routine.offset + i.offset == target
    let seenCalls := sites.filterMap fun i =>
      match i.flow with
      | .call t => some (i.offset, t)
      | _ => none
    let seenReturns := sites.filterMap fun i =>
      if i.flow = .ret then some i.offset else none
    seenCalls == calls && seenReturns == [returnOffset] &&
      sites.all fun i =>
        let hasNext := hasLocalTarget (routine.offset + i.offset + i.width)
        match i.flow with
        | .next | .repeat | .call _ => hasNext
        | .branch t => hasNext && hasLocalTarget t
        | .jump t => hasLocalTarget t
        | .ret => true

end Crypto.HMACSHA256
