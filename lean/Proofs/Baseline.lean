import Reference.SHA256

/-!
Shared memory/trace predicates for the stateless crypto baseline. These are
requirements, not a certificate: constructing a value of the target-specific
`Equal` proposition still requires every functional, safety, ABI, bound,
interference and confidentiality proof. The registered statement and its
semantic closure must be independently reviewed and pinned outside candidate
control before a checked verification claim is possible (§8).
-/
namespace Crypto.Baseline

abbrev Address := BitVec 64
abbrev Memory := Address → BitVec 8

structure Region where
  base : Address
  bytes : Nat

def Region.Valid (region : Region) : Prop :=
  region.base.toNat + region.bytes ≤ 2 ^ 64

def Region.Contains (region : Region) (address : Address) : Prop :=
  region.base.toNat ≤ address.toNat ∧ address.toNat < region.base.toNat + region.bytes

def Region.Disjoint (left right : Region) : Prop :=
  ∀ address, ¬(left.Contains address ∧ right.Contains address)

/-- The environment's independently established memory grants. Accurate grants,
ownership and lifetime are caller/environment assumptions, not facts inferred
from a buffer's embedded header. -/
structure Authority where
  readable : Address → Prop
  writable : Address → Prop
  executable : Address → Prop

structure Trace where
  fetches : List Address
  reads : List Address
  writes : List Address
  stackPointers : List Address
  deriving DecidableEq

def PreservedOutside (before after : Memory) (output stack : Region) : Prop :=
  ∀ address, ¬output.Contains address → ¬stack.Contains address → after address = before address

/-- A scheduler/other-thread step preserves the bytes exclusively borrowed by
this call and its immutable code. It may change all other memory arbitrarily. -/
def Preserves (footprint : Address → Prop) (external : Nat → Memory → Memory) : Prop :=
  ∀ tick memory address, footprint address → external tick memory address = memory address

end Crypto.Baseline
