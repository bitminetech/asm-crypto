import Proofs.Baseline
import Models.ARM64Machine

/-!
Proposed full ARM64 `equal` statement for independent review. No theorem of
this type is asserted here. Do not weaken Entry or any field of Equal to make
a candidate proof pass; changes create a new registered obligation (§8).
-/
namespace Crypto.ARM64.Requirements

open Baseline

structure Arguments where
  codeBase : Address
  messagePointer : Address
  messageExtent : Nat
  digestPointer : Address
  stackPointer : Address
  returnAddress : Address
  message : Reference.ByteList
  authority : Authority

def input (args : Arguments) : Region := ⟨args.messagePointer, args.messageExtent⟩
def header (args : Arguments) : Region := ⟨args.messagePointer, 24⟩
def used (args : Arguments) : Region :=
  ⟨args.messagePointer + BitVec.ofNat 64 args.message.offset, args.message.bytes.size⟩
def output (args : Arguments) : Region := ⟨args.digestPointer, 32⟩
def stack (args : Arguments) : Region := ⟨args.stackPointer - 416, 416⟩
def image (args : Arguments) : Region := ⟨args.codeBase, 896⟩
def constants (args : Arguments) : Region := ⟨args.codeBase + 608, 288⟩

def codeLoaded (args : Arguments) (memory : Memory) : Prop :=
  ∀ i : Fin 224, Round.read32 memory (args.codeBase + BitVec.ofNat 64 (4 * i.val)) = imageWords[i.val]!

def protectedMemory (args : Arguments) (address : Address) : Prop :=
  (input args).Contains address ∨ (output args).Contains address ∨
  (stack args).Contains address ∨ (image args).Contains address

def readable (args : Arguments) (address : Address) : Prop :=
  (header args).Contains address ∨ (used args).Contains address ∨
  (stack args).Contains address ∨ (constants args).Contains address

def writable (args : Arguments) (address : Address) : Prop :=
  (output args).Contains address ∨ (stack args).Contains address

/-- Entry requirements contain only caller-established layout, memory, loading,
ownership, architectural state and argument facts. Stack/output contents and
all nonargument registers are arbitrary. `start` initializes ghost logs only. -/
def Entry (args : Arguments) (s : Machine.State) : Prop :=
  s.pc = args.codeBase ∧ s.sp = args.stackPointer ∧
  Machine.readX s 0 = args.messagePointer ∧ Machine.readX s 1 = args.digestPointer ∧
  Machine.readX s 30 = args.returnAddress ∧
  args.codeBase.toNat % 16 = 0 ∧ args.messagePointer.toNat % 8 = 0 ∧
  args.digestPointer.toNat % 8 = 0 ∧ args.stackPointer.toNat % 16 = 0 ∧
  416 ≤ args.stackPointer.toNat ∧
  args.message.WellFormed ∧ args.message.size ≤ args.messageExtent ∧
  args.messageExtent < 2 ^ 57 ∧
  (input args).Valid ∧ (output args).Valid ∧ (stack args).Valid ∧ (image args).Valid ∧
  (output args).Disjoint (input args) ∧ (output args).Disjoint (stack args) ∧
  (output args).Disjoint (image args) ∧ (stack args).Disjoint (input args) ∧
  (stack args).Disjoint (image args) ∧
  (∀ address, (input args).Contains address → args.authority.readable address) ∧
  (∀ address, writable args address → args.authority.writable address ∧ args.authority.readable address) ∧
  (∀ address, (image args).Contains address → args.authority.readable address) ∧
  (∀ i : Fin 151, args.authority.executable (args.codeBase + BitVec.ofNat 64 (4 * i.val))) ∧
  codeLoaded args s.memory ∧
  Machine.loadLE s.memory args.messagePointer 8 = BitVec.ofNat 64 args.message.size ∧
  Machine.loadLE s.memory (args.messagePointer + 8) 8 = BitVec.ofNat 64 args.message.offset ∧
  Machine.loadLE s.memory (args.messagePointer + 16) 8 = BitVec.ofNat 64 args.message.bytes.size ∧
  (∀ i : Fin args.message.bytes.size,
    s.memory (args.messagePointer + BitVec.ofNat 64 (args.message.offset + i.val)) =
      args.message.bytes[i.val]!.toBitVec)

/-- A conservative instruction budget. Establishing this bound requires the
full loop proof; the formula is not a claim that the proof already exists. -/
def instructionBound (args : Arguments) : Nat :=
  512 + 4000 * ((args.message.bytes.size + 8) / 64 + 1)

def digest (args : Arguments) (s : Machine.State) : Reference.Digest :=
  Vector.ofFn fun i : Fin 32 => UInt8.ofBitVec (s.memory (args.digestPointer + BitVec.ofNat 64 i.val))

def trace (s : Machine.State) : Trace :=
  ⟨s.fetches, s.reads, s.writes, s.stackPointers⟩

def ABI (before after : Machine.State) : Prop :=
  (∀ i : Fin 31, 18 ≤ i.val → after.registers i = before.registers i) ∧
  after.sp = before.sp ∧ after.simd = before.simd ∧
  after.fpcr = before.fpcr ∧ after.fpsr = before.fpsr

def SafeTrace (args : Arguments) (s : Machine.State) : Prop :=
  (∀ address ∈ s.reads, readable args address) ∧
  (∀ address ∈ s.writes, writable args address) ∧
  (∀ address ∈ s.fetches, ∃ i : Fin 151, address = args.codeBase + BitVec.ofNat 64 (4 * i.val)) ∧
  (∀ pointer ∈ s.stackPointers,
    args.stackPointer.toNat - 416 ≤ pointer.toNat ∧
    pointer.toNat ≤ args.stackPointer.toNat ∧ pointer.toNat % 16 = 0)

def Outcome (args : Arguments) (before after : Machine.State) : Prop :=
  after.returned = true ∧ after.pc = args.returnAddress ∧
  Machine.readX after 0 = 0 ∧ digest args after = (Reference.sha256 args.message).2 ∧
  ABI before after ∧ SafeTrace args after ∧ after.fetches.length ≤ instructionBound args

def Post (args : Arguments) (before after : Machine.State) : Prop :=
  Outcome args before after ∧ PreservedOutside before.memory after.memory (output args) (stack args)

def Executes (args : Arguments) (before after : Machine.State) : Prop :=
  Machine.run (instructionBound args) (Machine.start before) = some after

def SamePublicArguments (left right : Arguments) : Prop :=
  left.codeBase = right.codeBase ∧ left.messagePointer = right.messagePointer ∧
  left.messageExtent = right.messageExtent ∧ left.digestPointer = right.digestPointer ∧
  left.stackPointer = right.stackPointer ∧ left.returnAddress = right.returnAddress ∧
  left.message.size = right.message.size ∧ left.message.offset = right.message.offset ∧
  left.message.bytes.size = right.message.bytes.size

/-- Used message bytes, the callee's private stack and its output can differ.
Other initial public bytes must agree. Private temporary register values are
not declassified by this policy; integration must not expose them. -/
def SamePublicMemory (args : Arguments) (left right : Memory) : Prop :=
  ∀ address, ¬(used args).Contains address → ¬(stack args).Contains address →
    ¬(output args).Contains address → left address = right address

def SamePublicResult (args : Arguments) (left right : Machine.State) : Prop :=
  Machine.readX left 0 = Machine.readX right 0 ∧ left.pc = right.pc ∧ left.sp = right.sp ∧
  (∀ address, ¬(used args).Contains address → ¬(stack args).Contains address →
    left.memory address = right.memory address)

/-- Full proof obligation for this pure, effect-free, leaf entry point.
There are no state buffers, software callees, OS boundaries or resource contexts
to omit from these guarantees. No constructor or theorem is supplied here. -/
structure Equal : Prop where
  terminates : ∀ args before, Entry args before →
    ∃ after, Executes args before after ∧ Post args before after
  concurrent : ∀ args before external, Entry args before → Preserves (protectedMemory args) external →
    ∃ after serial,
      Machine.runInterleaved external (instructionBound args) 0 (Machine.start before) = some after ∧
      Executes args before serial ∧ Outcome args before after ∧ trace after = trace serial
  confidentialTrace : ∀ left right beforeL beforeR afterL afterR,
    Entry left beforeL → Entry right beforeR → SamePublicArguments left right →
    Executes left beforeL afterL → Executes right beforeR afterR → trace afterL = trace afterR
  disclosures : ∀ left right beforeL beforeR afterL afterR,
    Entry left beforeL → Entry right beforeR → SamePublicArguments left right →
    SamePublicMemory left beforeL.memory beforeR.memory →
    (Reference.sha256 left.message).2 = (Reference.sha256 right.message).2 →
    Executes left beforeL afterL → Executes right beforeR afterR → SamePublicResult left afterL afterR

end Crypto.ARM64.Requirements
