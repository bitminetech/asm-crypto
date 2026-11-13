import Proofs.ARM64.Statement
import Models.ARM64

/-! Executable regression checks of the local ARM64 operational model. -/
open Crypto Crypto.ARM64 Crypto.ARM64.Machine

private def codeBase : Round.Address := 0x20000
private def messageBase : Round.Address := 0x1000
private def outputBase : Round.Address := 0x4000
private def stackTop : Round.Address := 0x10000
private def returnPC : Round.Address := 0x30000

private def memoryFor (message : ByteArray) (seed : Nat) : Round.Memory :=
  fun address =>
    let p := address.toNat
    if codeBase.toNat ≤ p && p < codeBase.toNat + 896 then
      let offset := p - codeBase.toNat
      ((imageWords[offset / 4]! >>> (8 * (offset % 4))).truncate 8)
    else if messageBase.toNat ≤ p && p < messageBase.toNat + 24 then
      let offset := p - messageBase.toNat
      let value := if offset / 8 = 0 then message.size + 48
        else if offset / 8 = 1 then 32 else message.size
      byteAt (BitVec.ofNat 64 value) (offset % 8)
    else if messageBase.toNat + 32 ≤ p && p < messageBase.toNat + 32 + message.size then
      message[p - messageBase.toNat - 32]!.toBitVec
    else BitVec.ofNat 8 (p * 17 + seed)

private def initialState (message : ByteArray) (seed : Nat) : State :=
  { registers := fun i => if i.val = 0 then messageBase
      else if i.val = 1 then outputBase else if i.val = 30 then returnPC
      else BitVec.ofNat 64 (seed * 65537 + i.val)
    sp := stackTop
    pc := codeBase
    memory := memoryFor message seed
    simd := fun i => BitVec.ofNat 128 (seed * 65537 + i.val)
    fpcr := BitVec.ofNat 32 seed
    fpsr := BitVec.ofNat 32 (seed + 1) }

private def argsFor (message : ByteArray) : Requirements.Arguments :=
  { codeBase := codeBase, messagePointer := messageBase
    messageExtent := message.size + 48, digestPointer := outputBase
    stackPointer := stackTop, returnAddress := returnPC
    message := ⟨message.size + 48, 32, message⟩
    authority := ⟨fun _ => True, fun _ => True, fun _ => True⟩ }

private def require (ok : Bool) (what : String) : IO Unit :=
  unless ok do throw (IO.userError what)

private def liftedState (message : ByteArray) (seed : Nat) : Arm64.State :=
  let s := initialState message seed
  let permission := fun address : Round.Address =>
    let p := address.toNat
    if codeBase.toNat ≤ p && p < codeBase.toNat + 604 then some Arm64.Perm.rx
    else if codeBase.toNat + 604 ≤ p && p < codeBase.toNat + 896 then some Arm64.Perm.ro
    else if messageBase.toNat ≤ p && p < messageBase.toNat + message.size + 48 then
      some Arm64.Perm.ro
    else if (stackTop.toNat - 416 ≤ p && p < stackTop.toNat) ||
        (outputBase.toNat ≤ p && p < outputBase.toNat + 32) then some Arm64.Perm.rw
    else none
  { regs := ⟨fun i => readX s i.toNat⟩
    vregs := ⟨fun i => s.simd ⟨i.toNat, i.isLt⟩⟩
    sp := s.sp, pc := s.pc, fpsr := s.fpsr
    mem := Arm64.Memory.ofFn s.memory permission }

private def checkImported (message : ByteArray) (seed : Nat) : IO Unit := do
  let args := argsFor message
  let before := liftedState message seed
  let some after := Imported.runToReturn (Imported.program codeBase)
      (Requirements.instructionBound args) before
    | throw (IO.userError s!"imported model faulted or exhausted fuel, length={message.size}")
  let actual := Vector.ofFn fun i : Fin 32 =>
    UInt8.ofBitVec (after.mem.read8 (outputBase + BitVec.ofNat 64 i.val))
  require (actual == (Reference.sha256 args.message).2) "imported model digest"
  require (after.pc == returnPC && after.sp == stackTop && after.regs.read 0 == 0)
    "imported model return"
  require ((List.range 13).all fun i => after.regs.read (BitVec.ofNat 5 (i + 18)) ==
    before.regs.read (BitVec.ofNat 5 (i + 18))) "imported model GPR preservation"
  require ((List.finRange 32).all fun i => after.vregs.read (BitVec.ofNat 5 i.val) ==
    before.vregs.read (BitVec.ofNat 5 i.val)) "imported model SIMD preservation"
  require (after.fpsr == before.fpsr && after.trace.isEmpty) "imported model effects"

private def check (message : ByteArray) (seed : Nat) : IO Baseline.Trace := do
  let args := argsFor message
  let before := initialState message seed
  let some after := run (Requirements.instructionBound args) (start before)
    | throw (IO.userError s!"model rejected instruction, length={message.size}")
  require after.returned s!"fuel exhausted, length={message.size}"
  require (after.pc == returnPC && after.sp == stackTop && readX after 0 == 0) "return/ABI"
  require (Requirements.digest args after == (Reference.sha256 args.message).2)
    s!"wrong digest, length={message.size}, seed={seed}"
  require ((List.range 13).all fun i => readX after (i + 18) == readX before (i + 18)) "GPR preservation"
  require ((List.finRange 32).all fun i => after.simd i == before.simd i)
    "SIMD preservation"
  require (after.fpcr == before.fpcr && after.fpsr == before.fpsr) "FP state preservation"
  let blocks := message.size / 64 + if message.size % 64 < 56 then 1 else 2
  require (after.fetches.length == 64 + 6 * (message.size % 64) + 3100 * blocks +
      (if message.size % 64 < 56 then 0 else 1))
    s!"instruction count: {after.fetches.length}, length={message.size}"
  require (after.reads.all fun a => by
    exact @decide (Requirements.readable args a) (by
      unfold Requirements.readable Baseline.Region.Contains
      infer_instance)) "read outside permitted region"
  require (after.writes.all fun a => by
    exact @decide (Requirements.writable args a) (by
      unfold Requirements.writable Baseline.Region.Contains
      infer_instance)) "write outside permitted region"
  require (after.fetches.all fun a => a.toNat ≥ codeBase.toNat &&
    a.toNat < codeBase.toNat + 604 && a.toNat % 4 == 0) "invalid fetch"
  require (after.stackPointers.all fun a => a.toNat ≥ stackTop.toNat - 416 &&
    a.toNat ≤ stackTop.toNat && a.toNat % 16 == 0) "stack bound/alignment"
  -- Check protected source bytes and neighbors in this finite test layout.
  for (base, size) in [(messageBase.toNat - 8, message.size + 64),
      (codeBase.toNat, 896), (outputBase.toNat - 8, 8), (outputBase.toNat + 32, 8),
      (stackTop.toNat - 424, 8), (stackTop.toNat, 8)] do
    for i in [:size] do
      let p := BitVec.ofNat 64 (base + i)
      require (after.memory p == before.memory p) "unexpected memory change"
  pure (Requirements.trace after)

def main : IO Unit := do
  for size in [0, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129] do
    let one := ByteArray.mk ((List.range size).map (fun i => UInt8.ofNat (i * 37 + 11))).toArray
    let two := ByteArray.mk (Array.replicate size 0xa5)
    let traceOne ← check one 3
    let traceTwo ← check two 197
    checkImported one 3
    checkImported two 197
    require (traceOne == traceTwo) s!"message-dependent trace, length={size}"
    IO.println s!"ARM64 model length {size}: digest, ABI, trace, bounds and finite frame checks passed"
