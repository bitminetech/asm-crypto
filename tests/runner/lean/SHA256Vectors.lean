import Reference.SHA256
import Reference.SHA256Blocks

/-! Executable vector checks for the imported Lean reference. These tests are
not proofs and introduce no proof axioms. Large-data cases use the bounded-memory
path whose equivalence to the imported reference is proved in Proofs.Repeated. -/

namespace ReferenceVectors

structure Cursor where
  bytes : ByteArray
  position : Nat := 0

def take (cursor : Cursor) (size : Nat) : Except String (ByteArray × Cursor) := do
  if cursor.position + size > cursor.bytes.size then
    throw "truncated vector file"
  return (cursor.bytes.extract cursor.position (cursor.position + size),
          { cursor with position := cursor.position + size })

def take64 (cursor : Cursor) : Except String (Nat × Cursor) := do
  let (bytes, next) ← take cursor 8
  let value := (List.range 8).foldl (fun value i => value + bytes[i]!.toNat * 2 ^ (8 * i)) 0
  return (value, next)

def digest (message : ByteArray) : ByteArray :=
  ByteArray.mk (SHS.SHA256.Impl.sha256 message).toArray

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def runFile (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let (magic, c) ← IO.ofExcept (take ⟨bytes, 0⟩ 8)
  require (magic == "SHA256V1".toUTF8) "bad vector magic"
  let (kind, c) ← IO.ofExcept (take64 c)
  let (count, c) ← IO.ofExcept (take64 c)
  let mut c := c
  let mut checks := 0
  for caseIndex in [:count] do
    if kind == 1 then
      let (size, next) ← IO.ofExcept (take64 c)
      let (message, next) ← IO.ofExcept (take next size)
      let (expected, next) ← IO.ofExcept (take next 32)
      c := next
      require (digest message == expected) s!"{path}: case {caseIndex} failed"
      checks := checks + 1
    else if kind == 2 then
      let (variant, next) ← IO.ofExcept (take64 c)
      let (seedSize, next) ← IO.ofExcept (take64 next)
      let (seed, next) ← IO.ofExcept (take next seedSize)
      let (checkpoints, next) ← IO.ofExcept (take64 next)
      let (expected, next) ← IO.ofExcept (take next (checkpoints * 32))
      c := next
      require (variant == 1 || variant == 2) "unknown Monte Carlo variant"
      let mut seed := seed
      for checkpoint in [:checkpoints] do
        let mut a := seed
        let mut b := seed
        let mut d := seed
        for _ in [:1000] do
          let mut message := a ++ b ++ d
          if variant == 2 then
            if message.size < seedSize then
              message := message ++ ByteArray.mk (Array.replicate (seedSize - message.size) 0)
            message := message.extract 0 seedSize
          let result := digest message
          a := b
          b := d
          d := result
        require (d == expected.extract (32 * checkpoint) (32 * (checkpoint + 1)))
          s!"{path}: checkpoint {checkpoint} failed"
        seed := d
        checks := checks + 1
    else if kind == 3 then
      let (contentSize, next) ← IO.ofExcept (take64 c)
      let (content, next) ← IO.ofExcept (take next contentSize)
      let (fullSize, next) ← IO.ofExcept (take64 next)
      let (expected, next) ← IO.ofExcept (take next 32)
      c := next
      require (content.size > 0 && 64 % content.size == 0 && fullSize % 64 == 0 && fullSize < 2 ^ 61)
        "large-data case is outside the proved repeated-block domain"
      let result := ByteArray.mk (Crypto.Reference.repeatedAlignedDigest content fullSize).toArray
      require (result == expected) s!"{path}: large-data case {caseIndex} failed"
      checks := checks + 1
    else
      throw (IO.userError "unknown vector kind")
  require (c.position == bytes.size) "trailing vector bytes"
  IO.println s!"{path}: {checks} reference checks passed"

end ReferenceVectors

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: reference-vectors FILE.bin ..."
    return (2 : UInt32)
  try
    for path in args do ReferenceVectors.runFile path
    return (0 : UInt32)
  catch e =>
    IO.eprintln e.toString
    return (1 : UInt32)
