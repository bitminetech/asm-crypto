import Proofs.HMACSHA256.X86KeyTrace
import Proofs.HMACSHA256.X86Key
import Proofs.HMACSHA256.X86KeySetup
import Proofs.HMACSHA256.X86FrameMemory
import Proofs.HMACSHA256.X86ShaResources
import Proofs.HMACSHA256.RegionSlice

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.Baseline (Authority Region)
open Crypto.ARM64.Imported (DataAccess caller_outside_delta caller_region_contains_offset)

def keyInput (s : Cpu) (extent : Nat) : Region := ⟨s.regs.get .rdi, extent⟩
def keyOutput (s : Cpu) : Region := ⟨s.regs.get .rsi, 64⟩
def keyWorkspace (s : Cpu) : Region := ⟨s.regs.get .rsp - 568#64, 568⟩
def keyReturn (s : Cpu) : Region := ⟨s.regs.get .rsp, 8⟩
def keyImage (base : Val) : Region := ⟨routineAddress base key, key.image.size⟩

structure KeyResources (base : Val) (s : Cpu) (extent : Nat) (authority : Authority) : Prop where
  available : 568 ≤ (s.regs.get .rsp).toNat
  aligned : (s.regs.get .rsp).toNat % 16 = 8
  inputAligned : (s.regs.get .rdi).toNat % 8 = 0
  inputValid : (keyInput s extent).Valid
  outputValid : (keyOutput s).Valid
  returnValid : (keyReturn s).Valid
  imageValid : (imageRegion (shaAddress base)).Valid
  keyImageValid : (keyImage base).Valid
  stackInput : (keyWorkspace s).Disjoint (keyInput s extent)
  stackOutput : (keyWorkspace s).Disjoint (keyOutput s)
  stackImage : (keyWorkspace s).Disjoint (imageRegion (shaAddress base))
  stackKeyImage : (keyWorkspace s).Disjoint (keyImage base)
  outputInput : (keyOutput s).Disjoint (keyInput s extent)
  outputImage : (keyOutput s).Disjoint (imageRegion (shaAddress base))
  outputKeyImage : (keyOutput s).Disjoint (keyImage base)
  returnOutput : (keyReturn s).Disjoint (keyOutput s)
  inputCanonical : ∀ p, (keyInput s extent).Contains p → canonical p = true
  outputCanonical : ∀ p, (keyOutput s).Contains p → canonical p = true
  stackCanonical : ∀ p, (keyWorkspace s).Contains p → canonical p = true
  codeCanonical : ∀ p, (imageRegion (shaAddress base)).Contains p → canonical p = true
  helperCanonical : ∀ p, (keyImage base).Contains p → canonical p = true
  returnCanonical : canonical (s.mem.readSize .q (s.regs.get .rsp)) = true
  inputRead : ∀ p, (keyInput s extent).Contains p → authority.readable p
  outputWrite : ∀ p, (keyOutput s).Contains p → authority.writable p
  stackRead : ∀ p, (keyWorkspace s).Contains p → authority.readable p
  stackWrite : ∀ p, (keyWorkspace s).Contains p → authority.writable p
  codeRead : ∀ p, (imageRegion (shaAddress base)).Contains p → authority.readable p
  shaExecutable : ∀ i < codeEnd, authority.executable (shaAddress base + BitVec.ofNat 64 i)

structure KeyFetchAuthority (base : Val) (s : Cpu) (authority : Authority) : Prop where
  text : KeyCodeRights base authority
  immutableText : ∀ i < key.image.size, ¬ authority.writable (routineAddress base key + BitVec.ofNat 64 i)
  returnRead : ∀ j < 8, canonical (s.regs.get .rsp + BitVec.ofNat 64 j) = true ∧
    authority.readable (s.regs.get .rsp + BitVec.ofNat 64 j)

inductive KeyPath (base : Val) (authority : Authority) (input : ByteList) (extent : Nat) (s : Cpu) : Cpu → Prop
  | short {setup copied out : Cpu}
      (length : input.bytes.size ≤ 64)
      (prep : runRange key 0x2b 3 s = some setup)
      (copy : loadedSteps key (routineAddress base key) setup (input.bytes.size + 1) = some copied)
      (jump : runRange key 0x37 1 copied = some out) : KeyPath base authority input extent s out
  | long {out : Cpu} {events : List Event}
      (length : 64 < input.bytes.size)
      (call : runRange key 0x39 3 s = some (longKeyCall s))
      (ran : NativeSerial (shaAddress base) (longKeyCall s) out input extent authority events) :
      KeyPath base authority input extent s out

def keyFrontEvents (base : Val) (s : Cpu) : List Event :=
  frameEnterEvents .key (routineAddress base key) (s.regs.get .rsp) ++ keyInitEvents base ++
  clearKeyEvents (routineAddress base key + 0x1e#64) (s.regs.get .rsi) ++ keyTestEvents base (s.regs.get .rdi)

def keyShaContext (s : Cpu) : Cpu :=
  { s with regs := s.regs.set .rsp (s.regs.get .rsp - 64#64) }

def keyBodyEvents (base : Val) (s : Cpu) (input : ByteList) : List Event :=
  if input.bytes.size ≤ 64 then
    keyCopySetupEvents base (s.regs.get .rdi) ++
    copyEvents (routineAddress base key + 0x35#64) (s.regs.get .rdi + BitVec.ofNat 64 input.offset) (s.regs.get .rsi)
      input.bytes.size ++ keyCopyExitEvents base
  else
    keyCallEvents base (s.regs.get .rsp - 56#64) ++ callEvents (shaAddress base) (keyShaContext s) input

def keyNativeEvents (base : Val) (s : Cpu) (input : ByteList) : List Event :=
  keyFrontEvents base s ++ keyBodyEvents base s input ++
    frameReturnEvents .key (routineAddress base key + 0x44#64) (s.regs.get .rsp - 56#64)

structure KeyExecution (base : Val) (s out : Cpu) (input : ByteList) (extent : Nat) (authority : Authority) where
  clearStart : Cpu
  cleared : Cpu
  tested : Cpu
  beforeReturn : Cpu
  prologue : runRange key 0 7 s = some (enteredFrame .key s)
  setup : runRange key 0xe 5 (enteredFrame .key s) = some clearStart
  clear : loadedSteps key (routineAddress base key) clearStart 9 = some cleared
  lengthTest : runRange key 0x21 3 cleared = some tested
  body : KeyPath base authority input extent tested beforeReturn
  epilogue : runRange key 0x44 8 beforeReturn = some out
  native : KeyFetchAuthority base s authority → LinkedExecution base authority s (keyNativeEvents base s input) out
  live : out.ms = none
  direction : out.flags.df = s.flags.df
  sp : out.regs.get .rsp = s.regs.get .rsp + 8#64
  link : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  saved : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  bytes : ∀ i : Fin 64, out.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = (hmacKey input)[i.val].toBitVec
  frame : ∀ p, ¬ (keyWorkspace s).Contains p → ¬ (keyOutput s).Contains p → out.mem.read p = s.mem.read p

theorem long_key_call_registers (s : Cpu) :
    (longKeyCall s).regs.get .rdi = s.regs.get .rbx ∧
    (longKeyCall s).regs.get .rsi = s.regs.get .rbp ∧
    (longKeyCall s).regs.get .rsp = s.regs.get .rsp - 8#64 ∧
    (longKeyCall s).mem = s.mem.writeSize .q (s.regs.get .rsp - 8#64) (s.rip + 11#64) := by
  simp (config := {decide := true}) [longKeyCall, Cpu.setRip, Cpu.push, Cpu.setReg, Cpu.writeMem,
    Size.bytes, Value.writeView_q, Regs.get_set_same, Regs.get_set_ne]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem key_execution_from_caller (base : Val) (s : Cpu) (input : ByteList) (extent : Nat)
    (authority : Authority)
    (layout : input.WellFormed) (accessible : input.size ≤ extent)
    (sizeBound : input.size < 2 ^ 64) (lengthBound : input.bytes.size < 2 ^ 61)
    (encoding : EncodedByteList (byteView s.mem) (s.regs.get .rdi) input)
    (g : KeyResources base s extent authority) (pc : s.rip = routineAddress base key)
    (live : s.ms = none) (direction : s.flags.df = false)
    (shaCanon : canonical (shaAddress base) = true)
    (shaLoaded : ImageLoaded (shaAddress base) s.mem) (loaded : key.Loaded (routineAddress base key) s.mem.read) :
    ∃ out, Nonempty (KeyExecution base s out input extent authority) := by
  let work := keyWorkspace s
  let saves := regionSlice work 520 48
  let nest := regionSlice work 0 512
  let push := regionSlice work 504 8
  let sp := s.regs.get .rsp
  let start := enteredFrame .key s
  let clear := keyClearState start
  let cleared := storeSteps clear 9
  let tested := keyTestState cleared
  let count := BitVec.ofNat 64 input.bytes.size
  have countBound : input.bytes.size < 2 ^ 64 := by omega
  have available : 568 ≤ sp.toNat := g.available
  have valid : work.Valid := stackRegion_valid sp 568 g.available
  have fits (a n : Nat) (bound : a + n ≤ 568) : a + n ≤ work.bytes := bound
  have area (a n : Nat) (bound : a ≤ 568) :
      regionSlice work a n = ⟨sp - BitVec.ofNat 64 (568 - a), n⟩ :=
    stackRegion_slice sp 568 a n bound
  have inside (a n : Nat) (ok : a + n ≤ 568) (p : Val) (h : (regionSlice work a n).Contains p) :
      work.Contains p := regionSlice_inside _ _ _ valid (fits _ _ ok) p h
  have regionValid (a n : Nat) (ok : a + n ≤ 568) : (regionSlice work a n).Valid :=
    regionSlice_valid _ _ _ valid (fits _ _ ok)
  have saveBase : saves.base = savedBase s := congrArg Region.base (area 520 48 (by decide))
  have startSP : start.regs.get .rsp = sp - 56#64 := by rw [entered_frame_stack, HmacRoutine.locals, BitVec.sub_sub]; rfl
  have startPC : start.rip = routineAddress base key + 0xe#64 := by rw [entered_frame_pc, pc]; rfl
  have startLive := (entered_frame_live .key s).trans live
  have startDF := (entered_frame_direction .key s).trans direction
  obtain ⟨clearDst, saveInput, saveOutput, clearCount, clearZero, clearStack, clearMem, clearDF, clearLive⟩ :=
    key_clear_arguments start
  have dst : clear.regs.get .rdi = s.regs.get .rsi :=
    clearDst.trans (entered_frame_register .key s .rsi (by decide))
  have clearPC : clear.rip = routineAddress base key + 0x1e#64 := by
    change start.rip + 16#64 = _
    rw [startPC, BitVec.add_assoc]
    rfl
  have running : clear.ms = none := clearLive.trans startLive
  have forward : clear.flags.df = false := clearDF.trans startDF
  have entryKeeps (p : Val) (off : ¬ saves.Contains p) : clear.mem.read p = s.mem.read p := by
    have h := caller_outside_delta saves (regionValid 520 48 (by decide)) p off
    rw [saveBase] at h
    rw [clearMem]
    exact frame_saved_outside .key s p h
  have inKeyCode (i : Nat) (h : i < key.image.size) :
      (keyImage base).Contains (routineAddress base key + BitVec.ofNat 64 i) :=
    caller_region_contains_offset (keyImage base) g.keyImageValid i h
  have keyExec (off : Nat) (bound : off < key.image.size) :
      canonical (routineAddress base key + BitVec.ofNat 64 off) = true :=
    g.helperCanonical _ (inKeyCode off bound)
  have codeFrame (i : Nat) (h : i < key.image.size) :
      64 ≤ (routineAddress base key + BitVec.ofNat 64 i - clear.regs.get .rdi).toNat := by
    rw [dst]
    exact caller_outside_delta _ g.outputValid _ (fun hit => g.outputKeyImage _ ⟨hit, inKeyCode i h⟩)
  have clearCode : key.Loaded (routineAddress base key) clear.mem.read := by
    intro i h
    exact (entryKeeps _ (fun hit => g.stackKeyImage _ ⟨inside 520 48 (by decide) _ hit, inKeyCode i h⟩)).trans (loaded i h)
  have clearRun := key_clear_loaded (routineAddress base key) clear clearCode clearPC
    (by rw [clearPC]; exact keyExec 0x1e (by decide +kernel))
    running forward clearCount clearZero codeFrame
  obtain ⟨endClear, clearedLive, zeros, clearPreserves⟩ := clear_key_block clear running forward clearCount clearZero
  have clearedPC : cleared.rip = routineAddress base key + 0x21#64 := by rw [endClear, clearPC, BitVec.add_assoc]; rfl
  obtain ⟨clearedDF, clearedRegs⟩ := clear_key_registers clear running forward clearCount clearZero
  have srcPtr : cleared.regs.get .rbx = s.regs.get .rdi :=
    (clearedRegs _ (by decide) (by decide)).trans (saveInput.trans (entered_frame_register .key s .rdi (by decide)))
  have dstPtr : cleared.regs.get .rbp = s.regs.get .rsi :=
    (clearedRegs _ (by decide) (by decide)).trans (saveOutput.trans (entered_frame_register .key s .rsi (by decide)))
  have stk : cleared.regs.get .rsp = sp - 56#64 :=
    (clearedRegs _ (by decide) (by decide)).trans (clearStack.trans startSP)
  have cleaned (p : Val) (out : ¬ (keyOutput s).Contains p) : cleared.mem.read p = clear.mem.read p :=
    clearPreserves p (by rw [dst]; exact caller_outside_delta _ g.outputValid p out)
  have source : EncodedByteList (byteView cleared.mem) (s.regs.get .rdi) input := by
    apply encoding.preserved layout accessible g.inputValid
    intro p insideInput
    exact congrArg (fun byte => some (none, byte))
      ((cleaned p (fun h => g.outputInput p ⟨h, insideInput⟩)).trans
       (entryKeeps p (fun h => g.stackInput p ⟨inside 520 48 (by decide) p h, insideInput⟩)))
  have countAt : cleared.mem.readSize .q (cleared.regs.get .rbx + 16#64) = count := by
    rw [srcPtr, byteView_read64]
    exact source.count
  have testedRun := key_length_test cleared clearedLive (by rw [clearedPC, BitVec.add_assoc]; exact keyExec 0x39 (by decide +kernel))
  have testedIP : tested.rip = if 64 < input.bytes.size then routineAddress base key + 0x39#64
      else routineAddress base key + 0x2b#64 := by
    change (if 64 < (cleared.mem.readSize .q (cleared.regs.get .rbx + 16#64)).toNat
      then cleared.rip + 24#64 else cleared.rip + 10#64) = _
    rw [countAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound, clearedPC]
    split <;> rw [BitVec.add_assoc] <;> rfl
  have testRegs (r : GPR) (other : r ≠ .rcx) : tested.regs.get r = cleared.regs.get r :=
    Regs.get_set_ne _ _ _ _ other.symm
  have testCode : key.Loaded (routineAddress base key) tested.mem.read := by
    intro i h
    exact (clearPreserves _ (codeFrame i h)).trans (clearCode i h)
  have testSP := (testRegs .rsp (by decide)).trans stk
  have testDF : tested.flags.df = false := clearedDF
  have testLive : tested.ms = none := clearedLive
  have baseRead (off : Nat) (fits : off + 8 ≤ extent) (j : Nat) (hj : j < 8) :
      canonical (s.regs.get .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 j) = true ∧
      authority.readable (s.regs.get .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have inside := caller_region_contains_offset _ g.inputValid (off + j) (by
      change off + j < extent
      omega)
    exact ⟨g.inputCanonical _ inside, g.inputRead _ inside⟩
  have blockWrite (j : Nat) (hj : j < 64) :
      canonical (s.regs.get .rsi + BitVec.ofNat 64 j) = true ∧
      authority.writable (s.regs.get .rsi + BitVec.ofNat 64 j) := by
    have hit := caller_region_contains_offset _ g.outputValid j hj
    exact ⟨g.outputCanonical _ hit, g.outputWrite _ hit⟩
  have prologue := enter_frame .key s live
  have setup := key_clear_setup start startLive
  have throughSetup (right : KeyFetchAuthority base s authority) :
      LinkedExecution base authority s (keyFrontEvents base s) tested := by
    have saveWrite (j : Nat) (hj : j < 48) :
        canonical (savedBase s + BitVec.ofNat 64 j) = true ∧
        authority.writable (savedBase s + BitVec.ofNat 64 j) := by
      have hit : work.Contains (savedBase s + BitVec.ofNat 64 j) := by
        rw [← saveBase]
        exact inside 520 48 (by decide) _ (caller_region_contains_offset saves
          (regionValid 520 48 (by decide)) j hj)
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have pro := run_range_observes (.inr (.inl rfl)) loaded right.immutableText
      (prologue_decoded .key) prologue (frame_prologue_ready .key base authority s pc live direction right.text saveWrite)
    have stage := run_range_observes (.inr (.inl rfl)) (pro.keeps_routine key loaded right.immutableText)
      right.immutableText key_clear_setup_decoded setup (by
        have allowed := key_clear_setup_ready start startPC startLive startDF right.text
        simpa only [key_clear_setup_decoded, Option.getD_some] using allowed)
    have zero := key_clear_fetched_observes clear clearPC clearCode right.immutableText
      (by rw [clearPC]; exact fetch_rights right.text (by decide +kernel : 0x1e + 3 ≤ key.image.size))
      running forward clearCount clearZero (by rw [dst]; exact blockWrite)
    have countRead : ∀ j < 8, canonical (cleared.regs.get .rbx + 16#64 + BitVec.ofNat 64 j) = true ∧
        authority.readable (cleared.regs.get .rbx + 16#64 + BitVec.ofNat 64 j) := by
      rw [srcPtr]
      exact baseRead 16 (by have := layout.1; have := layout.2.2.1; omega)
    have throughClear := pro.append (stage.append zero)
    have lengthTest := run_range_observes (.inr (.inl rfl))
      (throughClear.keeps_routine key loaded right.immutableText) right.immutableText
      key_length_decoded testedRun (by
        have allowed := key_length_ready cleared clearedPC clearedLive clearedDF right.text countRead
        simpa only [key_length_decoded, Option.getD_some] using allowed)
    have proEvents : rangeEvents (saveCode .key) s =
        frameEnterEvents .key (routineAddress base key) (s.regs.get .rsp) := by
      rw [frame_prologue_events _ _ live, pc]
    have initEvents := key_init_events start startPC startLive
    have lengthEvents := key_test_events cleared clearedPC clearedLive
    rw [srcPtr] at lengthEvents
    simp only [key_clear_setup_decoded, key_length_decoded, Option.getD_some, start, cleared] at initEvents lengthEvents
    rw [proEvents] at pro
    rw [initEvents] at stage
    rw [lengthEvents] at lengthTest
    rw [clearPC, dst] at zero
    exact ((pro.append stage).append zero).append lengthTest
  have body : ∃ after, KeyPath base authority input extent tested after ∧
      after.regs.get .rsp = sp - 56#64 ∧ after.rip = routineAddress base key + 0x44#64 ∧ after.ms = none ∧ after.flags.df = false ∧
      (∀ i : Fin 64, after.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) =
        (EthLib.Base.packBytes (hmacKey input))[i.val]!.toBitVec) ∧
      (∀ p, ¬ nest.Contains p → ¬ (keyOutput s).Contains p → after.mem.read p = cleared.mem.read p) ∧
      (KeyFetchAuthority base s authority → LinkedExecution base authority tested (keyBodyEvents base s input) after) := by
    by_cases short : input.bytes.size ≤ 64
    · have atShort := testedIP
      rw [if_neg (Nat.not_lt.mpr short)] at atShort
      let ready := keyCopyState tested
      have readyPC : ready.rip = routineAddress base key + 0x35#64 := by
        change tested.rip + 10#64 = _
        rw [atShort, BitVec.add_assoc]
        rfl
      have rdi : ready.regs.get .rdi = s.regs.get .rsi := by
        simp only [ready, keyCopyState, Regs.get_set_same, testRegs .rbp (by decide), dstPtr]
      have offset : tested.mem.readSize .q (tested.regs.get .rbx + 8#64) = BitVec.ofNat 64 input.offset := by
        rw [testRegs .rbx (by decide), srcPtr, byteView_read64]
        exact source.offset
      have rsi : ready.regs.get .rsi = s.regs.get .rdi + BitVec.ofNat 64 input.offset := by
        have dest : ready.regs.get .rsi =
            tested.mem.readSize .q (tested.regs.get .rbx + 8#64) + tested.regs.get .rbx := by
          simp (config := {decide := true}) only [ready, keyCopyState, Regs.get_set_ne, Regs.get_set_same]
        rw [dest, offset, testRegs .rbx (by decide), srcPtr]
        exact BitVec.add_comm _ _
      have rcx : ready.regs.get .rcx = count := by
        have value : tested.regs.get .rcx = cleared.mem.readSize .q (cleared.regs.get .rbx + 16#64) := by
          simp only [tested, keyTestState, Regs.get_set_same]
        simp (config := {decide := true}) only [ready, keyCopyState, Regs.get_set_ne, value, countAt]
      have payload (i : Nat) (hi : i < input.bytes.size) :
          (keyInput s extent).Contains (s.regs.get .rdi + BitVec.ofNat 64 (input.offset + i)) :=
        caller_region_contains_offset _ g.inputValid _ (by
          change input.offset + i < extent
          have a := layout.2.2.1
          have b := layout.2.2.2
          omega)
      have apart (i : Nat) (hi : i < input.bytes.size) : input.bytes.size ≤
          (ready.regs.get .rsi + BitVec.ofNat 64 i - ready.regs.get .rdi).toNat := by
        rw [rsi, rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact short.trans (caller_outside_delta _ g.outputValid _ (fun h => g.outputInput _ ⟨h,payload i hi⟩))
      have codeAway (i : Nat) (hi : i < key.image.size) : input.bytes.size ≤
          (routineAddress base key + BitVec.ofNat 64 i - ready.regs.get .rdi).toNat := by
        rw [rdi, ← dst]
        exact short.trans (codeFrame i hi)
      have cp := short_key_copy_loaded _ ready input.bytes.size testCode readyPC
        (by rw [readyPC]; exact keyExec 0x35 (by decide +kernel)) testLive testDF rcx short apart codeAway
      obtain ⟨copied, ran, copyPC, copyLive, copiedValue⟩ := short_key_after_clear _ ready input short
        testCode readyPC (by rw [readyPC]; exact keyExec 0x35 (by decide +kernel)) testLive testDF rcx
        (by intro i h; rw [rsi, BitVec.add_assoc, ← BitVec.ofNat_add, ← byteView_read]; exact source.bytes ⟨i,h⟩)
        (by intro i _; rw [rdi, ← dst]; exact zeros i) apart codeAway
      have eq := Option.some.inj (ran.symm.trans cp)
      subst copied
      let afterCopy := copySteps ready (input.bytes.size + 1)
      let returned := { afterCopy with rip := afterCopy.rip + 13#64 }
      have returnPC : returned.rip = routineAddress base key + 0x44#64 := by
        change afterCopy.rip + 13#64 = _
        rw [copyPC, BitVec.add_assoc]
        rfl
      have j := key_copy_exit afterCopy copyLive (by rw [show afterCopy.rip + 13#64 = _ from returnPC]; exact keyExec 0x44 (by decide +kernel))
      have beforeStack : ready.regs.get .rsp = sp - 56#64 := by
        simpa (config := {decide := true}) only [ready, keyCopyState, Regs.get_set_ne] using testSP
      have copySP := copy_done_register ready input.bytes.size testLive testDF rcx countBound apart
        .rsp (by decide) (by decide) (by decide)
      have final := (copy_done ready input.bytes.size testLive testDF rcx countBound apart).2.2.2.2
      have flags := (copy_done ready input.bytes.size testLive testDF rcx countBound apart).2.2.1
      have df : returned.flags.df = false := by
        change afterCopy.flags.df = false
        rw [flags]
        exact testDF
      refine ⟨returned, .short short (key_copy_setup tested testLive) ran j, copySP.trans beforeStack,
        returnPC, copyLive, df, ?_, ?_, ?_⟩
      · intro i
        rw [← rdi]
        exact copiedValue i
      · intro p _ outside
        exact final p (by rw [rdi]; exact short.trans (caller_outside_delta _ g.outputValid p outside))
      · intro right
        have whereKey := (testRegs .rbx (by decide)).trans srcPtr
        have readWord : ∀ j < 8, canonical (tested.regs.get .rbx + 8#64 + BitVec.ofNat 64 j) = true ∧
            authority.readable (tested.regs.get .rbx + 8#64 + BitVec.ofNat 64 j) := by
          rw [whereKey]
          exact baseRead 8 (by have := layout.1; have := layout.2.2.1; omega)
        have prepare := run_range_observes (.inr (.inl rfl)) testCode right.immutableText short_setup_decoded
          (key_copy_setup tested testLive) (by
            have allowed := key_copy_setup_ready tested atShort testLive testDF right.text readWord
            simpa only [short_setup_decoded, Option.getD_some] using allowed)
        have readByte (j : Nat) (hj : j < input.bytes.size) :
            canonical (ready.regs.get .rsi + BitVec.ofNat 64 j) = true ∧
            authority.readable (ready.regs.get .rsi + BitVec.ofNat 64 j) := by
          rw [rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact ⟨g.inputCanonical _ (payload j hj), g.inputRead _ (payload j hj)⟩
        have writeByte (j : Nat) (hj : j < input.bytes.size) :
            canonical (ready.regs.get .rdi + BitVec.ofNat 64 j) = true ∧
            authority.writable (ready.regs.get .rdi + BitVec.ofNat 64 j) := by
          rw [rdi]
          exact blockWrite j (by omega)
        have copied := copy_fetched_observes (count := input.bytes.size) (off := 0x35) ready
          (.inr (.inl rfl)) repeat_decoded.2.1 ⟨by decide, by decide +kernel⟩ readyPC
          (prepare.keeps_routine key testCode right.immutableText) right.immutableText
          (by rw [readyPC]; exact fetch_rights right.text (by decide +kernel : 0x35 + 2 ≤ key.image.size))
          testLive testDF rcx countBound apart readByte writeByte
        have throughCopy := prepare.append copied
        have jump := run_range_observes (.inr (.inl rfl))
          (throughCopy.keeps_routine key testCode right.immutableText) right.immutableText
          key_copy_exit_decoded j (key_copy_exit_ready afterCopy copyPC copyLive df right.text)
        have setupEvents := key_copy_setup_events tested atShort testLive
        rw [whereKey] at setupEvents
        simp only [short_setup_decoded, Option.getD_some] at setupEvents
        have exitEvents := key_copy_exit_events afterCopy copyPC
        simp only [afterCopy] at exitEvents
        rw [setupEvents] at prepare
        rw [exitEvents] at jump
        rw [readyPC, rdi, rsi] at copied
        rw [keyBodyEvents, if_pos short]
        exact (prepare.append copied).append jump
    · have long : 64 < input.bytes.size := by omega
      have atLong := testedIP
      rw [if_pos long] at atLong
      let call := longKeyCall tested
      obtain ⟨calleeInput, calleeOutput, calleeStack, calleeMem⟩ := long_key_call_registers tested
      have inputPtr : call.regs.get .rdi = s.regs.get .rdi :=
        calleeInput.trans ((testRegs _ (by decide)).trans srcPtr)
      have outputPtr : call.regs.get .rsi = s.regs.get .rsi :=
        calleeOutput.trans ((testRegs _ (by decide)).trans dstPtr)
      have incoming : inputRegion call extent = keyInput s extent := by simp only [inputRegion, keyInput, inputPtr]
      have output : outputRegion call = regionSlice (keyOutput s) 0 32 := by simp [outputRegion, keyOutput, regionSlice, outputPtr]
      have lower : Crypto.X86_64.stackRegion call = nest := by
        change (⟨call.regs.get .rsp - 504#64, 512⟩ : Region) = _
        rw [calleeStack, testSP, BitVec.sub_sub, BitVec.sub_sub, show nest = _ from area 0 512 (by decide)]
        rfl
      have pushed : call.regs.get .rsp = push.base := by
        rw [calleeStack, testSP, BitVec.sub_sub, show push = _ from area 504 8 (by decide)]
        rfl
      have slot : tested.regs.get .rsp - 8#64 = push.base := calleeStack.symm.trans pushed
      have framePush (p : Val) (off : ¬ push.Contains p) : call.mem.read p = cleared.mem.read p := by
        rw [calleeMem, slot]
        exact store64_outside _ _ _ _ (caller_outside_delta push (regionValid 504 8 (by decide)) p off)
      have code : ImageLoaded (shaAddress base) call.mem := by
        intro i hi
        let p := shaAddress base + BitVec.ofNat 64 i
        have hit := caller_region_contains_offset _ g.imageValid i hi
        have saved := entryKeeps p (fun h => g.stackImage p ⟨inside 520 48 (by decide) p h, hit⟩)
        have overwrite := cleaned p (fun h => g.outputImage p ⟨h, hit⟩)
        have pushed := framePush p (fun h => g.stackImage p ⟨inside 504 8 (by decide) p h, hit⟩)
        exact pushed.trans (overwrite.trans (saved.trans (shaLoaded i hi)))
      have actual : EncodedByteList (byteView call.mem) (call.regs.get .rdi) input := by
        rw [inputPtr]
        apply source.preserved layout accessible g.inputValid
        intro p h
        exact congrArg (fun byte => some (none, byte))
          (framePush p (fun hit => g.stackInput p ⟨inside 504 8 (by decide) p hit,h⟩))
      have dstFit : 0 + 32 ≤ (keyOutput s).bytes := by change 32 ≤ 64; decide
      have dstValid := regionSlice_valid _ 0 32 g.outputValid dstFit
      have smallOut (p : Val) (h : (outputRegion call).Contains p) : (keyOutput s).Contains p :=
        regionSlice_inside _ _ _ g.outputValid dstFit p (output ▸ h)
      have stackContains (p : Val) (h : (Crypto.X86_64.stackRegion call).Contains p) : work.Contains p :=
        inside 0 512 (by decide) p (show nest.Contains p from lower ▸ h)
      have callAlign : (call.regs.get .rsp).toNat % 16 = 8 := by
        rw [pushed, show push = _ from area 504 8 (by decide)]
        have stack := frame_base_end sp 64 (by omega)
        have align := g.aligned
        change sp.toNat % 16 = 8 at align
        change (sp - 64#64).toNat % 16 = 8
        omega
      have resource : ShaResources (shaAddress base) call input extent authority :=
        ShaResources.of_caller_regions code callAlign (inputPtr.symm ▸ g.inputAligned)
          (incoming.symm ▸ g.inputValid) (output.symm ▸ dstValid) (lower.symm ▸ regionValid 0 512 (by decide))
          g.imageValid
          (fun p h => g.stackInput p ⟨stackContains p h.2, incoming ▸ h.1⟩)
          (fun p h => g.stackImage p ⟨stackContains p h.2, h.1⟩)
          (fun p h => g.stackOutput p ⟨stackContains p h.1, smallOut p h.2⟩)
          (fun p h => g.outputImage p ⟨smallOut p h.2, h.1⟩)
          (fun p h => g.outputInput p ⟨smallOut p h.2, incoming ▸ h.1⟩)
          g.codeCanonical (fun p h => g.inputCanonical p (incoming ▸ h))
          (fun p h => g.stackCanonical p (stackContains p h)) (fun p h => g.outputCanonical p (smallOut p h))
          (fun p h => g.inputRead p (incoming ▸ h)) g.codeRead
          (fun p h => g.stackRead p (stackContains p h)) (fun p h => g.stackWrite p (stackContains p h))
          (fun p h => g.outputWrite p (smallOut p h)) g.shaExecutable
      have link : call.mem.readSize .q (call.regs.get .rsp) = routineAddress base key + 0x44#64 := by
        rw [calleeMem, calleeStack, read64_write64, atLong, BitVec.add_assoc]
        rfl
      have contract := establish_sha_entry layout accessible sizeBound lengthBound actual resource
        (key_call_target _ _ atLong) testLive (by rw [link]; exact keyExec 0x44 (by decide +kernel))
      have tailDst : tested.regs.get .rbp = s.regs.get .rsi := (testRegs _ (by decide)).trans dstPtr
      have tailSafe (i : Fin 64) (h : (Crypto.X86_64.stackRegion call).Contains (s.regs.get .rsi + BitVec.ofNat 64 i.val)) : False :=
        g.stackOutput _ ⟨stackContains _ h, caller_region_contains_offset _ g.outputValid i.val i.isLt⟩
      obtain ⟨out, events, transfer, sha, digest⟩ := long_key_after_clear base tested input extent authority long
        atLong testLive shaCanon contract
        (by
          intro i _
          rw [tailDst]
          change call.mem.read (s.regs.get .rsi + BitVec.ofNat 64 i.val) = 0#8
          have safe := caller_region_contains_offset (keyOutput s) g.outputValid i.val i.isLt
          rw [framePush (s.regs.get .rsi + BitVec.ofNat 64 i.val)
            (fun h => g.stackOutput _ ⟨inside 504 8 (by decide) _ h,safe⟩), ← dst]
          exact zeros i)
        (by intro i _; rw [tailDst]; exact tailSafe i)
      have flags : out.flags.df = call.flags.df := by
        have same := congrArg (fun p => p.2.2.2.2.2) sha.platform
        exact same
      refine ⟨out, .long long transfer sha, ?_, sha.result.pc.trans link, sha.result.live, flags.trans testDF, ?_, ?_, ?_⟩
      · rw [sha.result.stack, calleeStack]
        change tested.regs.get .rsp - 8#64 + 8#64 = _
        rw [BitVec.sub_add_cancel, testSP]
      · intro i
        rw [← tailDst]
        exact digest i
      · intro p noNest noOutput
        have noPush : ¬ push.Contains p := fun h => noNest (regionSlice_inside nest 504 8
          (regionValid 0 512 (by decide)) (by change 504 + 8 ≤ 512; decide) p
          (by simpa only [nest, push, regionSlice, BitVec.add_zero] using h))
        rw [sha.result.frame p (fun h => noOutput (smallOut p h)) (by rwa [lower])]
        exact framePush p noPush
      · intro right
        have pushRight (j : Nat) (hj : j < 8) :
            canonical (tested.regs.get .rsp - 8#64 + BitVec.ofNat 64 j) = true ∧
            authority.writable (tested.regs.get .rsp - 8#64 + BitVec.ofNat 64 j) := by
          rw [slot]
          have hit := inside 504 8 (by decide) _ (caller_region_contains_offset push
            (regionValid 504 8 (by decide)) j hj)
          exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
        have invoke := run_range_observes (.inr (.inl rfl)) testCode right.immutableText long_call_decoded
          transfer (by
            have allowed := key_call_ready tested atLong testLive testDF right.text pushRight
            simpa only [long_call_decoded, Option.getD_some] using allowed)
        have invokeEvents := key_call_events tested atLong testLive
        rw [testSP] at invokeEvents
        simp only [long_call_decoded, Option.getD_some] at invokeEvents
        have hashEvents : events = callEvents (shaAddress base) (keyShaContext s) input := by
          rw [sha.publicTrace]
          have a : call.regs.get .rsp = (keyShaContext s).regs.get .rsp := by
            rw [calleeStack, testSP, BitVec.sub_sub, keyShaContext, Regs.get_set_same]
            rfl
          have b : call.regs.get .rdi = (keyShaContext s).regs.get .rdi := by
            rw [inputPtr]
            exact (Regs.get_set_ne _ _ _ _ (by decide : GPR.rsp ≠ .rdi)).symm
          have c : call.regs.get .rsi = (keyShaContext s).regs.get .rsi := by
            rw [outputPtr]
            exact (Regs.get_set_ne _ _ _ _ (by decide : GPR.rsp ≠ .rsi)).symm
          change callEvents (shaAddress base) call input = _
          simp only [callEvents, frameBase, a, b, c]
        have throughHash := invoke.append (LinkedExecution.shaCall sha (.nil _))
        simpa only [keyBodyEvents, if_neg short, invokeEvents, hashEvents, List.append_nil] using throughHash
  obtain ⟨after, path, afterSp, afterPC, afterLive, afterDF, digest, kept, traceBody⟩ := body
  have keepOuter (p : Val) (offStack : ¬ work.Contains p) (offOutput : ¬ (keyOutput s).Contains p) :
      after.mem.read p = s.mem.read p :=
    (kept p (fun h => offStack (inside 0 512 (by decide) p h)) offOutput).trans
      ((cleaned p offOutput).trans (entryKeeps p (fun h => offStack (inside 520 48 (by decide) p h))))
  have returnSlot : after.regs.get .rsp + 56#64 = sp := by rw [afterSp, BitVec.sub_add_cancel]
  have link : after.mem.readSize .q (after.regs.get .rsp + 56#64) = s.mem.readSize .q sp := by
    rw [returnSlot]
    apply Mem.readN_congr
    intro i hi
    let p := sp + BitVec.ofNat 64 i
    have hit := caller_region_contains_offset (keyReturn s) g.returnValid i hi
    have off : ¬ work.Contains p := by
      intro held
      have bound := frame_base_end sp 568 g.available
      change (sp - 568#64).toNat ≤ p.toNat ∧ p.toNat < (sp - 568#64).toNat + 568 at held
      change sp.toNat ≤ p.toNat ∧ p.toNat < sp.toNat + 8 at hit
      omega
    exact keepOuter p off (fun other => g.returnOutput _ ⟨hit,other⟩)
  have atSave : after.regs.get .rsp + 8#64 = savedBase s := by
    rw [afterSp, savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    rfl
  have savedValues (i : Fin 6) : after.mem.readSize .q
      (after.regs.get .rsp + 8#64 + BitVec.ofNat 64 (savedOffset i)) = s.regs.get (savedReg i) := by
    rw [atSave]
    refine (Mem.readN_congr _ _ _ 8 ?_).trans (frame_saved_word .key s i)
    intro j hj
    let p := savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j
    have hit : saves.Contains p := by
      change saves.Contains (savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← saveBase]
      exact caller_region_contains_offset saves (regionValid 520 48 (by decide)) _ (by
        change savedOffset i + j < 48
        have hi := i.isLt
        unfold savedOffset
        omega)
    have offNest : ¬ nest.Contains p := fun h =>
      regionSlices_disjoint _ 0 512 520 48 valid (by decide) (fits _ _ (by decide)) p ⟨h, hit⟩
    have offOut : ¬ (keyOutput s).Contains p := fun h => g.stackOutput p ⟨inside 520 48 (by decide) p hit, h⟩
    rw [kept p offNest offOut, cleaned p offOut, clearMem]
  let out := restoredState after 8#64 4
  obtain ⟨outSp, outLink, memory⟩ := restored_stack_and_link after 8#64 4
  have epilogue := (returns after afterLive).2.1 (by rw [link]; exact g.returnCanonical)
  refine ⟨out, ⟨⟨clear, cleared, tested, after, enter_frame .key s live, key_clear_setup start startLive,
    clearRun, testedRun, path, epilogue, ?_, (restored_live _ _ _).trans afterLive,
    (restored_direction _ _ _).trans (afterDF.trans direction.symm), ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro right
    have untilReturn := (throughSetup right).append (traceBody right)
    have readRestored (j : Nat) (hj : j < 56) :
        canonical (after.regs.get .rsp + 8#64 + BitVec.ofNat 64 j) = true ∧
        authority.readable (after.regs.get .rsp + 8#64 + BitVec.ofNat 64 j) := by
      rw [atSave]
      by_cases inFrame : j < 48
      · have hit := inside 520 48 (by decide) (savedBase s + BitVec.ofNat 64 j) (by
          rw [← saveBase]
          exact caller_region_contains_offset saves (regionValid 520 48 (by decide)) j inFrame)
        exact ⟨g.stackCanonical _ hit, g.stackRead _ hit⟩
      · have split : savedBase s + BitVec.ofNat 64 j = s.regs.get .rsp + BitVec.ofNat 64 (j - 48) := by
          have sum : j = 48 + (j - 48) := by omega
          nth_rw 1 [sum]
          rw [BitVec.ofNat_add, ← BitVec.add_assoc]
          exact congrArg (· + BitVec.ofNat 64 (j - 48)) (BitVec.sub_add_cancel _ _)
        rw [split]
        exact right.returnRead _ (by omega)
    have returning := run_range_observes (.inr (.inl rfl))
      (untilReturn.keeps_routine key loaded right.immutableText) right.immutableText
      key_return_decoded epilogue (frame_epilogue_ready .key base authority after afterPC
        afterLive afterDF right.text readRestored)
    have retEvents := frame_return_events .key after afterLive
    rw [afterPC, afterSp] at retEvents
    simp only [HmacRoutine.locals, HmacRoutine.allocLength, sp] at retEvents
    rw [retEvents] at returning
    exact untilReturn.append returning
  · rw [outSp, afterSp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]
    rfl
  · rw [outLink, BitVec.add_assoc]
    exact link
  · intro i
    exact (restored_register after 8#64 4 i).trans (savedValues i)
  · intro i
    rw [memory]
    have outByte := digest i
    rw [getElem!_pos _ _ (by change i.val < (hmacKey input).toArray.size; rw [(hmacKey input).size_toArray]; exact i.isLt)] at outByte
    exact outByte
  · intro p a b
    rw [memory]
    exact keepOuter p a b

structure KeyPublic (s t : Cpu) (a b : ByteList) : Prop where
  stack : s.regs.get .rsp = t.regs.get .rsp
  input : s.regs.get .rdi = t.regs.get .rdi
  output : s.regs.get .rsi = t.regs.get .rsi
  offset : a.offset = b.offset
  count : a.bytes.size = b.bytes.size

theorem key_native_events_equal {base : Val} {s t : Cpu} {a b : ByteList}
    (same : KeyPublic s t a b) : keyNativeEvents base s a = keyNativeEvents base t b := by
  have padding : Crypto.ARM64.Imported.paddingBlockCount a.bytes = Crypto.ARM64.Imported.paddingBlockCount b.bytes := by
    unfold Crypto.ARM64.Imported.paddingBlockCount
    rw [same.count]
  simp (config := { decide := true }) only [keyNativeEvents, keyFrontEvents, keyBodyEvents,
    keyShaContext, callEvents, frameBase, bodyEvents, preparedCallEvents,
    Regs.get_set_same, Regs.get_set_ne, same.stack, same.input, same.output, same.offset,
    same.count, padding]

end Crypto.HMACSHA256.X86_64
