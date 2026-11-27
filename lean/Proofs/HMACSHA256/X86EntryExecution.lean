import Proofs.HMACSHA256.X86EntryTrace
import Proofs.HMACSHA256.X86EntryResources
import Proofs.HMACSHA256.X86Inner

namespace Crypto.HMACSHA256.X86_64

open X86 Crypto.X86_64 Crypto.Reference
open Crypto.ARM64.Imported (caller_outside_delta caller_region_contains_offset memoryBytes32)
open Crypto.Baseline (Authority Region)

structure EntryResult (s out : Cpu) (input message : ByteList) (capacity : Nat) : Prop where
  status : out.regs.get .rax = BitVec.ofNat 64 (hmacSha256 input message capacity).status
  live : out.ms = none
  stack : out.regs.get .rsp = s.regs.get .rsp + 8#64
  link : out.rip = s.mem.readSize .q (s.regs.get .rsp)
  registers : ∀ i : Fin 6, out.regs.get (savedReg i) = s.regs.get (savedReg i)
  failure : capacity < hmacScratchRequired message →
    ∀ p, ¬ (entrySaved s).Contains p → out.mem.read p = s.mem.read p
  digest : hmacScratchRequired message ≤ capacity →
    memoryBytes32 (byteView out.mem) (s.regs.get .rcx) =
      (EthLib.Cryptography.Hash.Hmac.hmac32 input.bytes message.bytes).map UInt8.toBitVec
  inner : hmacScratchRequired message ≤ capacity →
    EncodedByteList (byteView out.mem) (s.regs.get .rdx + 8#64) (hmacInner message (hmacKey input) capacity)
  frame : ∀ p, ¬ (entryWorkspace s).Contains p →
    ¬ (⟨s.regs.get .rdx + 8#64, 88 + message.bytes.size⟩ : Region).Contains p →
    ¬ (entryMac s).Contains p → out.mem.read p = s.mem.read p

inductive EntryBody (base : Val) (authority : Authority) (s : Cpu) (input message : ByteList)
    (keyExtent capacity : Nat) : Cpu → Prop where
  | short (small : capacity < hmacScratchRequired message) : EntryBody base authority s input message keyExtent capacity s
  | full {postKey header padded copier prepared afterFinish : Cpu}
      (keyCall : runRange entry 0x3a 3 s = some (entryKeyCall s))
      (keyRan : KeyExecution base (entryKeyCall s) postKey input keyExtent authority)
      (head : runRange entry 0x45 8 postKey = some header)
      (pad : runRange entry 0x72 24 header = some padded)
      (copySetup : runRange entry 0xd9 4 padded = some copier)
      (copy : loadedSteps entry (routineAddress base entry) copier (message.bytes.size + 1) = some prepared)
      (finishCall : runRange entry 0xeb 4 prepared = some (entryFinishCall prepared))
      (finishRan : Finished base (entryFinishCall prepared) afterFinish
        (hmacInner message (hmacKey input) capacity) (hmacKey input) (capacity - 8) authority)
      (status : runRange entry 0xfb 1 afterFinish = some (successState afterFinish)) :
        EntryBody base authority s input message keyExtent capacity (successState afterFinish)

structure EntryFetchAuthority (base : Val) (s : Cpu) (capacity : Nat) (authority : Authority) : Prop where
  entryExec : EntryCodeRights base authority
  entryText : ∀ i < entry.image.size, ¬ authority.writable (routineAddress base entry + BitVec.ofNat 64 i)
  keyExec : KeyCodeRights base authority
  keyText : ∀ i < key.image.size, ¬ authority.writable (routineAddress base key + BitVec.ofNat 64 i)
  finishExec : FinishCodeRights base authority
  finishText : ∀ i < finish.image.size, ¬ authority.writable (routineAddress base finish + BitVec.ofNat 64 i)
  finishLoaded : finish.Loaded (routineAddress base finish) s.mem.read
  scratchWrite : ∀ p, (entryScratch s capacity).Contains p → authority.writable p
  returnRead : ReadWord authority (s.regs.get .rsp)

def entryFrontEvents (base : Val) (s : Cpu) (capacity : Nat) : List Event :=
  frameEnterEvents .entry (routineAddress base entry) (s.regs.get .rsp) ++
  entryCapacityEvents base (s.regs.get .rdx) (s.regs.get .rsi) ++
  x86GuardEvents (routineAddress base entry + 0x27#64) capacity

def entryKeyContext (s : Cpu) : Cpu :=
  shaTraceContext s (s.regs.get .rsp - 128#64) (s.regs.get .rdi) (s.regs.get .rsp - 120#64)

def entryFinishContext (s : Cpu) : Cpu :=
  let inner := shaTraceContext s (s.regs.get .rsp - 128#64) (s.regs.get .rdx + 8#64) (s.regs.get .rsp - 120#64)
  { inner with regs := inner.regs.set .rdx (s.regs.get .rcx) }

private theorem entry_finish_context_arguments (s : Cpu) :
    (entryFinishContext s).regs.get .rsp = s.regs.get .rsp - 128#64 ∧
    (entryFinishContext s).regs.get .rdi = s.regs.get .rdx + 8#64 ∧
    (entryFinishContext s).regs.get .rsi = s.regs.get .rsp - 120#64 ∧
    (entryFinishContext s).regs.get .rdx = s.regs.get .rcx := by
  obtain ⟨sp, input, output⟩ := sha_trace_context s (s.regs.get .rsp - 128#64)
    (s.regs.get .rdx + 8#64) (s.regs.get .rsp - 120#64)
  simpa (config := {decide := true}) only [entryFinishContext, Regs.get_set_same, Regs.get_set_ne, and_true]
    using And.intro sp (And.intro input output)

def entryBodyEvents (base : Val) (s : Cpu) (input message : ByteList) (capacity : Nat) : List Event :=
  if capacity < hmacScratchRequired message then [] else
    let stack := s.regs.get .rsp - 120#64
    let scratch := s.regs.get .rdx
    let payload := s.regs.get .rsi
    let k0 := hmacKey input
    entryKeySetupEvents base stack ++ keyNativeEvents base (entryKeyContext s) input ++
    entryHeaderEvents base scratch payload ++
    x86PadEvents false (routineAddress base entry + 0x72#64) stack scratch 8 ++
    entryCopySetupEvents base payload ++
    copyEvents (routineAddress base entry + 0xe9#64) (payload + BitVec.ofNat 64 message.offset) (scratch + 96#64)
      message.bytes.size ++
    entryFinishSetupEvents base stack ++
    finishNativeEvents base (entryFinishContext s) (hmacInner message k0 capacity) k0 ++ entryStatusEvents base

def entryNativeEvents (base : Val) (s : Cpu) (input message : ByteList) (capacity : Nat) : List Event :=
  entryFrontEvents base s capacity ++ entryBodyEvents base s input message capacity ++
    frameReturnEvents .entry (routineAddress base entry + 0x100#64) (s.regs.get .rsp - 120#64)

structure EntryExecution (base : Val) (s out : Cpu) (input message : ByteList)
    (keyExtent capacity : Nat) (authority : Authority) where
  checked : Cpu
  beforeReturn : Cpu
  front : EntryPrefix base s checked capacity message.bytes.size
  body : EntryBody base authority checked input message keyExtent capacity beforeReturn
  tail : runRange entry 0x100 8 beforeReturn = some out
  native : EntryFetchAuthority base s capacity authority →
    LinkedExecution base authority s (entryNativeEvents base s input message capacity) out
  result : EntryResult s out input message capacity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 7000000 in
theorem entry_execution_from_caller (base : Val) (s : Cpu) (input message : ByteList)
    (keyExtent messageExtent capacity : Nat) (authority : Authority)
    (keyLayout : input.WellFormed) (messageLayout : message.WellFormed)
    (keyFits : input.size ≤ keyExtent) (messageFits : message.size ≤ messageExtent)
    (keySize : input.size < 2 ^ 64) (keyLength : input.bytes.size < 2 ^ 61)
    (messageLength : message.bytes.size < 2 ^ 61 - 64)
    (encodedKey : EncodedByteList (byteView s.mem) (s.regs.get .rdi) input)
    (encodedMessage : EncodedByteList (byteView s.mem) (s.regs.get .rsi) message)
    (size : s.mem.readSize .q (s.regs.get .rdx) = BitVec.ofNat 64 capacity)
    (minCap : 8 ≤ capacity) (cap64 : capacity < 2 ^ 64)
    (pc : s.rip = routineAddress base entry) (live : s.ms = none) (df : s.flags.df = false)
    (g : EntryResources base s keyExtent messageExtent capacity authority)
    (entryLoaded : entry.Loaded (routineAddress base entry) s.mem.read)
    (keyLoaded : key.Loaded (routineAddress base key) s.mem.read)
    (shaLoaded : ImageLoaded (shaAddress base) s.mem) :
    ∃ out, Nonempty (EntryExecution base s out input message keyExtent capacity authority) := by
  let sp := s.regs.get .rsp
  let work := entryWorkspace s
  let saved := entrySaved s
  let push := entryHelperReturn s
  let block := entryKeyBlock s
  let changed := regionSlice (entryScratch s capacity) 8 (88 + message.bytes.size)
  let k0 := hmacKey input
  have within : 824 ≤ sp.toNat := g.available
  have stackValid := stackRegion_valid sp 824 within
  have belowReturn := frame_base_end sp 824 within
  have inScratch (p : Val) (room : 96 + message.bytes.size ≤ capacity) (h : changed.Contains p) :
      (entryScratch s capacity).Contains p :=
    regionSlice_inside _ _ _ g.scratchValid (by change 8 + (88 + _) ≤ capacity; omega) p h
  have savedRegion : saved = regionSlice work 776 48 := (entry_slice s 776 48 (by decide)).symm
  have savedValid : saved.Valid := by rw [savedRegion]; exact entry_slice_valid g 776 48 (by decide)
  have savedInside (p : Val) (hit : saved.Contains p) : work.Contains p := by
    rw [savedRegion] at hit
    exact entry_slice_inside g 776 48 (by decide) p hit
  have metadata : 24 ≤ messageExtent := by
    have a := messageLayout.1
    have b := messageLayout.2.2.1
    omega
  have scratchOff (i : Nat) (hi : i < 8) :
      48 ≤ (s.regs.get .rdx + BitVec.ofNat 64 i - savedBase s).toNat := by
    have hit := caller_region_contains_offset (entryScratch s capacity) g.scratchValid i (by change i < capacity; omega)
    exact caller_outside_delta saved savedValid _
      (fun h => g.stackScratch _ ⟨savedInside _ h,hit⟩)
  have msgOff (i : Nat) (hi : i < 8) :
      48 ≤ (s.regs.get .rsi + 16#64 + BitVec.ofNat 64 i - savedBase s).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hit := caller_region_contains_offset _ g.messageValid (16 + i) (by change 16 + i < messageExtent; omega)
    exact caller_outside_delta saved savedValid _
      (fun h => g.stackMessage _ ⟨savedInside _ h,hit⟩)
  have msgLen := (byteView_read64 s.mem _).trans encodedMessage.count
  obtain ⟨checked, ⟨front⟩⟩ := entry_prefix base s capacity message.bytes.size cap64 (by omega)
    size msgLen scratchOff msgOff pc live (g.entry_pc_canonical 0x100 (by decide +kernel))
  have frontFrame (p : Val) (off : ¬ saved.Contains p) : checked.mem.read p = s.mem.read p := by
    rw [front.memory]
    exact frame_saved_outside _ _ _ (caller_outside_delta saved savedValid p off)
  have frontStack (p : Val) (off : ¬ work.Contains p) : checked.mem.read p = s.mem.read p :=
    frontFrame p (fun h => off (savedInside p h))
  have outsideRet (i : Nat) (hi : i < 8) : ¬ work.Contains (sp + BitVec.ofNat 64 i) := by
    have hit := caller_region_contains_offset (entryReturn s) g.returnValid i hi
    intro h
    change (sp - 824#64).toNat ≤ _ ∧ (sp + BitVec.ofNat 64 i).toNat < (sp - 824#64).toNat + 824 at h
    change sp.toNat ≤ (sp + BitVec.ofNat 64 i).toNat ∧ _ at hit
    change (sp - 824#64).toNat + 824 = sp.toNat at belowReturn
    omega
  have blockBase : block.base = sp - 120#64 := congrArg Region.base (entry_slice s 704 64 (by decide))
  have pushBase : push.base = sp - 128#64 := congrArg Region.base (entry_slice s 696 8 (by decide))
  have stackAt (off n : Nat) (fit : off + n ≤ 824) (i : Nat) (hi : i < n) :
      work.Contains ((regionSlice work off n).base + BitVec.ofNat 64 i) :=
    entry_slice_inside g off n fit _ (caller_region_contains_offset _ (entry_slice_valid g off n fit) i hi)
  have scratchRead : ReadWord authority (s.regs.get .rdx) := by
    intro i hi
    have hit := caller_region_contains_offset (entryScratch s capacity) g.scratchValid i (by
      change i < capacity
      omega)
    exact ⟨g.scratchCanonical _ hit, g.scratchRead _ hit⟩
  have msgRead (off : Nat) (fit : off + 8 ≤ messageExtent) :
      ReadWord authority (s.regs.get .rsi + BitVec.ofNat 64 off) := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hit := caller_region_contains_offset (entryMessage s messageExtent) g.messageValid (off + i) (by
      change off + i < messageExtent
      omega)
    exact ⟨g.messageCanonical _ hit, g.messageRead _ hit⟩
  have fetchedFront (right : EntryFetchAuthority base s capacity authority) :
      LinkedExecution base authority s (entryFrontEvents base s capacity) checked := by
    let start := enteredFrame .entry s
    have startLive := (entered_frame_live .entry s).trans live
    have startDF := (entered_frame_direction .entry s).trans df
    have startPC : start.rip = routineAddress base entry + 0xe#64 := by rw [entered_frame_pc, pc]; rfl
    have saveWrite (i : Nat) (hi : i < 48) :
        canonical (savedBase s + BitVec.ofNat 64 i) = true ∧
        authority.writable (savedBase s + BitVec.ofNat 64 i) := by
      have hit := savedInside _ (caller_region_contains_offset saved savedValid i hi)
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have pro := run_range_observes (.inl rfl) entryLoaded right.entryText (prologue_decoded .entry)
      front.enter (frame_prologue_ready .entry base authority s pc live df right.entryExec saveWrite)
    have setupReady := entry_capacity_ready start startPC startLive startDF right.entryExec
      (by rw [entered_frame_register .entry s .rdx (by decide)]; exact scratchRead)
      (by rw [entered_frame_register .entry s .rsi (by decide)]; exact msgRead 16 (by omega))
    have setup := run_range_observes (.inl rfl) (pro.keeps_routine entry entryLoaded right.entryText)
      right.entryText entry_capacity_decoded front.arguments
      (by simpa only [entry_capacity_decoded, Option.getD_some] using setupReady)
    have setupEq := Option.some.inj (front.arguments.symm.trans (entry_capacity_setup start startLive))
    have setupPC : front.setup.rip = routineAddress base entry + 0x27#64 := by
      rw [setupEq]
      change start.rip + 25#64 = _
      rw [startPC, BitVec.add_assoc]
      rfl
    have setupLive : front.setup.ms = none := by rw [setupEq]; exact startLive
    have setupDF : front.setup.flags.df = false := by rw [setupEq]; exact startDF
    have entered := pro.append setup
    have guarded := runGuard_observes front.guard setupPC setupLive setupDF right.entryExec
      (entered.keeps_routine entry entryLoaded right.entryText) right.entryText
    have headEvents : rangeEvents (saveCode .entry) s =
        frameEnterEvents .entry (routineAddress base entry) (s.regs.get .rsp) := by
      rw [frame_prologue_events _ _ live, pc]
    have arguments := entry_capacity_events start startPC startLive
    rw [entered_frame_register .entry s .rdx (by decide), entered_frame_register .entry s .rsi (by decide)] at arguments
    simp only [entry_capacity_decoded, Option.getD_some, start] at arguments
    have setupCap : (front.setup.regs.get .rcx).toNat = capacity := by
      rw [setupEq, (capacity_state_registers start).1, entered_frame_register .entry s .rdx (by decide)]
      have kept : start.mem.readSize .q (s.regs.get .rdx) = s.mem.readSize .q (s.regs.get .rdx) := by
        apply Mem.readN_congr
        intro j hj
        exact frame_saved_outside .entry s _ (scratchOff j hj)
      rw [kept, size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cap64]
    rw [headEvents] at pro
    rw [arguments] at setup
    rw [setupPC, setupCap] at guarded
    exact (pro.append setup).append guarded
  have fetchedReturn (right : EntryFetchAuthority base s capacity authority) (before out : Cpu)
      (spAt : before.regs.get .rsp = sp - 120#64)
      (pcAt : before.rip = routineAddress base entry + 0x100#64)
      (running : before.ms = none) (forward : before.flags.df = false)
      (loaded : entry.Loaded (routineAddress base entry) before.mem.read)
      (leave : runRange entry 0x100 8 before = some out) :
      LinkedExecution base authority before
        (frameReturnEvents .entry (routineAddress base entry + 0x100#64) (s.regs.get .rsp - 120#64)) out := by
    have saveStart : before.regs.get .rsp + 72#64 = savedBase s := by
      rw [spAt, savedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.sub_eq_add_neg]
      rfl
    have readAll (j : Nat) (hj : j < 56) :
        canonical (before.regs.get .rsp + 72#64 + BitVec.ofNat 64 j) = true ∧
        authority.readable (before.regs.get .rsp + 72#64 + BitVec.ofNat 64 j) := by
      rw [saveStart]
      by_cases inSaves : j < 48
      · have hit := savedInside _ (caller_region_contains_offset saved savedValid j inSaves)
        exact ⟨g.stackCanonical _ hit, g.stackRead _ hit⟩
      · have back : savedBase s + BitVec.ofNat 64 j = sp + BitVec.ofNat 64 (j - 48) := by
          have sum : j = 48 + (j - 48) := by omega
          nth_rw 1 [sum]
          rw [BitVec.ofNat_add, ← BitVec.add_assoc]
          exact congrArg (· + BitVec.ofNat 64 (j - 48)) (BitVec.sub_add_cancel _ _)
        rw [back]
        exact right.returnRead _ (by omega)
    have executed := run_range_observes (.inl rfl) loaded right.entryText entry_return_decoded leave
      (frame_epilogue_ready .entry base authority before pcAt running forward right.entryExec readAll)
    have observed := frame_return_events .entry before running
    rw [pcAt, spAt] at observed
    simp only [HmacRoutine.locals, HmacRoutine.allocLength, sp] at observed
    rw [observed] at executed
    exact executed
  by_cases short : capacity < hmacScratchRequired message
  · have retWord : checked.mem.readSize .q sp = s.mem.readSize .q sp := by
      apply Mem.readN_congr
      intro i hi
      exact frontStack _ (outsideRet i hi)
    have savedWords (i : Fin 6) : checked.mem.readSize .q (savedBase s + BitVec.ofNat 64 (savedOffset i)) =
        s.regs.get (savedReg i) := by rw [front.memory]; exact frame_saved_word _ _ i
    obtain ⟨out, leave, stack, link, status, running, _, registers, memory⟩ :=
      entry_return_frame s checked front.live front.sp g.exitCanonical retWord savedWords
    refine ⟨out, ⟨⟨checked, checked, front, .short short, leave, ?_, ?_⟩⟩⟩
    · intro right
      have execution := fetchedFront right
      have endPC : checked.rip = routineAddress base entry + 0x100#64 := by
        rw [front.pc, if_pos (show capacity < 96 + message.bytes.size from short)]
      have returned := fetchedReturn right checked out front.sp endPC front.live (front.df.trans df)
        (execution.keeps_routine entry entryLoaded right.entryText) leave
      simpa only [entryNativeEvents, entryBodyEvents, if_pos short, List.append_nil] using execution.append returned
    · refine ⟨?_, running, stack, link, registers, ?_, ?_, ?_, ?_⟩
      · rw [status, front.status, hmacSha256_insufficient _ _ _ short]
        rfl
      · intro _ p h
        rw [memory]
        exact frontFrame p h
      · exact fun h => False.elim (Nat.not_le.mpr short h)
      · exact fun h => False.elim (Nat.not_le.mpr short h)
      · intro p h _ _
        rw [memory]
        exact frontStack p h
  have enough : hmacScratchRequired message ≤ capacity := Nat.le_of_not_gt short
  have room : 96 + message.bytes.size ≤ capacity := enough
  have keyPC : checked.rip = routineAddress base entry + 0x3a#64 := by
    rw [front.pc, if_neg (show ¬ capacity < 96 + message.bytes.size from short)]
  let keyCall := entryKeyCall checked
  obtain ⟨rdi, rsi, rsp, mem⟩ := entry_key_arguments checked
  have keyIn : keyCall.regs.get .rdi = s.regs.get .rdi := rdi.trans front.key
  have keyOut : keyCall.regs.get .rsi = block.base := rsi.trans (front.sp.trans blockBase.symm)
  have keySP : keyCall.regs.get .rsp = sp - 128#64 := by
    rw [rsp, front.sp, BitVec.sub_sub]
    rfl
  have keyTarget := entry_key_target base checked keyPC
  have keyRegister : checked.regs.get .rsp - 8#64 = push.base := rsp.symm.trans (keySP.trans pushBase.symm)
  have target : canonical (checked.rip + 710#64) = true := by
    change canonical keyCall.rip = true
    rw [keyTarget]
    simpa only [BitVec.add_zero] using g.key_pc_canonical 0 (by decide +kernel)
  have enterKey := entry_key_call checked front.live target
  have keyLink : keyCall.mem.readSize .q (keyCall.regs.get .rsp) = routineAddress base entry + 0x45#64 := by
    rw [mem, rsp, read64_write64, keyPC, BitVec.add_assoc]
    rfl
  have keyGrants := g.key_grants keyCall keyIn keyOut keySP
    (by rw [keyLink]; exact g.entry_pc_canonical 0x45 (by decide +kernel))
  have pushOutside (p : Val) (off : ¬ push.Contains p) : keyCall.mem.read p = checked.mem.read p := by
    rw [mem, keyRegister]
    exact store64_outside _ _ _ _ (caller_outside_delta _ (entry_slice_valid g 696 8 (by decide)) p off)
  have keyCallFrame (p : Val) (off : ¬ work.Contains p) : keyCall.mem.read p = s.mem.read p :=
    (pushOutside p (fun h => off (entry_slice_inside g 696 8 (by decide) p h))).trans (frontStack p off)
  have keyEncoding : EncodedByteList (byteView keyCall.mem) (keyCall.regs.get .rdi) input := by
    rw [keyIn]
    apply encodedKey.preserved keyLayout keyFits g.keyValid
    intro p h
    exact congrArg (fun b => some (none, b)) (keyCallFrame p (fun hit => g.stackKey p ⟨hit,h⟩))
  have shaCode : ImageLoaded (shaAddress base) keyCall.mem := by
    intro i hi
    have hit := caller_region_contains_offset _ g.shaValid i hi
    exact (keyCallFrame _ (fun p => g.stackSha _ ⟨p,hit⟩)).trans (shaLoaded i hi)
  have codeAtKey : key.Loaded (routineAddress base key) keyCall.mem.read := by
    intro i hi
    have hit := caller_region_contains_offset _ g.keyCodeValid i hi
    exact (keyCallFrame _ (fun p => g.stackKeyCode _ ⟨p,hit⟩)).trans (keyLoaded i hi)
  obtain ⟨afterKey, ⟨keyRan⟩⟩ := key_execution_from_caller base keyCall input keyExtent authority
    keyLayout keyFits keySize keyLength keyEncoding keyGrants keyTarget front.live (front.df.trans df)
    (g.sha_base_canonical) shaCode codeAtKey
  have afterKeySP : afterKey.regs.get .rsp = block.base := by
    rw [keyRan.sp, keySP, blockBase]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have afterKeyLive := keyRan.live
  have afterKeyDF : afterKey.flags.df = false := keyRan.direction.trans (front.df.trans df)
  have afterKeyPc : afterKey.rip = routineAddress base entry + 0x45#64 := keyRan.link.trans keyLink
  have messagePtr : afterKey.regs.get .rbp = s.regs.get .rsi := by
    have value : afterKey.regs.get .rbp = keyCall.regs.get .rbp := keyRan.saved ⟨1, by decide⟩
    have same : keyCall.regs.get .rbp = checked.regs.get .rbp := by
      simp (config := {decide := true}) [keyCall, entryKeyCall, Cpu.push, Cpu.setRip, Cpu.setReg,
        Cpu.writeMem, Regs.get_set_ne]
    exact value.trans (same.trans front.message)
  have scratchPtr : afterKey.regs.get .r12 = s.regs.get .rdx := by
    have value : afterKey.regs.get .r12 = keyCall.regs.get .r12 := keyRan.saved ⟨2, by decide⟩
    have same : keyCall.regs.get .r12 = checked.regs.get .r12 := by
      simp (config := {decide := true}) [keyCall, entryKeyCall, Cpu.push, Cpu.setRip, Cpu.setReg,
        Cpu.writeMem, Regs.get_set_ne]
    exact value.trans (same.trans front.scratch)
  have macPtr : afterKey.regs.get .r13 = s.regs.get .rcx := by
    have value : afterKey.regs.get .r13 = keyCall.regs.get .r13 := keyRan.saved ⟨3, by decide⟩
    have same : keyCall.regs.get .r13 = checked.regs.get .r13 := by
      simp (config := {decide := true}) [keyCall, entryKeyCall, Cpu.push, Cpu.setRip, Cpu.setReg,
        Cpu.writeMem, Regs.get_set_ne]
    exact value.trans (same.trans front.mac)
  have keyWork : keyWorkspace keyCall = regionSlice work 128 568 := by
    change (⟨keyCall.regs.get .rsp - 568#64, 568⟩ : Region) = regionSlice (entryWorkspace s) 128 568
    rw [keySP, BitVec.sub_sub, entry_slice s 128 568 (by decide)]
    rfl
  have keyArea : keyOutput keyCall = block := by
    change (⟨keyCall.regs.get .rsi, 64⟩ : Region) = ⟨block.base, 64⟩
    rw [keyOut]
  have afterKeyFrame (p : Val) (off : ¬ work.Contains p) : afterKey.mem.read p = s.mem.read p := by
    rw [keyRan.frame p (fun h => off (entry_slice_inside g 128 568 (by decide) p (by rwa [keyWork] at h)))
      (fun h => off (entry_slice_inside g 704 64 (by decide) p (by rwa [keyArea] at h)))]
    exact keyCallFrame p off
  have msg : EncodedByteList (byteView afterKey.mem) (afterKey.regs.get .rbp) message := by
    rw [messagePtr]
    apply encodedMessage.preserved messageLayout messageFits g.messageValid
    intro p h
    exact congrArg (fun b => some (none, b)) (afterKeyFrame p (fun hit => g.stackMessage p ⟨hit,h⟩))
  have cap : afterKey.mem.readSize .q (afterKey.regs.get .r12) = BitVec.ofNat 64 capacity := by
    rw [scratchPtr, ← size]
    apply Mem.readN_congr
    intro i hi
    change i < 8 at hi
    exact afterKeyFrame _ (fun h => g.stackScratch _ ⟨h,
      caller_region_contains_offset _ g.scratchValid i (by change i < capacity; omega)⟩)
  have entryCode : entry.Loaded (routineAddress base entry) afterKey.mem.read := by
    intro i hi
    have hit := caller_region_contains_offset _ g.entryCodeValid i hi
    exact (afterKeyFrame _ (fun h => g.stackEntryCode _ ⟨h,hit⟩)).trans (entryLoaded i hi)
  have blockValid : block.Valid := entry_slice_valid g 704 64 (by decide)
  have blockInside (p : Val) (h : block.Contains p) : work.Contains p := entry_slice_inside g 704 64 (by decide) p h
  have messageShaped : (⟨afterKey.regs.get .rbp, messageExtent⟩ : Region) = entryMessage s messageExtent := by
    rw [messagePtr]
    rfl
  have scratchShaped : (⟨afterKey.regs.get .r12, capacity⟩ : Region) = entryScratch s capacity := by
    rw [scratchPtr]
    rfl
  have blockShaped : (⟨afterKey.regs.get .rsp, 64⟩ : Region) = block := by
    rw [afterKeySP]
    rfl
  obtain ⟨header, padded, copier, prepared, headerRun, padRun, setup, copy, preparedPC, preparedLive, preparedDF,
    preparedSP, preparedScratch, preparedMAC, innerValue, preparedFrame, innerFacts⟩ :=
    entry_inner_list (routineAddress base entry) afterKey message k0 capacity messageExtent
      messageLayout messageFits msg cap room cap64 (by rw [scratchShaped]; exact g.scratchValid)
      (by rw [messageShaped]; exact g.messageValid) (by rw [blockShaped]; exact blockValid) g.entryCodeValid
      (by rw [scratchShaped,messageShaped]; exact g.scratchMessage)
      (by rw [scratchShaped,blockShaped]; exact fun p h => g.stackScratch p ⟨blockInside p h.2,h.1⟩)
      (by rw [scratchShaped]; exact g.scratchEntryCode)
      (by rw [afterKeySP, ← keyOut]; exact keyRan.bytes)
      entryCode afterKeyPc (g.entry_pc_canonical 0xe9 (by decide +kernel)) afterKeyLive afterKeyDF
  have prepKeep (p : Val) (off : ¬ changed.Contains p) : prepared.mem.read p = afterKey.mem.read p := by
    apply preparedFrame
    rw [scratchPtr]
    exact off
  let fin := entryFinishCall prepared
  obtain ⟨finRdi, finRsi, finRdx, finRsp, finMem⟩ := entry_finish_arguments prepared
  have finSrc : fin.regs.get .rdi = s.regs.get .rdx + 8#64 :=
    finRdi.trans (congrArg (· + 8#64) (preparedScratch.trans scratchPtr))
  have finBlock : fin.regs.get .rsi = block.base := finRsi.trans (preparedSP.trans afterKeySP)
  have finMac : fin.regs.get .rdx = s.regs.get .rcx := finRdx.trans (preparedMAC.trans macPtr)
  have finSP : fin.regs.get .rsp = sp - 128#64 := by
    rw [finRsp, preparedSP, afterKeySP, blockBase, BitVec.sub_sub]
    rfl
  have finPC := entry_finish_target base prepared preparedPC
  have finLink : fin.mem.readSize .q (fin.regs.get .rsp) = routineAddress base entry + 0xfb#64 := by
    rw [finMem, finRsp, read64_write64, preparedPC, BitVec.add_assoc]
    rfl
  have finCall := entry_finish_call prepared preparedLive
    (by change canonical fin.rip = true; rw [finPC]; exact g.finishCanonical)
  have finGrants := g.finish_grants fin minCap finSrc finBlock finMac finSP
    (by rw [finLink]; exact g.entry_pc_canonical 0xfb (by decide +kernel))
  have finPush (p : Val) (off : ¬ push.Contains p) : fin.mem.read p = prepared.mem.read p := by
    rw [finMem, ← finRsp, finSP, ← pushBase]
    exact store64_outside _ _ _ _ (caller_outside_delta _ (entry_slice_valid g 696 8 (by decide)) p off)
  let inner := hmacInner message k0 capacity
  have innerLayout := hmacInner_layout message k0 capacity enough
  have innerFit : inner.size ≤ capacity - 8 := Nat.le_refl _
  have innerRegion : finishInput fin (capacity - 8) = regionSlice (entryScratch s capacity) 8 (capacity - 8) := by
    simp [finishInput, finSrc, regionSlice, entryScratch]
  have encoded : EncodedByteList (byteView fin.mem) (fin.regs.get .rdi) inner := by
    have old : EncodedByteList (byteView prepared.mem) (fin.regs.get .rdi) inner := by
      rw [finSrc, ← scratchPtr]
      exact innerValue
    apply old.preserved innerLayout innerFit finGrants.inputValid
    intro p h
    have hInside : (entryScratch s capacity).Contains p := by
      change (finishInput fin (capacity - 8)).Contains p at h
      rw [innerRegion] at h
      exact regionSlice_inside _ _ _ g.scratchValid (by change 8 + (capacity - 8) ≤ capacity; omega) p h
    exact congrArg (fun b => some (none, b)) (finPush p
      (fun hit => g.stackScratch p ⟨entry_slice_inside g 696 8 (by decide) p hit, hInside⟩))
  have keyAt (i : Fin 64) : fin.mem.read (fin.regs.get .rsi + BitVec.ofNat 64 i.val) = k0[i.val].toBitVec := by
    rw [finBlock]
    let p := block.base + BitVec.ofNat 64 i.val
    have hit := caller_region_contains_offset block blockValid i.val i.isLt
    have offPush : ¬ push.Contains p := fun h =>
      entry_slice_disjoint g 696 8 704 64 (by decide) (by decide) p ⟨h,hit⟩
    rw [finPush p offPush, prepKeep p (fun h => g.stackScratch p ⟨blockInside p hit,inScratch p room h⟩)]
    change afterKey.mem.read (block.base + BitVec.ofNat 64 i.val) = _
    rw [← keyOut]
    exact keyRan.bytes i
  have finalSha : ImageLoaded (shaAddress base) fin.mem := by
    intro i hi
    let p := shaAddress base + BitVec.ofNat 64 i
    have hit := caller_region_contains_offset _ g.shaValid i hi
    rw [finPush p (fun h => g.stackSha p ⟨entry_slice_inside g 696 8 (by decide) p h,hit⟩),
      prepKeep p (fun h => g.scratchSha p ⟨inScratch p room h,hit⟩),
      afterKeyFrame p (fun h => g.stackSha p ⟨h,hit⟩)]
    exact shaLoaded i hi
  obtain ⟨afterFin, ⟨finished⟩⟩ := finish_execution_from_caller base fin inner k0 (capacity - 8) authority
    innerLayout innerFit (by change capacity - 8 < 2 ^ 64; omega)
    (hmacInner_sha256_length _ _ _ messageLength) encoded keyAt finGrants finPC preparedLive
    g.sha_base_canonical finalSha
  let done := successState afterFin
  have doneSp : done.regs.get .rsp = sp - 120#64 := by
    simp (config := {decide := true}) only [done, successState, Regs.get_set_ne, finished.sp, finSP,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have finWork : finishWorkspace fin = regionSlice work 0 696 := by
    change (⟨fin.regs.get .rsp - 696#64, 696⟩ : Region) = regionSlice (entryWorkspace s) 0 696
    rw [finSP, BitVec.sub_sub, entry_slice s 0 696 (by decide)]
    rfl
  have finOut : finishMac fin = entryMac s := by simp only [finishMac, entryMac, finMac]
  have afterFinFrame (p : Val) (offStack : ¬ work.Contains p) (offScratch : ¬ changed.Contains p)
      (offMac : ¬ (entryMac s).Contains p) : afterFin.mem.read p = s.mem.read p := by
    rw [finished.frame p (fun h => offStack (entry_slice_inside g 0 696 (by decide) p (by rwa [finWork] at h)))
      (by rwa [finOut]), finPush p (fun h => offStack (entry_slice_inside g 696 8 (by decide) p h)),
      prepKeep p offScratch]
    exact afterKeyFrame p offStack
  have exitAddress : done.mem.readSize .q sp = s.mem.readSize .q sp := by
    apply Mem.readN_congr
    intro i hi
    let p := sp + BitVec.ofNat 64 i
    have h := caller_region_contains_offset _ g.returnValid i hi
    exact afterFinFrame p (outsideRet i hi) (fun e => g.returnScratch p ⟨h,inScratch p room e⟩)
      (fun e => g.returnMac p ⟨h,e⟩)
  have restoreSaved (i : Fin 6) : done.mem.readSize .q (savedBase s + BitVec.ofNat 64 (savedOffset i)) =
      s.regs.get (savedReg i) := by
    refine (Mem.readN_congr _ _ _ 8 ?_).trans (frame_saved_word .entry s i)
    intro j hj
    let p := savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j
    have hit : saved.Contains p := by
      change saved.Contains (savedBase s + BitVec.ofNat 64 (savedOffset i) + BitVec.ofNat 64 j)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact caller_region_contains_offset saved savedValid _ (by
        change savedOffset i + j < 48
        have := i.isLt
        unfold savedOffset
        omega)
    have h := hit
    rw [savedRegion] at h
    have noAlias (off n : Nat) (ordered : off + n ≤ 776) : ¬ (regionSlice work off n).Contains p :=
      fun e => entry_slice_disjoint g off n 776 48 ordered (by decide) p ⟨e,h⟩
    have noW : ¬ changed.Contains p := fun e => g.stackScratch p ⟨savedInside p hit,inScratch p room e⟩
    have noMac : ¬ (entryMac s).Contains p := fun e => g.stackMac p ⟨savedInside p hit,e⟩
    change afterFin.mem.read p = _
    rw [finished.frame p (by rw [finWork]; exact noAlias 0 696 (by decide)) (by rwa [finOut]),
      finPush p (noAlias 696 8 (by decide)), prepKeep p noW,
      keyRan.frame p (by rw [keyWork]; exact noAlias 128 568 (by decide))
        (by rw [keyArea]; exact noAlias 704 64 (by decide)),
      pushOutside p (noAlias 696 8 (by decide)), front.memory]
  obtain ⟨out, leave, stack, link, success, running, _, registers, outMemory⟩ :=
    entry_return_frame s done finished.live doneSp g.exitCanonical exitAddress restoreSaved
  have fetched (right : EntryFetchAuthority base s capacity authority) :
      LinkedExecution base authority s (entryNativeEvents base s input message capacity) out := by
    have pushAccess (i : Nat) (hi : i < 8) :
        canonical (push.base + BitVec.ofNat 64 i) = true ∧
        authority.writable (push.base + BitVec.ofNat 64 i) := by
      have hit := stackAt 696 8 (by decide) i hi
      exact ⟨g.stackCanonical _ hit, g.stackWrite _ hit⟩
    have returnSlot (i : Nat) (hi : i < 8) :
        canonical (push.base + BitVec.ofNat 64 i) = true ∧
        authority.readable (push.base + BitVec.ofNat 64 i) := by
      have hit := stackAt 696 8 (by decide) i hi
      exact ⟨g.stackCanonical _ hit, g.stackRead _ hit⟩
    have previous := fetchedFront right
    have keySent := run_range_observes (.inl rfl) (previous.keeps_routine entry entryLoaded right.entryText)
      right.entryText entry_key_call_decoded enterKey (by
        have allowed := entry_key_setup_ready checked keyPC front.live (front.df.trans df) right.entryExec
          (by rw [keyRegister]; exact pushAccess)
        simpa only [entry_key_call_decoded, Option.getD_some] using allowed)
    have keyed := keyRan.native ⟨right.keyExec, right.keyText, by rw [keySP, ← pushBase]; exact returnSlot⟩
    have throughKey := previous.append (keySent.append keyed)
    have scratchWrite (off : Nat) (j : Nat) (fits : off + j < capacity) :
        canonical (s.regs.get .rdx + BitVec.ofNat 64 off + BitVec.ofNat 64 j) = true ∧
        authority.writable (s.regs.get .rdx + BitVec.ofNat 64 off + BitVec.ofNat 64 j) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hit := caller_region_contains_offset (entryScratch s capacity) g.scratchValid (off + j) fits
      exact ⟨g.scratchCanonical _ hit, right.scratchWrite _ hit⟩
    have headerReady := entry_header_ready afterKey afterKeyPc afterKeyLive afterKeyDF right.entryExec
      (by rw [scratchPtr]; exact scratchRead) (by rw [messagePtr]; exact msgRead 16 (by omega))
      (by rw [scratchPtr]; exact fun j hj => scratchWrite 8 j (by omega))
      (by rw [scratchPtr]; exact fun j hj => scratchWrite 16 j (by omega))
      (by rw [scratchPtr]; exact fun j hj => scratchWrite 24 j (by omega))
    have headers := run_range_observes (.inl rfl) entryCode right.entryText inner_header_decoded headerRun
      (by simpa only [inner_header_decoded, Option.getD_some] using headerReady)
    have padRead (i : Nat) (hi : i < 64) :
        canonical (header.regs.get (sourceReg false) + BitVec.ofNat 64 i) = true ∧
        authority.readable (header.regs.get (sourceReg false) + BitVec.ofNat 64 i) := by
      change canonical (header.regs.get .rsp + BitVec.ofNat 64 i) = true ∧
        authority.readable (header.regs.get .rsp + BitVec.ofNat 64 i)
      rw [innerFacts.padKey, afterKeySP]
      have hit := stackAt 704 64 (by decide) i hi
      exact ⟨g.stackCanonical _ hit, g.stackRead _ hit⟩
    have padWrite (i : Nat) (hi : i < 64) :
        canonical (padDestination header false + BitVec.ofNat 64 i) = true ∧
        authority.writable (padDestination header false + BitVec.ofNat 64 i) := by
      rw [innerFacts.padDest, scratchPtr]
      exact scratchWrite 32 i (by omega)
    have pads := run_range_observes (.inl rfl) (headers.keeps_routine entry entryCode right.entryText)
      right.entryText entry_pad_decoded padRun (pad_range_ready false base header authority
        innerFacts.headerLive innerFacts.headerDF innerFacts.padApart innerFacts.headerPC
        right.entryExec padRead padWrite)
    have throughPad := headers.append pads
    have readyCopy := entry_copy_setup_ready padded innerFacts.paddedPC innerFacts.paddedLive innerFacts.paddedDF
      right.entryExec (by rw [innerFacts.paddedMessage, messagePtr]; exact msgRead 8 (by omega))
      (by rw [innerFacts.paddedMessage, messagePtr]; exact msgRead 16 (by omega))
    have copying := run_range_observes (.inl rfl) (throughPad.keeps_routine entry entryCode right.entryText)
      right.entryText copy_setup_decoded setup (by simpa only [copy_setup_decoded, Option.getD_some] using readyCopy)
    have throughCopy := throughPad.append copying
    have copyRead (j : Nat) (hj : j < message.bytes.size) :
        canonical (copier.regs.get .rsi + BitVec.ofNat 64 j) = true ∧
        authority.readable (copier.regs.get .rsi + BitVec.ofNat 64 j) := by
      rw [innerFacts.copySource, messagePtr, BitVec.add_assoc, ← BitVec.ofNat_add]
      have hit := caller_region_contains_offset (entryMessage s messageExtent) g.messageValid (message.offset + j) (by
        change message.offset + j < messageExtent
        have := messageLayout.2.2.1
        have := messageLayout.2.2.2
        omega)
      exact ⟨g.messageCanonical _ hit, g.messageRead _ hit⟩
    have copyWrite (j : Nat) (hj : j < message.bytes.size) :
        canonical (copier.regs.get .rdi + BitVec.ofNat 64 j) = true ∧
        authority.writable (copier.regs.get .rdi + BitVec.ofNat 64 j) := by
      rw [innerFacts.copyDest, scratchPtr]
      exact scratchWrite 96 j (by omega)
    have copied := copy_fetched_observes (r := entry) (off := 0xe9) copier (.inl rfl) repeat_decoded.1
      ⟨by decide, by decide +kernel⟩ innerFacts.copyPC
      (throughCopy.keeps_routine entry entryCode right.entryText) right.entryText
      (by rw [innerFacts.copyPC]; exact fetch_rights right.entryExec (by decide +kernel : 0xe9 + 2 ≤ entry.image.size))
      innerFacts.copyLive innerFacts.copyDF innerFacts.copyCount (by omega) innerFacts.copyApart copyRead copyWrite
    rw [innerFacts.copyResult] at copied
    have assembled := throughKey.append (throughCopy.append copied)
    have slot : prepared.regs.get .rsp - 8#64 = push.base := finRsp.symm.trans (finSP.trans pushBase.symm)
    have readyFinish := entry_finish_setup_ready prepared preparedPC preparedLive preparedDF right.entryExec
      (by rw [slot]; exact pushAccess)
    have enteredFinish := run_range_observes (.inl rfl)
      (assembled.keeps_routine entry entryLoaded right.entryText) right.entryText
      entry_finish_call_decoded finCall (by simpa only [entry_finish_call_decoded, Option.getD_some] using readyFinish)
    have untilFinish := assembled.append enteredFinish
    obtain ⟨hashed, finishDF⟩ := finished.native ⟨
      untilFinish.keeps_routine finish right.finishLoaded right.finishText, right.finishExec, right.finishText,
      preparedDF, by rw [finSP, ← pushBase]; exact returnSlot⟩
    have throughFinish := untilFinish.append hashed
    have retPC : afterFin.rip = routineAddress base entry + 0xfb#64 := finished.link.trans finLink
    have status := run_range_observes (.inl rfl) (throughFinish.keeps_routine entry entryLoaded right.entryText)
      right.entryText zero_status_decoded (entry_set_success afterFin finished.live)
      (entry_status_ready afterFin retPC finished.live finishDF right.entryExec)
    have donePC : done.rip = routineAddress base entry + 0x100#64 := by
      change afterFin.rip + 5#64 = _
      rw [retPC, BitVec.add_assoc]
      rfl
    have complete := throughFinish.append status
    have returned := fetchedReturn right done out doneSp donePC finished.live finishDF
      (complete.keeps_routine entry entryLoaded right.entryText) leave
    have keySetup := entry_key_setup_events checked keyPC front.live
    rw [front.sp] at keySetup
    have headerEvents := entry_header_events afterKey afterKeyPc afterKeyLive
    rw [scratchPtr, messagePtr] at headerEvents
    have padEvents := (pad_code_facts false 8 header innerFacts.headerLive innerFacts.headerDF
      (by decide) innerFacts.padApart).2.2
    change _ = x86PadEvents false header.rip (header.regs.get .rsp) (header.regs.get .r12) 8 at padEvents
    have padScratch : header.regs.get .r12 = afterKey.regs.get .r12 := by
      have eq := Option.some.inj (headerRun.symm.trans (entry_inner_header afterKey afterKeyLive))
      rw [eq]
      simp (config := {decide := true}) [innerHeaderState, Regs.get_set_ne]
    rw [innerFacts.headerPC, innerFacts.padKey, afterKeySP, blockBase, padScratch, scratchPtr] at padEvents
    have copySetup := entry_copy_setup_events padded innerFacts.paddedPC innerFacts.paddedLive
    rw [innerFacts.paddedMessage, messagePtr] at copySetup
    have finishSetup := entry_finish_setup_events prepared preparedPC preparedLive
    rw [preparedSP, afterKeySP, blockBase] at finishSetup
    have statusEvents := entry_status_events afterFin retPC
    simp only [entry_key_call_decoded, inner_header_decoded, copy_setup_decoded,
      entry_finish_call_decoded, Option.getD_some, sp] at keySetup headerEvents padEvents copySetup finishSetup
    have keyEvents : keyNativeEvents base keyCall input = keyNativeEvents base (entryKeyContext s) input := by
      obtain ⟨targetSP, targetIn, targetOut⟩ :=
        sha_trace_context s (s.regs.get .rsp - 128#64) (s.regs.get .rdi) (s.regs.get .rsp - 120#64)
      exact key_native_events_equal ⟨keySP.trans targetSP.symm, keyIn.trans targetIn.symm,
        keyOut.trans (blockBase.trans targetOut.symm), rfl, rfl⟩
    have finishEvents : finishNativeEvents base fin inner k0 = finishNativeEvents base (entryFinishContext s) inner k0 := by
      obtain ⟨targetSP, targetIn, targetKey, targetOut⟩ := entry_finish_context_arguments s
      exact finish_native_events_equal ⟨finSP.trans targetSP.symm, finSrc.trans targetIn.symm,
        finBlock.trans (blockBase.trans targetKey.symm), finMac.trans targetOut.symm, rfl, rfl⟩
    rw [keySetup] at keySent
    rw [keyEvents] at keyed
    rw [headerEvents] at headers
    rw [padEvents] at pads
    rw [copySetup] at copying
    rw [innerFacts.copyPC, innerFacts.copySource, innerFacts.copyDest, messagePtr, scratchPtr] at copied
    rw [finishSetup] at enteredFinish
    rw [finishEvents] at hashed
    rw [statusEvents] at status
    rw [entryNativeEvents, entryBodyEvents, if_neg short]
    have keyBlock := keySent.append keyed
    have innerList := ((((keyBlock.append headers).append pads).append copying).append copied)
    have result := ((innerList.append enteredFinish).append hashed).append status
    exact (previous.append result).append returned
  refine ⟨out, ⟨⟨checked, done, front, .full enterKey keyRan headerRun padRun setup copy finCall
    finished (entry_set_success afterFin finished.live), leave, fetched, ?_⟩⟩⟩
  refine ⟨?_, running, stack, link, registers, ?_, ?_, ?_, ?_⟩
  · rw [success, hmacSha256, if_neg short]
    simp [done, successState, HmacResult.status, Regs.get_set_same]
  · exact fun h => False.elim (short h)
  · intro _
    rw [outMemory, show done.mem = afterFin.mem from rfl, ← finMac, finished.digest, hmacFinish_hmacInner]
  · intro _
    rw [outMemory, show done.mem = afterFin.mem from rfl, ← finSrc]
    apply encoded.preserved innerLayout innerFit finGrants.inputValid
    intro p h
    exact congrArg (fun b => some (none, b)) (finished.frame p (fun e => finGrants.stackInput p ⟨e,h⟩)
      (fun e => finGrants.macInput p ⟨e,h⟩))
  · intro p sw sc mac
    rw [outMemory]
    exact afterFinFrame p sw sc mac

structure EntryPublic (s t : Cpu) (keyA keyB messageA messageB : ByteList) : Prop where
  stack : s.regs.get .rsp = t.regs.get .rsp
  key : s.regs.get .rdi = t.regs.get .rdi
  message : s.regs.get .rsi = t.regs.get .rsi
  scratch : s.regs.get .rdx = t.regs.get .rdx
  output : s.regs.get .rcx = t.regs.get .rcx
  keyOffset : keyA.offset = keyB.offset
  keyCount : keyA.bytes.size = keyB.bytes.size
  messageOffset : messageA.offset = messageB.offset
  messageCount : messageA.bytes.size = messageB.bytes.size

theorem entry_native_events_equal {base : Val} {s t : Cpu} {keyA keyB messageA messageB : ByteList}
    {capacity : Nat} (same : EntryPublic s t keyA keyB messageA messageB) :
    entryNativeEvents base s keyA messageA capacity = entryNativeEvents base t keyB messageB capacity := by
  have keys : keyNativeEvents base (entryKeyContext s) keyA = keyNativeEvents base (entryKeyContext t) keyB := by
    obtain ⟨spS, inS, outS⟩ := sha_trace_context s (s.regs.get .rsp - 128#64) (s.regs.get .rdi) (s.regs.get .rsp - 120#64)
    obtain ⟨spT, inT, outT⟩ := sha_trace_context t (t.regs.get .rsp - 128#64) (t.regs.get .rdi) (t.regs.get .rsp - 120#64)
    exact key_native_events_equal ⟨spS.trans ((congrArg (· - 128#64) same.stack).trans spT.symm),
      inS.trans (same.key.trans inT.symm), outS.trans ((congrArg (· - 120#64) same.stack).trans outT.symm),
      same.keyOffset, same.keyCount⟩
  have finishes : finishNativeEvents base (entryFinishContext s) (hmacInner messageA (hmacKey keyA) capacity) (hmacKey keyA) =
      finishNativeEvents base (entryFinishContext t) (hmacInner messageB (hmacKey keyB) capacity) (hmacKey keyB) := by
    obtain ⟨spS, inS, keyS, outS⟩ := entry_finish_context_arguments s
    obtain ⟨spT, inT, keyT, outT⟩ := entry_finish_context_arguments t
    exact finish_native_events_equal ⟨spS.trans ((congrArg (· - 128#64) same.stack).trans spT.symm),
      inS.trans ((congrArg (· + 8#64) same.scratch).trans inT.symm),
      keyS.trans ((congrArg (· - 120#64) same.stack).trans keyT.symm),
      outS.trans (same.output.trans outT.symm), rfl, by simp only [hmacInner_length, same.messageCount]⟩
  simp only [entryNativeEvents, entryFrontEvents, entryBodyEvents, keys, finishes, hmacScratchRequired,
    same.stack, same.message, same.scratch, same.messageOffset, same.messageCount]

end Crypto.HMACSHA256.X86_64
