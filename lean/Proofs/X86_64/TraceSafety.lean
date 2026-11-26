import Proofs.X86_64.Execution
import Proofs.X86_64.Interleaving

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset lengthOffset paddingBlockCount)

def DataWithin (read write : Val → Prop) (trace : List Event) : Prop :=
  ∀ event ∈ trace, ∀ access ∈ event.2.2, ∀ p, DataByte access p →
    if access.write then write p else read p

theorem DataWithin.append {read write : Val → Prop} {x y : List Event}
    (left : DataWithin read write x) (right : DataWithin read write y) : DataWithin read write (x++y) := by
  intro e member
  rcases List.mem_append.mp member with h | h
  · exact left e h
  · exact right e h

theorem DataWithin.mono {read read' write write' : Val → Prop} {trace : List Event}
    (bound : DataWithin read write trace) (r : ∀ p, read p → read' p) (w : ∀ p, write p → write' p) :
    DataWithin read' write' trace := by
  intro e he a ha p touched
  have original := bound e he a ha p touched
  cases direction : a.write <;> simp only [direction, Bool.false_eq_true, ↓reduceIte] at original ⊢
  · exact r p original
  · exact w p original

private theorem empty_within {read write : Val → Prop} : DataWithin read write [] := by
  simp [DataWithin]

private theorem byte_range {a : DataAccess} {p : Val} {base : Val} {offset count : Nat}
    (fits : offset + a.bytes ≤ count) (addr : a.address = base + BitVec.ofNat 64 offset)
    (touched : DataByte a p) (valid : (Region.mk base count).Valid) :
    (Region.mk base count).Contains p := by
  obtain ⟨j,hj,rfl⟩ := touched
  rw [addr,BitVec.add_assoc,← BitVec.ofNat_add]
  exact caller_region_contains_offset _ valid _ (by change offset+j < count; omega)

private def frameFits (size : Nat) (code : List Instr) : Bool :=
  code.all fun i => ((accessForms i).getD []).all fun access =>
    decide (access.ea.disp.toNat + access.bytes ≤ size)

private theorem frame_within (sp pc : Val) (size : Nat) (code : List Instr)
    (valid : (Region.mk sp size).Valid) (fits : frameFits size code = true) :
    DataWithin (Region.mk sp size).Contains (Region.mk sp size).Contains (frameEvents sp pc code) := by
  induction code generalizing pc with
  | nil => exact empty_within
  | cons i code ih =>
    obtain ⟨first,tail⟩ := Bool.and_eq_true_iff.mp fits
    intro e member a ha p touched
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨form,present,rfl⟩ := List.mem_map.mp ha
      have range := of_decide_eq_true (List.all_eq_true.mp first _ present)
      have inside := byte_range range (by simp) touched valid
      split <;> exact inside
    · exact ih _ tail e later a ha p touched

def frameFragmentFits (off count size : Nat) : Bool :=
  frameFits size ((decodeSeq off count).getD [])

theorem frame_fragment_within (base sp : Val) (off count size : Nat)
    (valid : (Region.mk sp size).Valid) (fits : frameFragmentFits off count size = true) :
    DataWithin (Region.mk sp size).Contains (Region.mk sp size).Contains (frameFragment base sp off count) :=
  frame_within _ _ _ _ valid fits

private theorem fetch_in_image (e : Event) (base : Val) (s out : Cpu) (trace : List Event)
    (run : ObservedExecution base s trace out) (valid : (imageRegion base).Valid)
    (member : e ∈ trace) (p : Val) (touched : DataByte ⟨false,e.1,e.2.1.len⟩ p) :
    (imageRegion base).Contains p := by
  induction run with
  | nil => simp at member
  | cons fetched executed observed rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨offset,pc,extent⟩ := fetched_extent fetched
      have code : codeEnd ≤ image.size := by decide +kernel
      exact byte_range (Nat.le_trans extent code) pc touched valid
    · exact ih later

def callBorrow (base : Val) (s : Cpu) (extent : Nat) : BorrowScope where
  shared p := (inputRegion s extent).Contains p ∨ (imageRegion base).Contains p ∨
    (Region.mk (s.regs.get .rsp) 8).Contains p
  exclusive p := (outputRegion s).Contains p ∨ (Region.mk (frameBase s) 504).Contains p

def headerRegion (s : Cpu) : Region := ⟨s.regs.get .rdi,24⟩

def payloadRegion (s : Cpu) (message : Crypto.Reference.ByteList) : Region :=
  ⟨s.regs.get .rdi+BitVec.ofNat 64 message.offset,message.bytes.size⟩

def callRead (base : Val) (s : Cpu) (message : Crypto.Reference.ByteList) (extent : Nat) (p : Val) : Prop :=
  ((inputRegion s extent).Contains p ∧ ((headerRegion s).Contains p ∨ (payloadRegion s message).Contains p)) ∨
  (imageRegion base).Contains p ∨ (Region.mk (s.regs.get .rsp) 8).Contains p ∨
  (Region.mk (frameBase s) 504).Contains p

theorem callRead_protected {base s message extent p} (inside : callRead base s message extent p) :
    (callBorrow base s extent).protected p := by
  rcases inside with ⟨full,_⟩|image|ret|stack
  · exact Or.inl (Or.inl full)
  · exact Or.inl (Or.inr (Or.inl image))
  · exact Or.inl (Or.inr (Or.inr ret))
  · exact Or.inr (Or.inr stack)

theorem observed_call_access {base s out trace} (run : ObservedExecution base s trace out)
    (extent : Nat) (imageValid : (imageRegion base).Valid)
    (bounds : DataWithin (callBorrow base s extent).protected (callBorrow base s extent).exclusive trace) :
    ∀ e ∈ trace, CallAccess (callBorrow base s extent) (ReportedAccess e.1 e.2.1 e.2.2) := by
  intro e member
  refine ⟨?_,?_,fun _ => id,fun _ => id⟩
  · intro p h
    rcases h with fetch | ⟨a,ha,direction,touched⟩
    · exact Or.inl (Or.inr (Or.inl (fetch_in_image e base s out trace run imageValid member p fetch)))
    · simpa only [direction, Bool.false_eq_true, if_false] using bounds e member a ha p touched
  · rintro p ⟨a,ha,direction,touched⟩
    simpa only [direction, if_true] using bounds e member a ha p touched

end Crypto.X86_64

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset lengthOffset paddingBlockCount)

private def wordWindow (sp ptr k : Val) (r : GPR) : Region :=
  ⟨if r = .rsp then sp else if r = .rbp then ptr else k, tableBytes r⟩

private theorem words_within (loop : WordLoop) (base sp ptr k : Val) (n : Nat)
    (legal : loop.initialIndex + n < loop.limit.toNat)
    {read write : Val → Prop}
    (schedule : (Region.mk sp 256).Valid)
    (source : (Region.mk ptr 64).Valid) (constants : (Region.mk k 256).Valid)
    (readStack : ∀ p, (Region.mk sp 256).Contains p → read p)
    (writeStack : ∀ p, (Region.mk sp 256).Contains p → write p)
    (readInput : ∀ p, (Region.mk ptr 64).Contains p → read p)
    (readK : ∀ p, (Region.mk k 256).Contains p → read p) :
    DataWithin read write (loop.iteration base sp ptr k (loop.initialIndex + n)) := by
  intro e member a ha p hp
  rw [WordLoop.iteration] at member
  rcases List.mem_append.mp member with body | latch
  · let s := loop.withInputs base sp ptr k (loop.initialIndex+n)
    obtain ⟨word,seen,rfl⟩ := word_event_access _ s e body a ha
    have index : s.regs.get .rbx = BitVec.ofNat 64 (loop.initialIndex+n) := by simp [s,WordLoop.withInputs]
    have windows := compression_word_bounds s (by rfl) e.1 word
    have authorized : InWordWindow s word := by
      cases loop with
      | input =>
        change 0+n < 16 at legal
        exact windows.1 ⟨n,by omega⟩ (by simpa only [WordLoop.initialIndex,Nat.zero_add] using index) seen
      | expansion =>
        change 16+n < 64 at legal
        exact windows.2.1 ⟨n,by omega⟩ index seen
      | round =>
        change 0+n < 64 at legal
        exact windows.2.2 ⟨n,by omega⟩ (by simpa only [WordLoop.initialIndex,Nat.zero_add] using index) seen
    obtain ⟨r,offset,fits,loc,onlyStack⟩ := authorized
    have classify : r = .rsp ∨ r = .rbp ∨ r = .rdi := by
      cases r <;> simp_all [tableBytes]
    have bound : (wordWindow sp ptr k r).Valid := by
      rcases classify with rfl|rfl|rfl <;> first | exact schedule | exact source | exact constants
    have address : word.address = (wordWindow sp ptr k r).base + BitVec.ofNat 64 offset := by
      rw [loc]
      rcases classify with rfl|rfl|rfl <;>
        simp (config := {decide := true}) [s, WordLoop.withInputs, wordWindow, Regs.get_set_ne]
    have inside : (wordWindow sp ptr k r).Contains p :=
      byte_range fits address hp bound
    by_cases writing : word.write = true
    · have eq := onlyStack writing
      subst r
      simpa only [writing,if_true] using writeStack p inside
    · have readable : read p := by
        rcases classify with rfl|rfl|rfl
        · exact readStack p inside
        · exact readInput p inside
        · exact readK p inside
      simpa only [writing,if_false] using readable
  · simp only [latchEvents,List.mem_cons,List.not_mem_nil,or_false] at latch
    rcases latch with rfl|rfl|rfl <;> simp at ha

private theorem word_loop_within (loop : WordLoop) (base sp ptr k : Val) (n : Nat)
    (legal : loop.initialIndex+n ≤ loop.limit.toNat)
    {read write : Val → Prop}
    (schedule : (Region.mk sp 256).Valid)
    (source : (Region.mk ptr 64).Valid) (constants : (Region.mk k 256).Valid)
    (readStack : ∀ p, (Region.mk sp 256).Contains p → read p)
    (writeStack : ∀ p, (Region.mk sp 256).Contains p → write p)
    (readInput : ∀ p, (Region.mk ptr 64).Contains p → read p)
    (readK : ∀ p, (Region.mk k 256).Contains p → read p) :
    DataWithin read write (loop.prefix base sp ptr k n) := by
  induction n with
  | zero => exact empty_within
  | succ n ih =>
    exact (ih (by omega)).append (words_within loop base sp ptr k n (by omega)
      schedule source constants readStack writeStack readInput readK)

private theorem subregion_valid {base : Val} {outer size : Nat}
    (valid : (Region.mk base outer).Valid) (sizeFits : size ≤ outer) :
    (Region.mk base size).Valid := by
  change base.toNat + outer ≤ 2^64 at valid
  change base.toNat + size ≤ 2^64
  omega

private theorem subregion_contains {base : Val} {outer size : Nat} {p : Val}
    (sizeFits : size ≤ outer) (inside : (Region.mk base size).Contains p) :
    (Region.mk base outer).Contains p :=
  ⟨inside.1, Nat.lt_of_lt_of_le inside.2 (Nat.add_le_add_left sizeFits _)⟩

private theorem window_place {region : Region} {offset size : Nat}
    (valid : region.Valid) (fits : offset+size ≤ region.bytes) :
    (Region.mk (region.base+BitVec.ofNat 64 offset) size).Valid ∧
      ∀ p, (Region.mk (region.base+BitVec.ofNat 64 offset) size).Contains p → region.Contains p := by
  by_cases h : size = 0
  · subst size
    exact ⟨by exact Nat.le_of_lt (BitVec.isLt _), fun p h => False.elim (Nat.not_lt_of_ge h.1 h.2)⟩
  have head := caller_region_contains_offset region valid offset (by omega)
  have addr : (region.base+BitVec.ofNat 64 offset).toNat = region.base.toNat+offset := by
    have total : region.base.toNat+region.bytes ≤ 2^64 := valid
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega : region.base.toNat+offset < 2^64)]
  constructor
  · change (region.base+BitVec.ofNat 64 offset).toNat + size ≤ 2^64
    rw [addr]
    have total : region.base.toNat+region.bytes ≤ 2^64 := valid
    omega
  · intro p inside
    change _ ≤ p.toNat ∧ p.toNat < (region.base+BitVec.ofNat 64 offset).toNat+size at inside
    rw [addr] at inside
    unfold Region.Contains
    omega

attribute [local irreducible] WordLoop.prefix frameFragment blockEvents phaseEvents cycleEvents

private theorem block_within {base sp ptr : Val} {read write : Val → Prop}
    (stack : (Region.mk sp 504).Valid) (source : (Region.mk ptr 64).Valid) (image : (imageRegion base).Valid)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p)
    (inputRead : ∀ p, (Region.mk ptr 64).Contains p → read p)
    (imageRead : ∀ p, (imageRegion base).Contains p → read p) :
    DataWithin read write (blockEvents base sp ptr (base+0x390)) := by
  have tableFits : 0x390 + 256 ≤ (imageRegion base).bytes := by
    change 0x390+256 ≤ Crypto.X86_64.image.size
    decide +kernel
  obtain ⟨table,range⟩ := window_place (offset := 0x390) (size := 256) image tableFits
  have schedule := subregion_valid stack (by decide : 256 ≤ 504)
  have scheduleR p (h : (Region.mk sp 256).Contains p) := stackRead p (subregion_contains (by decide) h)
  have scheduleW p (h : (Region.mk sp 256).Contains p) := stackWrite p (subregion_contains (by decide) h)
  have tableR p (h : (Region.mk (base+0x390) 256).Contains p) := imageRead p (range p h)
  have input := word_loop_within .input base sp ptr (base+0x390) 16 (by decide)
    schedule source table scheduleR scheduleW inputRead tableR
  have expansion := word_loop_within .expansion base sp ptr (base+0x390) 48 (by decide)
    schedule source table scheduleR scheduleW inputRead tableR
  have rounds := word_loop_within .round base sp ptr (base+0x390) 64 (by decide)
    schedule source table scheduleR scheduleW inputRead tableR
  have hash := (frame_fragment_within base sp 0x1c2 9 504 stack (by decide +kernel)).mono stackRead stackWrite
  have feed := (frame_fragment_within base sp 0x282 8 504 stack (by decide +kernel)).mono stackRead stackWrite
  unfold blockEvents
  simpa only [List.append_assoc] using input.append (expansion.append (hash.append (rounds.append feed)))

private theorem phase_within {base sp ptr : Val} {read write : Val → Prop} {n : Nat}
    (stack : (Region.mk sp 504).Valid) (image : (imageRegion base).Valid)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p)
    (imageRead : ∀ p, (imageRegion base).Contains p → read p)
    (input : ∀ j < n,
      let block := Region.mk (ptr+BitVec.ofNat 64 (64*j)) 64
      block.Valid ∧ ∀ p, block.Contains p → read p) :
    DataWithin read write (phaseEvents base sp (base+0x390) n ptr) := by
  have guard := (frame_fragment_within base sp 0x15c 2 504 stack (by decide +kernel)).mono stackRead stackWrite
  induction n generalizing ptr with
  | zero => rw [phaseEvents]; exact guard
  | succ n ih =>
    have source := input 0 (by omega)
    simp only [Nat.mul_zero,BitVec.add_zero] at source
    have block := block_within stack source.1 image stackRead stackWrite source.2 imageRead
    have reset := (frame_fragment_within base sp 0x16b 1 504 stack (by decide +kernel)).mono stackRead stackWrite
    have advance := (frame_fragment_within base sp 0x2c2 3 504 stack (by decide +kernel)).mono stackRead stackWrite
    have tail := ih (ptr := ptr+64) (fun j hj => by
      have addr : ptr+64+BitVec.ofNat 64 (64*j) = ptr+BitVec.ofNat 64 (64*(j+1)) := by
        rw [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (64 : Val)]
        rfl
      simp only [addr]
      exact input (j+1) (by omega))
    unfold phaseEvents
    apply DataWithin.append _ tail
    unfold cycleEvents
    simpa only [List.append_assoc] using guard.append (reset.append (block.append advance))

end Crypto.X86_64

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset lengthOffset paddingBlockCount)

private theorem event_without_data {read write : Val → Prop} {pc : Val} {i : Instr} :
    DataWithin read write [(pc,i,[])] := by simp [DataWithin]

private theorem one_access {read write : Val → Prop} {pc base : Val} {i : Instr} {size off n : Nat}
    (valid : (Region.mk base size).Valid) (fits : off+n ≤ size) (direction : Bool)
    (grant : ∀ p, (Region.mk base size).Contains p → if direction then write p else read p) :
    DataWithin read write [(pc,i,[⟨direction,base+BitVec.ofNat 64 off,n⟩])] := by
  intro e he a ha p hp
  obtain rfl := List.mem_singleton.mp he
  obtain rfl := List.mem_singleton.mp ha
  apply grant
  exact byte_range fits rfl hp valid

private theorem one_address {read write : Val → Prop} {pc base address : Val} {i : Instr} {size off n : Nat}
    (valid : (Region.mk base size).Valid) (fits : off+n ≤ size) (direction : Bool)
    (grant : ∀ p, (Region.mk base size).Contains p → if direction then write p else read p)
    (addressAt : address = base+BitVec.ofNat 64 off) :
    DataWithin read write [(pc,i,[⟨direction,address,n⟩])] := by
  subst address
  exact one_access valid fits direction grant

private theorem copy_within {base sp src : Val} {read write : Val → Prop} (n : Nat)
    (stack : (Region.mk sp 504).Valid) (source : (Region.mk src n).Valid)
    (r : n ≤ 64)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p)
    (input : ∀ p, (Region.mk src n).Contains p → read p) :
    DataWithin read write (tailCopyEvents base sp src n) := by
  have test := (frame_fragment_within base sp 0xc9 2 504 stack (by decide +kernel)).mono stackRead stackWrite
  have preceding (count : Nat) (bound : count ≤ n) :
      DataWithin read write (copyPrefixEvents base sp src count) := by
    induction count with
    | zero => exact empty_within
    | succ count ih =>
      have body : DataWithin read write (copyBodyEvents base sp src count) := by
        unfold copyBodyEvents
        refine DataWithin.append (x := [_]) (y := [_,_,_]) ?_ ?_
        · exact one_access source (off := count) (n := 1) (by omega) false input
        · refine DataWithin.append (x := [_]) (y := [_,_]) ?_ ?_
          · refine one_address stack (off := 288+count) (n := 1) (by omega) true stackWrite ?_
            simp [BitVec.ofNat_add,BitVec.add_assoc]
          · exact DataWithin.append (x := [_]) (y := [_]) event_without_data event_without_data
      exact ((ih (by omega)).append test).append body
  exact (preceding n (by omega)).append test

private theorem suffix_within {base sp : Val} {read write : Val → Prop} {r : Nat}
    (stack : (Region.mk sp 504).Valid) (short : r < 64)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p) :
    DataWithin read write (suffixEvents base sp r) := by
  have bitLength : lengthOffset r + 8 ≤ 128 := by
    unfold lengthOffset
    split <;> decide
  have choose := (frame_fragment_within base sp 0xe8 3 504 stack (by decide +kernel)).mono stackRead stackWrite
  have optional := (frame_fragment_within base sp 0xf3 1 504 stack (by decide +kernel)).mono stackRead stackWrite
  have saved := (frame_fragment_within base sp 0xf8 4 504 stack (by decide +kernel)).mono stackRead stackWrite
  have selected : DataWithin read write (choosePaddingEvents base sp r) := by
    unfold choosePaddingEvents
    apply choose.append
    split
    · exact empty_within
    · exact optional
  simp only [suffixEvents,List.append_assoc]
  refine DataWithin.append (x := [_]) ?_ (selected.append (saved.append ?_))
  · refine one_address stack (off := 288+r) (n := 1) (by omega) true stackWrite ?_
    simp [BitVec.ofNat_add,BitVec.add_assoc]
  · refine one_address stack (off := 288+lengthOffset r) (n := 8) (by omega) true stackWrite ?_
    simp [BitVec.ofNat_add,BitVec.add_assoc]

private theorem iv_within {base sp : Val} {read write : Val → Prop}
    (stack : (Region.mk sp 504).Valid) (image : (imageRegion base).Valid)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p)
    (imageRead : ∀ p, (imageRegion base).Contains p → read p) :
    DataWithin read write (initialHashEvents base sp) := by
  obtain ⟨pool,subset⟩ := window_place (offset := 0x490) (size := 32) image (by
    change 0x490+32 ≤ Crypto.X86_64.image.size
    decide +kernel)
  have readPool p h := imageRead p (subset p h)
  have each (i : Fin 4) : DataWithin read write (ivPairEvents base sp i) := by
    have limits := i.isLt
    simp (config := {decide := true}) only [ivPairEvents, ivPair,moveEvents,FrameMove.eval,
      Regs.get_set_ne,Regs.get_set_same]
    refine DataWithin.append (x := [_]) (y := [_]) ?_ ?_
    · exact one_access pool (off := 8*i.val) (n := 8) (by omega) false readPool
    · exact one_access stack (off := 256+8*i.val) (n := 8) (by omega) true stackWrite
  have pre (n : Nat) : DataWithin read write (ivPrefixEvents base sp n) := by
    induction n with
    | zero => exact (frame_fragment_within base sp 0x113 1 504 stack (by decide +kernel)).mono stackRead stackWrite
    | succ n ih =>
      unfold ivPrefixEvents
      apply ih.append
      split
      · exact each _
      · exact empty_within
  exact (pre 4).append ((frame_fragment_within base sp 0x149 2 504 stack (by decide +kernel)).mono stackRead stackWrite)

private theorem digest_within {base sp dst : Val} {read write : Val → Prop}
    (stack : (Region.mk sp 504).Valid) (output : (Region.mk dst 32).Valid)
    (stackRead : ∀ p, (Region.mk sp 504).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p)
    (digestWrite : ∀ p, (Region.mk dst 32).Contains p → write p) :
    DataWithin read write (digestEvents base sp dst) := by
  have each (i : Fin 8) : DataWithin read write (digestWordEvents base sp dst i) := by
    have limits := i.isLt
    have fits : ∀ index : Fin 8, frameFragmentFits (digestPC index.val) 2 504 = true := by decide +kernel
    have get := (frame_fragment_within base sp _ 2 504 stack (fits i)).mono stackRead stackWrite
    unfold digestWordEvents
    exact get.append (one_access output (off := 4*i.val) (n := 4) (by omega) true digestWrite)
  have words (n : Nat) : DataWithin read write (digestPrefixEvents base sp dst n) := by
    induction n with
    | zero => exact empty_within
    | succ n ih =>
      unfold digestPrefixEvents
      apply ih.append
      split
      · exact each _
      · exact empty_within
  exact ((frame_fragment_within base sp 0x307 1 504 stack (by decide +kernel)).mono stackRead stackWrite).append (words 8)

end Crypto.X86_64

namespace Crypto.X86_64
open X86 Crypto.Baseline
open Crypto.ARM64.Imported (DataAccess caller_region_contains_offset lengthOffset paddingBlockCount)

private theorem pushes_within {base sp : Val} {read write : Val → Prop} (n : Nat)
    (valid : (Region.mk (sp-48) 48).Valid) (grant : ∀ p, (Region.mk (sp-48) 48).Contains p → write p) :
    DataWithin read write (pushEvents base sp n) := by
  induction n with
  | zero => exact empty_within
  | succ n ih =>
    unfold pushEvents
    apply ih.append
    split
    · exact one_access (off := 40-8*n) (n := 8) valid (by omega) true grant
    · exact empty_within

private theorem return_within {base sp : Val} {read write : Val → Prop}
    (valid : (Region.mk sp 512).Valid) (grant : ∀ p, (Region.mk sp 512).Contains p → read p) :
    DataWithin read write (returnEvents base sp) := by
  unfold returnEvents
  refine DataWithin.append (x := [_]) (y := [_,_,_,_,_,_,_,_]) event_without_data ?_
  refine DataWithin.append (x := [_]) (y := [_,_,_,_,_,_,_]) event_without_data ?_
  refine DataWithin.append (x := [_]) (y := [_,_,_,_,_,_]) (one_access valid (off := 456) (n := 8) (by decide) false grant) ?_
  refine DataWithin.append (x := [_]) (y := [_,_,_,_,_]) (one_access valid (off := 464) (n := 8) (by decide) false grant) ?_
  refine DataWithin.append (x := [_]) (y := [_,_,_,_]) (one_access valid (off := 472) (n := 8) (by decide) false grant) ?_
  refine DataWithin.append (x := [_]) (y := [_,_,_]) (one_access valid (off := 480) (n := 8) (by decide) false grant) ?_
  refine DataWithin.append (x := [_]) (y := [_,_]) (one_access valid (off := 488) (n := 8) (by decide) false grant) ?_
  exact DataWithin.append (x := [_]) (y := [_]) (one_access valid (off := 496) (n := 8) (by decide) false grant)
    (one_access valid (off := 504) (n := 8) (by decide) false grant)

private theorem header_within {base sp src : Val} {extent : Nat} {read write : Val → Prop}
    (stack : (Region.mk sp 504).Valid) (input : (Region.mk src extent).Valid) (headerFits : 24 ≤ extent)
    (argRead : ∀ p, (Region.mk src extent).Contains p → read p)
    (stackWrite : ∀ p, (Region.mk sp 504).Contains p → write p) :
    DataWithin read write (headerEvents base sp src) := by
  simp (config := {decide := true}) only [headerEvents,header,moveEvents,FrameMove.eval,Regs.get_set_same,
    Regs.get_set_ne, List.cons_append,List.nil_append]
  refine DataWithin.append (x := [_]) (y := [_,_,_]) (one_access stack (off := 416) (n := 8) (by decide) true stackWrite) ?_
  refine DataWithin.append (x := [_]) (y := [_,_]) (one_access input (show 8+8 ≤ extent by omega) false argRead) ?_
  exact DataWithin.append (x := [_]) (y := [_])
    (one_access input (show 16+8 ≤ extent by omega) false argRead) event_without_data

attribute [local irreducible] prepareEvents preparedCallEvents prepareTailEvents tailCopyEvents
  hashPhasesEvents frameFragment phaseEvents digestEvents digestReturnEvents suffixEvents entryEvents
  initialHashEvents headerEvents returnEvents bodyEvents

/-- Each effective byte address follows from the public call parameters and
lies in the corresponding independently sized caller region. -/
theorem sha256_data_within {base s message extent} (entry : CallerEntry base s message extent) :
    DataWithin (callRead base s message extent) (callBorrow base s extent).exclusive
      (callEvents base s message) := by
  let sp := frameBase s
  let inp := s.regs.get .rdi
  let dst := s.regs.get .rsi
  let ptr := inp + BitVec.ofNat 64 message.offset
  let size := message.bytes.size
  let read := callRead base s message extent
  let write := (callBorrow base s extent).exclusive
  have stack : (Region.mk sp 512).Valid := entry.stackValid
  have locals := subregion_valid stack (by decide : 504 ≤ 512)
  have image : (imageRegion base).Valid := entry.imageValid
  have input : (Region.mk inp extent).Valid := entry.inputValid
  have output : (Region.mk dst 32).Valid := entry.outputValid
  have stackW p (h : (Region.mk sp 504).Contains p) : write p := Or.inr h
  have stackR p (h : (Region.mk sp 504).Contains p) : read p := Or.inr (Or.inr (Or.inr h))
  have imageR p (h : (imageRegion base).Contains p) : read p := Or.inr (Or.inl h)
  have outputW p (h : (Region.mk dst 32).Contains p) : write p := Or.inl h
  have ⟨saved, savedInStack⟩ := window_place (offset := 456) (size := 48) locals (by change 456+48 ≤ 504; decide)
  have savedAddr : sp + BitVec.ofNat 64 456 = s.regs.get .rsp - 48 := by
    change s.regs.get .rsp-504+456 = s.regs.get .rsp-48
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [savedAddr] at saved savedInStack
  have prologue : DataWithin read write (entryEvents base (s.regs.get .rsp)) := by
    unfold entryEvents
    exact (pushes_within 6 saved (fun p h => stackW p (savedInStack p h))).append event_without_data
  obtain ⟨headerMin,_,heapOffset,fit⟩ := entry.layout
  have accessible := entry.accessible
  have headerFits : 24 ≤ extent := by omega
  have hdr := subregion_valid input headerFits
  have hdrRead p (inside : (Region.mk inp 24).Contains p) : read p :=
    Or.inl ⟨subregion_contains headerFits inside, Or.inl inside⟩
  have arguments := header_within (base := base) locals hdr (by decide) hdrRead stackW
  have payloadFits : message.offset+size ≤ extent := by
    change message.bytes.size ≤ message.size-message.offset at fit
    dsimp [size]
    omega
  obtain ⟨payload,payloadInside⟩ := window_place (offset := message.offset) (size := size) input payloadFits
  have payloadR p (inside : (Region.mk ptr size).Contains p) : read p :=
    Or.inl ⟨payloadInside p inside, Or.inr inside⟩
  have init := (frame_fragment_within base sp 0x25 17 504 locals (by decide +kernel)).mono stackR stackW
  have length := (frame_fragment_within base sp 0xa7 9 504 locals (by decide +kernel)).mono stackR stackW
  have tailFit : size/64*64+size%64 ≤ size := by omega
  obtain ⟨tailRegion, tailInside⟩ := window_place (offset := size/64*64)
    (size := size%64) payload tailFit
  have copy := copy_within (base := base) _ locals tailRegion (by omega : size%64 ≤ 64)
    stackR stackW (fun p h => payloadR p (tailInside p h))
  have suffix := suffix_within (base := base) locals (Nat.mod_lt size (by decide)) stackR stackW
  have iv := iv_within locals image stackR stackW imageR
  have prepare : DataWithin read write (prepareEvents base sp ptr size) := by
    unfold prepareEvents prepareTailEvents
    simpa only [List.append_assoc] using init.append (length.append (copy.append (suffix.append iv)))
  have messageWindow (j : Nat) (hj : j < size/64) :
      (Region.mk (ptr+BitVec.ofNat 64 (64*j)) 64).Valid ∧
        ∀ p, (Region.mk (ptr+BitVec.ofNat 64 (64*j)) 64).Contains p → read p := by
    obtain ⟨valid,within⟩ := window_place (offset := 64*j) (size := 64) payload (by change 64*j+64 ≤ size; omega)
    exact ⟨valid,fun p h => payloadR p (within p h)⟩
  have padCount := (Crypto.ARM64.Imported.paddingBlockCount_bounds message.bytes).2
  have paddingWindow (j : Nat) (hj : j < paddingBlockCount message.bytes) :
      (Region.mk (sp+288+BitVec.ofNat 64 (64*j)) 64).Valid ∧
        ∀ p, (Region.mk (sp+288+BitVec.ofNat 64 (64*j)) 64).Contains p → read p := by
    obtain ⟨valid,within⟩ := window_place (offset := 288+64*j) (size := 64) locals (by dsimp; omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at valid within
    exact ⟨valid,fun p h => stackR p (within p h)⟩
  have messagePhase := phase_within locals image stackR stackW imageR messageWindow
  have padPhase := phase_within locals image stackR stackW imageR paddingWindow
  have test := (frame_fragment_within base sp 0x2d3 2 504 locals (by decide +kernel)).mono stackR stackW
  have switch := (frame_fragment_within base sp 0x2de 5 504 locals (by decide +kernel)).mono stackR stackW
  have hash : DataWithin read write
      (hashPhasesEvents base sp ptr (size/64) (paddingBlockCount message.bytes)) := by
    unfold hashPhasesEvents phaseTestEvents
    simpa only [List.append_assoc] using messagePhase.append (test.append (switch.append (padPhase.append test)))
  have bytes := digest_within (base := base) locals output stackR stackW outputW
  have retAddr : sp+BitVec.ofNat 64 504 = s.regs.get .rsp := BitVec.sub_add_cancel _ _
  have fullStackR (p : Val) (inside : (Region.mk sp 512).Contains p) : read p := by
    by_cases low : p.toNat < sp.toNat+504
    · exact stackR p ⟨inside.1,low⟩
    · have start : (sp+BitVec.ofNat 64 504).toNat = sp.toNat+504 := by
        have top : sp.toNat+512 ≤ 2^64 := stack
        rw [BitVec.toNat_add]
        change (sp.toNat+504) % (2^64) = sp.toNat+504
        exact Nat.mod_eq_of_lt (by omega)
      have high : (Region.mk (sp+BitVec.ofNat 64 504) 8).Contains p := by
        have below : p.toNat < sp.toNat+512 := inside.2
        unfold Region.Contains
        change (sp+BitVec.ofNat 64 504).toNat ≤ p.toNat ∧ p.toNat < (sp+BitVec.ofNat 64 504).toNat+8
        rw [start]; omega
      rw [retAddr] at high
      exact Or.inr (Or.inr (Or.inl high))
  have returned := return_within (base := base) (write := write) stack fullStackR
  unfold callEvents bodyEvents preparedCallEvents digestReturnEvents
  simpa only [List.append_assoc] using prologue.append (arguments.append (prepare.append (hash.append (bytes.append returned))))

end Crypto.X86_64
