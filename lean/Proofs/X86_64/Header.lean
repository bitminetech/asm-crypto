import Proofs.X86_64.SetupMoves

namespace Crypto.X86_64
open X86

def header : FrameCode := [(.store 416 .rsi,8),(.load .rax .rdi 8,4),(.load .rcx .rdi 16,4)]
private def payloadPtr : Instr := ⟨.lea .q .rbp {base := some .rdi, index := some .rax},4⟩
private def zeroRax : Instr := ⟨(WordInst.rr .xor .rax .rax).op,2⟩
private def zeros (n : Nat) : FrameCode := (List.range n).map (fun i => (.store (288+8*i) .rax,8))

private theorem setup_bytes : decodeSeq 0x11 3 = some (moveInstructions header) ∧
    decodeAt image 0x21 = some payloadPtr ∧ decodeAt image 0x25 = some zeroRax ∧
    decodeSeq 0x27 16 = some (moveInstructions (zeros 16)) := by decide +kernel

private theorem payload_step (s : Cpu) (live : s.ms = none) : X86.step payloadPtr s =
    {s with regs := s.regs.set .rbp (s.regs.get .rdi + s.regs.get .rax), rip := s.rip+4} := by
  simp [payloadPtr, X86.step, Cpu.stopped, live, Cpu.setReg, Cpu.setRip, Ea.offset, Scale.toVal, Value.writeView]

private theorem clear_step (s : Cpu) (live : s.ms = none) :
    let out := X86.step zeroRax s
    out.ms = none ∧ out.rip = s.rip+2 ∧ out.mem = s.mem ∧ out.regs = s.regs.set .rax 0 := by
  obtain ⟨proj, hl, rip⟩ := word_step (.rr .xor .rax .rax) s 2 live
  refine ⟨hl,rip,congrArg DataState.mem proj,?_⟩
  simpa [WordInst.eval, WordOp.apply, DataState.put, project, DataState.word, zeroRax] using congrArg DataState.regs proj

private def zeroMem (s : Cpu) (n : Nat) := (List.range n).foldl (fun (m : Mem) i =>
  m.writeSize .q (s.regs.get .rsp+BitVec.ofNat 64 (288+8*i)) 0) s.mem

private theorem zeros_eval (s : Cpu) (n : Nat) (z : s.regs.get .rax = 0) :
    moveRun (zeros n) s = {s with rip := s.rip+BitVec.ofNat 64 (8*n), mem := zeroMem s n} := by
  induction n with
  | zero => simp [moveRun, zeros, zeroMem]
  | succ n ih =>
    change List.foldl _ _ _ = _ at ih
    simp only [zeros, moveRun, List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, zeros] at ih ⊢
    rw [ih]
    simp [FrameMove.eval, zeroMem, List.range_succ, z, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]

private theorem zero_view (s : Cpu) (n : Nat) :
    byteView (zeroMem s n) = (List.range n).foldl (fun m i =>
      Arm64.Memory.write64 m (s.regs.get .rsp+BitVec.ofNat 64 (288+8*i)) 0) (byteView s.mem) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zeroMem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, byteView_write64] at ih ⊢
    rw [ih]

theorem zero_padding_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x25)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 416 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat) :
    ∃ out, steps base 17 s = some out ∧ out.ms = none ∧ out.rip = base+0xa7 ∧
      out.regs = s.regs.set .rax 0 ∧ (∀ i : Fin 128, out.mem.read (s.regs.get .rsp+288+BitVec.ofNat 64 i.val) = 0) ∧
      ∀ p, 128 ≤ (p-(s.regs.get .rsp+288)).toNat → out.mem.read p = s.mem.read p := by
  let mid := X86.step zeroRax s
  have first := one_at base s 0x25 _ live loaded pc setup_bytes.2.2.1 (by decide) (by decide)
  obtain ⟨ok, rip, mem, regs⟩ := clear_step s live
  change mid.mem = s.mem at mem
  change mid.regs = _ at regs
  have sp : mid.regs.get .rsp = s.regs.get .rsp := by simp [regs, Regs.get_set_ne]
  have wf : ∀ p ∈ zeros 16, p.1.wellPlaced 416 := by
    intro p hp
    obtain ⟨i, h, rfl⟩ := List.mem_map.mp hp
    change 288+8*i+8 ≤ 416
    have := List.mem_range.mp h
    omega
  have stores := moves_loaded base (zeros 16) 0x27 416 mid ok (by simpa [pc, BitVec.add_assoc] using rip)
    (mem ▸ loaded) (by simpa only [sp] using sep) wf setup_bytes.2.2.2
  have eval := zeros_eval mid 16 (by simp [regs])
  let snapshot : Arm64.State := {mem := byteView s.mem, sp := s.regs.get .rsp}
  have bytes : byteView (zeroMem mid 16) = Crypto.ARM64.Imported.zeroPadMemory snapshot := by
    rw [zero_view, sp, mem]; rfl
  refine ⟨_, steps_append first stores, ?_⟩
  rw [eval]
  refine ⟨ok, ?_, regs, ?_, ?_⟩
  · change mid.rip + _ = _; rw [show mid.rip = _ from rip, pc]; simp [BitVec.add_assoc]
  · intro i
    change (zeroMem mid 16).read _ = _
    rw [← byteView_read, bytes]
    exact Crypto.ARM64.Imported.zeroPadMemory_byte snapshot i
  · intro p hp
    change (zeroMem mid 16).read p = _
    rw [← byteView_read, bytes]
    change (Crypto.ARM64.Imported.zeroPadMemory snapshot).read8 p = (byteView s.mem).read8 p
    unfold Arm64.Memory.read8
    rw [Crypto.ARM64.Imported.zeroPadMemory_outside snapshot p hp]

def headerOffset (s : Cpu) := s.mem.readSize .q (s.regs.get .rdi+8)
def headerLength (s : Cpu) := s.mem.readSize .q (s.regs.get .rdi+16)

def headerEvents (base sp input : Val) : List Event :=
  moveEvents header {rip := base+0x11, regs := (Regs.set {} .rsp sp).set .rdi input} ++
    [(base+0x21,payloadPtr,[])]

structure HeaderState (base : Val) (s out : Cpu) : Prop where
  live : out.ms = none
  pc : out.rip = base+0x25
  stack : out.regs.get .rsp = s.regs.get .rsp
  count : out.regs.get .rcx = headerLength s
  payload : out.regs.get .rbp = s.regs.get .rdi + headerOffset s
  mem : out.mem = s.mem.writeSize .q (s.regs.get .rsp+416) (s.regs.get .rsi)
  observations : ObservedExecution base s (headerEvents base (s.regs.get .rsp) (s.regs.get .rdi)) out

set_option maxHeartbeats 1200000 in
theorem header_loaded (base : Val) (s : Cpu) (live : s.ms = none) (pc : s.rip = base+0x11)
    (loaded : ImageLoaded base s.mem)
    (sep : ∀ j, j < image.size → 424 ≤ (base+BitVec.ofNat 64 j-s.regs.get .rsp).toNat)
    (arg : ∀ j : Fin 24, 8 ≤ (s.regs.get .rdi+BitVec.ofNat 64 j.val-(s.regs.get .rsp+416)).toNat) :
    ∃ out, steps base 4 s = some out ∧ HeaderState base s out := by
  have wf : ∀ p ∈ header, p.1.wellPlaced 424 := by
    intro p h; simp only [header,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h <;> subst p <;> decide
  let mid := moveRun header s
  have run := moves_loaded base header 0x11 424 s live pc loaded sep wf setup_bytes.1
  let saved := s.mem.writeSize .q (s.regs.get .rsp+416) (s.regs.get .rsi)
  have read (n : Nat) (bound : n+8 ≤ 24) :
      saved.readSize .q (s.regs.get .rdi+BitVec.ofNat 64 n) = s.mem.readSize .q (s.regs.get .rdi+BitVec.ofNat 64 n) := by
    apply Mem.readN_congr _ _ _ 8
    intro b hb
    apply counter_frame
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact arg ⟨n+b,by omega⟩
  have mem : mid.mem = saved := by simp [mid, moveRun, header, FrameMove.eval, saved]
  have ok : mid.ms = none := by simp [mid, moveRun, header, FrameMove.eval, live]
  have rip : mid.rip = base+0x21 := by simp [mid, moveRun, header, FrameMove.eval, pc, BitVec.add_assoc]
  have code : ImageLoaded base mid.mem := by
    intro j hj
    rw [mem]
    dsimp only [saved]
    exact (counter_frame _ _ _ _ (Crypto.ARM64.Imported.region_store_delta _ _ 416 424 8 (by decide) (sep j hj))).trans (loaded j hj)
  have last := one_at base mid 0x21 _ ok code rip setup_bytes.2.1 (by decide) (by decide)
  have registers : mid.regs = (s.regs.set .rax (saved.readSize .q (s.regs.get .rdi+8))).set .rcx
      (saved.readSize .q (s.regs.get .rdi+16)) := by
    simp [mid, moveRun, header, FrameMove.eval, saved, Regs.get_set_ne]
  have offset : mid.regs.get .rax = headerOffset s := by
    simp only [registers, Regs.get_set_ne _ .rcx .rax _ (by decide), Regs.get_set_same]
    exact read 8 (by decide)
  have len : mid.regs.get .rcx = headerLength s := by
    simp only [registers, Regs.get_set_same]; exact read 16 (by decide)
  have sp : mid.regs.get .rsp = s.regs.get .rsp := by simp [registers, Regs.get_set_ne]
  have argPtr : mid.regs.get .rdi = s.regs.get .rdi := by simp [registers, Regs.get_set_ne]
  have readTrace := moves_observed header live run pc setup_bytes.1 (by decide +kernel)
  have addressTrace := steps_observe_single last rip setup_bytes.2.1 (by decide) (by decide) rfl
  have events : moveEvents header s ++ [(base+0x21,payloadPtr,[])] =
      headerEvents base (s.regs.get .rsp) (s.regs.get .rdi) := by
    simp [headerEvents,header,moveEvents,FrameMove.eval,pc,Regs.get_set_ne,BitVec.add_assoc]
  have observed := readTrace.append addressTrace
  change ObservedExecution base s (moveEvents header s ++ [(base+0x21,payloadPtr,[])]) _ at observed
  rw [events] at observed
  refine ⟨_, steps_append run last, ?_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,observed⟩ <;> rw [payload_step mid ok]
  · exact ok
  · simp [rip,BitVec.add_assoc]
  · simpa [Regs.get_set_ne] using sp
  · simpa [Regs.get_set_ne] using len
  · simp [argPtr,offset]
  · exact mem

end Crypto.X86_64
