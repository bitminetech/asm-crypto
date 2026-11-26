import Proofs.X86_64.PlatformFrame
import Proofs.X86_64.Image
import Proofs.X86_64.ScalarControl

namespace Crypto.X86_64
open X86

def codeLayout := (layout 0 200).getD []
def starts := codeLayout.map Prod.fst

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem edges : codeLayout.all (fun p =>
    (successors p.1 p.2).all (fun a => starts.contains a.toNat)) = true := by decide +kernel

private theorem layout_decodes {off n code} (h : layout off n = some code) :
    ∀ p ∈ code, decodeAt image p.1 = some p.2 := by
  induction n generalizing off code with
  | zero => simp [layout] at h; simp [h.2]
  | succ n ih =>
    rw [layout] at h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i,decoded,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest,tail,h⟩ := Option.bind_eq_some_iff.mp h
    have eq : (off,i)::rest = code := Option.some.inj h
    subst code
    intro p member
    rcases List.mem_cons.mp member with rfl | later
    · exact decoded
    · exact ih tail p later

private theorem code_decodes {p} (member : p ∈ codeLayout) : decodeAt image p.1 = some p.2 := by
  unfold codeLayout at member
  cases result : layout 0 200 with
  | none => simp [result] at member
  | some code => exact layout_decodes result _ (by simpa only [result,Option.getD_some] using member)

theorem entry_is_instruction_start : 0 ∈ starts := by decide +kernel

private theorem step_successor (form : ScalarForm) (len : Nat) (s : Cpu) (base : Val)
    (live : s.ms = none) (after : (X86.step ⟨form.op,len⟩ s).ms = none)
    (regular : isReturn ⟨form.op,len⟩ = false) :
    (X86.step ⟨form.op,len⟩ s).rip - base ∈ successors (s.rip-base).toNat ⟨form.op,len⟩ := by
  have actual := step_edges form len s live regular after
  generalize hp : (X86.step ⟨form.op,len⟩ s).rip = p at actual ⊢
  have shift (n : Val) : s.rip+n-base = (s.rip-base)+n := by
    simp only [BitVec.sub_eq_add_neg]; ac_rfl
  have branch (n d : Val) : s.rip+n+d-base = (s.rip-base)+n+d := by
    simp only [BitVec.sub_eq_add_neg]; ac_rfl
  cases form <;> simp only [successors, nextAddresses, ScalarForm.op, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.mem_cons, List.not_mem_nil, or_false] at actual ⊢ <;>
    first | contradiction | (rw [actual,shift]) | (rw [actual,branch]) |
      (rcases actual with h|h <;> rw [h] <;> simp [shift,branch])

attribute [local irreducible] X86.step codeLayout image

theorem decoded_boundary {base s i} (fetched : fetch base s = some i) (start : (s.rip-base).toNat ∈ starts) :
    ((s.rip-base).toNat,i) ∈ codeLayout := by
  obtain ⟨⟨off,op⟩,member,pc⟩ := List.mem_map.mp start
  dsimp only [Prod.fst] at pc
  subst off
  have eq := Option.some.inj ((fetch_decodes fetched).symm.trans (code_decodes member))
  change i = op at eq
  exact eq ▸ member

theorem fetched_successor {base s i} (fetched : fetch base s = some i) (live : s.ms = none)
    (after : (X86.step i s).ms = none) (regular : isReturn i = false) :
    (X86.step i s).rip-base ∈ successors (s.rip-base).toNat i := by
  obtain ⟨form,shape⟩ := fetched_scalar fetched
  obtain ⟨op,len⟩ := i
  change op = form.op at shape
  subst op
  exact step_successor form len s base live after regular

theorem successor_start {base s i} (fetched : fetch base s = some i) (live : s.ms = none)
    (after : (X86.step i s).ms = none) (regular : isReturn i = false)
    (start : (s.rip-base).toNat ∈ starts) :
    ((X86.step i s).rip-base).toNat ∈ starts := by
  have closed := List.all_eq_true.mp edges _ (decoded_boundary fetched start)
  exact List.contains_iff_mem.mp (List.all_eq_true.mp closed _ (fetched_successor fetched live after regular))

theorem returnAt_live {base n s out} (returned : returnAt base n s = some out) : s.ms = none := by
  cases n with
  | zero => simp [returnAt] at returned
  | succ n =>
    cases h : s.ms with
    | none => rfl
    | some e => simp [returnAt, guard, Cpu.stopped, h] at returned

theorem returnAt_boundaries {base n s out} (start : (s.rip-base).toNat ∈ starts)
    (returned : returnAt base n s = some out) :
    ∃ trace, Execution base s trace out ∧ trace.length = n ∧
      ∀ e ∈ trace, ((e.1-base).toNat, e.2) ∈ codeLayout := by
  induction n generalizing s with
  | zero => simp [returnAt] at returned
  | succ n ih =>
    have live := returnAt_live returned
    rw [returnAt] at returned
    cases f : fetch base s with
    | none => simp [Cpu.stopped, live, f, guard] at returned
    | some i =>
      have one : stepLoaded base s = some (X86.step i s) := by simp [stepLoaded,Cpu.stopped,live,guard,f]
      have member := decoded_boundary f start
      cases r : isReturn i with
      | true =>
        cases n with
        | zero =>
          have eq : X86.step i s = out := by simpa [Cpu.stopped,live,f,guard,r] using returned
          subst out
          exact ⟨[(_,i)],.cons f one (.nil _),rfl,by intro e h; obtain rfl := List.mem_singleton.mp h; exact member⟩
        | succ n => simp [Cpu.stopped,live,f,guard,r] at returned
      | false =>
        have tail : returnAt base n (X86.step i s) = some out := by simpa [Cpu.stopped,live,f,guard,r] using returned
        obtain ⟨trace,actual,count,bound⟩ := ih (successor_start f live (returnAt_live tail) r start) tail
        exact ⟨(_,i)::trace,.cons f one actual,by simp [count],
          by intro e h; rcases List.mem_cons.mp h with rfl | later; exact member; exact bound e later⟩

theorem sha256_instruction_boundaries {base s message extent} (entry : CallerEntry base s message extent) :
    ∃ out trace, Execution base s trace out ∧ CallResult s out message ∧
      trace.length = callSteps message.bytes.size ∧ ∀ e ∈ trace, ((e.1-base).toNat,e.2) ∈ codeLayout := by
  obtain ⟨out,returned,result⟩ := sha256_serial _ _ _ _ entry
  obtain ⟨trace,actual,count,sites⟩ := returnAt_boundaries (by simpa [entry.pc] using entry_is_instruction_start) returned
  exact ⟨out,trace,actual,result,count,sites⟩

end Crypto.X86_64
