import Proofs.ARM64.ImportedLinearFetch

/-!
Static-path rules for image spans ending in a branch and repeated recorded
cycles. A cycle proof plus the existing native PC invariant lifts its repeated
path; no cryptographic operation replaces an instruction.
-/
namespace Crypto.ARM64.Imported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem image_permitted_all : ∀ i : Fin 151,
    ((Arm64.decode imageWords[i.val]!).map permittedInstruction).getD false = true := by
  decide +kernel

theorem image_permitted (i : Fin 151) (instruction : Arm64.Instr)
    (decoded : Arm64.decode imageWords[i.val]! = some instruction) : permittedInstruction instruction = true := by
  have result := image_permitted_all i
  simpa only [decoded, Option.map_some, Option.getD_some] using result

theorem image_single_permitted (i : Fin 151) : PermittedWords [imageWords[i.val]!] := by
  intro word member instruction decoded
  have eq : word = imageWords[i.val]! := by simpa using member
  subst word
  exact image_permitted i instruction decoded

theorem image_single_path (base : BitVec 64) (i : Fin 224) (s out : Arm64.State)
    (pc : s.pc = base + BitVec.ofNat 64 (4 * i.val))
    (executed : runWords [imageWords[i.val]!] s = some out) : StaticPath base [imageWords[i.val]!] s := by
  cases decoded : Arm64.decode imageWords[i.val]! with
  | none => simp [runWords, decoded] at executed
  | some instruction =>
    simp only [StaticPath, decoded]
    refine ⟨?_, True.intro⟩
    rw [pc, image_fetch, decoded]

def imageChunk (offset prefixCount : Nat) := imageSlice offset prefixCount ++ [imageWords[offset + prefixCount]!]

set_option maxRecDepth 16384 in
theorem image_chunk_path (base : BitVec 64) (offset prefixCount : Nat) (s out : Arm64.State)
    (bound : offset + prefixCount < 151)
    (sequential : SequentialWords (imageSlice offset prefixCount))
    (pc : s.pc = base + BitVec.ofNat 64 (4 * offset))
    (executed : runWords (imageChunk offset prefixCount) s = some out) (running : out.status = .Running) :
    StaticPath base (imageChunk offset prefixCount) s := by
  obtain ⟨mid, prefixExec, branchExec⟩ := runWords_append_split (imageSlice offset prefixCount)
    [imageWords[offset + prefixCount]!] s out executed
  have midRunning := runWords_running_before [imageWords[offset + prefixCount]!] mid out
    (image_single_permitted ⟨offset + prefixCount, bound⟩) branchExec running
  obtain ⟨prefixPath, midPC⟩ := sequential_slice_path base offset prefixCount s mid (by omega)
    sequential pc prefixExec midRunning
  have branchPath := image_single_path base ⟨offset + prefixCount, by omega⟩ mid out midPC branchExec
  exact StaticPath.append prefixExec prefixPath branchPath

theorem PermittedWords.append {xs ys : List (BitVec 32)} (left : PermittedWords xs) (right : PermittedWords ys) :
    PermittedWords (xs ++ ys) := by
  intro word member instruction decoded
  cases List.mem_append.mp member with
  | inl h => exact left word h instruction decoded
  | inr h => exact right word h instruction decoded

theorem PermittedWords.repeated {code : List (BitVec 32)} (permitted : PermittedWords code) (n : Nat) :
    PermittedWords (List.replicate n code).flatten := by
  induction n with
  | zero => intro word member; simp at member
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    exact permitted.append ih

theorem cycles_staticPath (base : BitVec 64) (code : List (BitVec 32)) (startPC : BitVec 64)
    (s out : Arm64.State) (n : Nat) (permitted : PermittedWords code)
    (cyclePath : ∀ (before after : Arm64.State), before.pc = startPC → runWords code before = some after →
      after.status = .Running → StaticPath base code before)
    (pcInvariant : ∀ i, i < n → ∀ mid, runCycles code i s = some mid → mid.pc = startPC)
    (executed : runCycles code n s = some out) (running : out.status = .Running) :
    StaticPath base (List.replicate n code).flatten s := by
  induction n generalizing out with
  | zero => exact True.intro
  | succ n ih =>
    change (runCycles code n s).bind (runWords code) = some out at executed
    cases hm : runCycles code n s with
    | none => simp [hm] at executed
    | some mid =>
      have bodyExec : runWords code mid = some out := by simpa only [hm, Option.bind_some] using executed
      have midRunning := runWords_running_before code mid out permitted bodyExec running
      have prefixPath := ih mid (fun i hi mid he => pcInvariant i (by omega) mid he) hm midRunning
      have prefixExec := (runCycles_words code n s).symm.trans hm
      have lastPath := cyclePath mid out (pcInvariant n (by omega) mid hm) bodyExec running
      have combined := StaticPath.append prefixExec prefixPath lastPath
      simpa only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using combined

end Crypto.ARM64.Imported
