import Proofs.ARM64.ImportedBranchFetch

namespace Crypto.ARM64.Imported

theorem cycles_path_of_prefixes (base : BitVec 64) (code : List (BitVec 32))
    (s out : Arm64.State) (n : Nat) (permitted : PermittedWords code)
    (cyclePath : ∀ i, i < n → ∀ (before after : Arm64.State),
      runCycles code i s = some before → runWords code before = some after →
      after.status = .Running → StaticPath base code before)
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
      have prefixPath := ih mid (fun i hi before after hp he hr => cyclePath i (by omega) before after hp he hr) hm midRunning
      have prefixExec := (runCycles_words code n s).symm.trans hm
      have lastPath := cyclePath n (by omega) mid out hm bodyExec running
      have combined := StaticPath.append prefixExec prefixPath lastPath
      simpa only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using combined


end Crypto.ARM64.Imported
