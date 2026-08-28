import Tablet.ExtensionBaseSupportClass
import Tablet.SupportingPEColorChain

-- [TABLET NODE: ExtensionBaseSupportClassColors]
theorem ExtensionBaseSupportClassColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (w : V)
    (hw : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc))
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        ∃ a : Fin (p + 1), indices a = r)
    (henumerates : ∀ r : Fin ett.rounds,
      (r.val ≤ q.val ∧
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w) ↔
      ∃ a : Fin (p + 1), indices a = r)
    (gamma delta : Fin (p + 1) → Fin k)
    (hgamma : ∀ a, ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a, ett.series.data.delta (indices a).succ = some (delta a))
    (hdeltaAvoidsEarlierGamma : ∀ a b, a.val ≤ b.val →
      delta b ≠ gamma a) :
    (∀ a : Fin p, gamma a.succ = delta a.castSucc) ∧
      Function.Injective (Fin.cons (gamma 0) delta) := by
-- BODY
  sorry
