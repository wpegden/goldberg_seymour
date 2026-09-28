import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep

-- [TABLET NODE: ExtensionBaseSameSupportStoredPairOverlap]
theorem ExtensionBaseSameSupportStoredPairOverlap {V E : Type*}
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
    (hdeltaAvoidsEarlierGamma : ∀ (a b : Fin (p + 1))
      (gammaA deltaB : Fin k), a.val ≤ b.val →
      ett.series.data.gamma (indices a).succ = some gammaA →
      ett.series.data.delta (indices b).succ = some deltaB →
      deltaB ≠ gammaA)
    (s t : Fin ett.rounds)
    (hsClass : s ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport w)
    (htClass : t ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport w)
    (hst : s.val < t.val)
    (gammaS deltaS gammaT deltaT : Fin k)
    (hsGamma : ett.series.data.gamma s.succ = some gammaS)
    (hsDelta : ett.series.data.delta s.succ = some deltaS)
    (htGamma : ett.series.data.gamma t.succ = some gammaT)
    (htDelta : ett.series.data.delta t.succ = some deltaT) :
    ((ett.series.data.stored s.succ ∩
        ett.series.data.stored t.succ).Nonempty ↔
      ¬ ∃ r : Fin ett.rounds,
        r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport w ∧
        s.val < r.val ∧ r.val < t.val) ∧
    ((ett.series.data.stored s.succ ∩
        ett.series.data.stored t.succ).Nonempty →
      ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ = {gammaT} ∧
        ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ = {deltaS}) := by
-- BODY
  sorry
