import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ExtensionBaseAlgorithmAColorState]
theorem ExtensionBaseAlgorithmAColorState {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigmaN gammaT deltaT)
    (hclassMissing : ∀ (w : V) (t : Fin ett.rounds) (deltaT : Fin k),
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ⊆
          ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport →
      t ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport w →
      (∀ s : Fin ett.rounds,
        s ∈ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport w →
        s.val ≤ t.val) →
      ett.series.data.delta t.succ = some deltaT →
      MissingColors G sigmaN w ∩
          (ExtensionBaseSupportClass ett terminalSupport hterminalSupport w).biUnion
            (fun s => ett.series.data.stored s.succ) = {deltaT})
    (hpairOverlap : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
          vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport vs ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty →
        ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {gammaT} ∧
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {deltaS})) :
    ∀ a : Fin trace.steps,
      trace.delta a ∈
          MissingColors G (trace.coloring a.castSucc) (trace.support a) ∧
        trace.gamma a ∈
          PresentColors G (trace.coloring a.castSucc) (trace.support a) := by
-- BODY
  sorry
