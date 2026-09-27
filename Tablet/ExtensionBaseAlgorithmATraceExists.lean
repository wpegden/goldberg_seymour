import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationTrace
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ExtensionBaseAlgorithmATraceExists]
theorem ExtensionBaseAlgorithmATraceExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (sigmaN : PartialEdgeColoring E k)
    (hslotData : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT) :
    Nonempty (ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN) := by
-- BODY
  sorry
