import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.LooplessMultigraph
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseClaim43EdgeEffects]
theorem ExtensionBaseClaim43EdgeEffects {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace) :
    let rho1 := trace.coloring (Fin.last trace.steps)
    let restorationColors :=
      (ExtensionBaseRestorationIndices ett terminalSupport
        hterminalSupport).biUnion fun t => ett.series.data.stored t.succ
    ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors := by
-- BODY
  sorry
