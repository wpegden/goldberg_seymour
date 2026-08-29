import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.Incident
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseClaim43Stability]
theorem ExtensionBaseClaim43Stability {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN phiJ : PartialEdgeColoring E k)
    (C : Finset (Fin k))
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace)
    (hsigmaStable : StableColoringBeforeVertex T terminalSupport
      hterminalSupport C phiJ sigmaN) :
    StableColoringBeforeVertex T terminalSupport hterminalSupport C phiJ
      (trace.coloring (Fin.last trace.steps)) := by
-- BODY
  sorry
