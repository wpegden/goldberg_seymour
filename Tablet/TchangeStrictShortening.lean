import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetClosed
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TchangeCounterexampleMeasure
import Tablet.TchangeKempeClosureData
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: TchangeStrictShortening]
theorem TchangeStrictShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0)
    (D : TchangeKempeClosureData C) :
    ∃ C' : TchangeCounterexample G k e0,
      TchangeCounterexampleMeasure C' < TchangeCounterexampleMeasure C := by
-- BODY
  sorry
