import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.TashTree
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovClosureExists
import Tablet.TashkinovTree
import Tablet.TchangeKempeClosureData
import Tablet.TreeExitPath
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: TchangeKempeClosurePreparation]
theorem TchangeKempeClosurePreparation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0)
    (hmissing : C.a ∈ MissingColors G C.phi C.b3)
    (h13 : TreeVertexOrder C.T C.b1 C.b3)
    (h23 : TreeVertexOrder C.T C.b2 C.b3) :
    Nonempty (TchangeKempeClosureData C) := by
-- BODY
  sorry
