import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideReplacementBoundaryParity
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideReplacementBoundaryAtMostThree]
theorem ScheideReplacementBoundaryAtMostThree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      let X := TreeSequenceVertexSet T
      let Z := X \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}
      let B := @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
        (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
      B.card ≤ 3 := by
-- BODY
  sorry
