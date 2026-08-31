import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.OutsideKempeRecoloring
import Tablet.StableColoring
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: OutsideKempeRecoloringStable]
theorem OutsideKempeRecoloringStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi sigma : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring T C phi sigma ∧
    TreeColoringInvariant T phi sigma ∧
    ∀ f : E, TreeIncidentEdge T f → sigma f = phi f := by
-- BODY
  sorry
