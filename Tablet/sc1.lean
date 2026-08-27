import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors

-- [TABLET NODE: sc1]
theorem sc1 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperPi : IsProperEdgeColoring G pi)
    (honePi : IsOneEdgeUncolored pi e0) :
    StableColoring T C phi pi ↔
      ∀ f, TreeIncidentEdge T f →
        ((∃ c ∈ TreeMissingColors phi T ∪ C, phi f = some c) ∨
          (∃ c ∈ TreeMissingColors phi T ∪ C, pi f = some c)) →
        pi f = phi f := by
-- BODY
  sorry
