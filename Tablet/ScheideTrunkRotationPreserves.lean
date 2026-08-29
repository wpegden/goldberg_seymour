import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGraphHeightOdd
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideTrunkRotationPreserves]
theorem ScheideTrunkRotationPreserves {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k)
      (T' : TreeSequence G e1)
      (N' : NormalGlobalMaximumTriple G k e1 psi T'),
      TrunkRotation N j e1 psi T' N' ∧
        BalancedGlobalMaximumTriple N' := by
-- BODY
  sorry
