import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree
import Tablet.OutsideTreeColorSwap
import Tablet.StableColoring
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.sc1
import Tablet.sc2

open scoped Sym2

-- [TABLET NODE: LEM_extable]
theorem LEM_extable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 f : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) (u v : V) (delta : Fin k)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (hfboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T))
    (hfends : G.ends f = s(u, v))
    (huout : u ∉ TreeSequenceVertexSet T)
    (hvin : v ∈ TreeSequenceVertexSet T)
    (hfcolor : phi f = some delta)
    (hexists : ∃ pi : PartialEdgeColoring E k,
      IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
        StableColoring T (insert delta C) phi pi ∧
        ∃ beta, beta ∈ MissingColors G pi u ∧ beta ∈ TreeMissingColors pi T) :
    ∀ alpha, alpha ∈ MissingColors G phi v →
      ∃ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
          StableColoring T (insert delta C) phi sigma ∧
          TreeExit T sigma alpha delta v := by
-- BODY
  sorry
