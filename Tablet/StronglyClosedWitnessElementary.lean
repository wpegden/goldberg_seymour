import Tablet.ChromaticIndex
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.Degree
import Tablet.Density
import Tablet.DensityCeil
import Tablet.DensityLowerBound
import Tablet.DensityValue
import Tablet.Elementary
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.PresentColors

-- [TABLET NODE: StronglyClosedWitnessElementary]
theorem StronglyClosedWitnessElementary {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hends : ∀ v, v ∈ G.ends e0 → v ∈ X)
    (helementary : ColoredVertexSetElementary G phi X)
    (hstrong : ColoredVertexSetStronglyClosed G phi X) : Elementary G := by
-- BODY
  sorry
