import Tablet.ColoredVertexSetElementary
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.ChromaticIndexSpec
import Tablet.Critical
import Tablet.Density
import Tablet.DensityCeil
import Tablet.DensityLowerBound
import Tablet.DensityValue
import Tablet.Elementary
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.StronglyClosedWitnessElementary

open scoped Sym2

-- [TABLET NODE: egraph2]
theorem egraph2 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e) :
    (Elementary G ↔
      ∀ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
          ColoredVertexSetElementary G phi Finset.univ) ∧
    ((∀ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
          ColoredVertexSetElementary G phi Finset.univ) ↔
      ∃ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          ColoredVertexSetElementary G phi Finset.univ) ∧
    ((∃ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          ColoredVertexSetElementary G phi Finset.univ) ↔
      ∃ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          (∀ v, v ∈ G.ends e0 → v ∈ X) ∧
          ColoredVertexSetElementary G phi X ∧
          ColoredVertexSetStronglyClosed G phi X) := by
-- BODY
  sorry
