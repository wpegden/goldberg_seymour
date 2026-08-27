import Tablet.Critical
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree

-- [TABLET NODE: KTriple]
def KTriple {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) : Prop :=
-- BODY
  Critical G ∧ ChromaticIndex G = k + 1 ∧ MaximumDegree G + 1 ≤ k ∧
    IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0
