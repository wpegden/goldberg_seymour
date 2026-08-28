import Tablet.AdjacentEdges
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideGraphHeight
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideMaximalKempePath
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideHeightFiveOutsideLinks]
theorem ScheideHeightFiveOutsideLinks {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (f1 f2 : E) (v1 v2 : V)
    (hf1ends : G.ends f1 =
      s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1))
    (hf2ends : G.ends f2 =
      s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2))
    (hf1color : phi f1 = some gamma) (hf2color : phi f2 = some gamma)
    (hv1T : v1 ∈ TreeSequenceVertexSet T)
    (hv2T : v2 ∈ TreeSequenceVertexSet T)
    (hv10 : v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv11 : v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv12 : v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv13 : v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv14 : v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩)
    (hv20 : v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv21 : v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv22 : v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv23 : v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv24 : v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ alphaEdge betaEdge : E,
      G.ends alphaEdge = s(v1, v2) ∧ phi alphaEdge = some N.alpha ∧
      G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧
      alphaEdge ≠ betaEdge := by
-- BODY
  sorry
