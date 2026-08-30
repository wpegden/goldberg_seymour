import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumOrder
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
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideHeightFiveGammaEdges]
theorem ScheideHeightFiveGammaEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (g : E) (v : V) (hgcolor : phi g = some gamma)
    (hgends :
      G.ends g = s(T.vertex ⟨0, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨2, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨3, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v))
    (hvT : v ∈ TreeSequenceVertexSet T)
    (hv0 : v ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv1 : v ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv2 : v ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv3 : v ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv4 : v ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ (f1 f2 f3 : E) (v1 v2 : V),
      G.ends f1 = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1) ∧
      G.ends f2 = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2) ∧
      G.ends f3 = s(T.vertex ⟨2, by have := N.height_upper; omega⟩,
        T.vertex ⟨3, by have := N.height_upper; omega⟩) ∧
      phi f1 = some gamma ∧ phi f2 = some gamma ∧
      phi f3 = some gamma ∧
      v1 ∈ TreeSequenceVertexSet T ∧ v2 ∈ TreeSequenceVertexSet T ∧
      v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ := by
-- BODY
  sorry
