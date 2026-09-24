import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralInternalPair
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

open scoped Sym2

-- [TABLET NODE: ScheideDefectiveCrossingSelection]
theorem ScheideDefectiveCrossingSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (g1 : E) (hg1 : phi g1 = some d.1)
    (x : V) (hx : x ∈ ({C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1} : Finset V))
    (hxg1 : Incident G x g1)
    (z1 : V) (hz1 : z1 ∈ TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1})
    (hz1g1 : Incident G z1 g1) :
    let i := D.gammaIndex d
    let X := TreeSequenceVertexSet T
    let U := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
    let Z := X \ U
    ∃ u1 u2 : V, ∃ g2 g3 : E, ∃ z3 w3 : V,
      ({u1, u2} : Finset V) = U ∧ x = u1 ∧
      u1 ≠ u2 ∧ u1 ∈ U ∧ u2 ∈ U ∧ u1 ∈ X ∧ u2 ∈ X ∧
      D.v0 d ∈ Z ∧
      C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ Z ∧
      D.alpha0 ≠ C.gamma i ∧ D.alpha0 ≠ d.1 ∧ C.gamma i ≠ d.1 ∧
      G.ends g1 = s(u1, z1) ∧
      phi g2 = some D.alpha0 ∧ G.ends g2 = s(u1, u2) ∧
      g3 ∈ BoundaryColorEdges G phi X d.1 ∧ g3 ≠ D.f0 d ∧
      z3 ∈ Z ∧ w3 ∉ X ∧ G.ends g3 = s(z3, w3) ∧
      g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 := by
-- BODY
  sorry
