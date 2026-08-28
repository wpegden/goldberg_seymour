import Tablet.IsProperEdgeColoring
import Tablet.ScheideReplacementInternalMissing

-- [TABLET NODE: ScheideReplacementPairsLaminar]
theorem ScheideReplacementPairsLaminar {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ∀ d d', ({(R d).u1, (R d).u2} : Finset V) =
        ({(R d').u1, (R d').u2} : Finset V) ∨
      Disjoint ({(R d).u1, (R d).u2} : Finset V)
        ({(R d').u1, (R d').u2} : Finset V) := by
-- BODY
  sorry
