import Tablet.ScheideReplacementMaximum
import Tablet.ScheideSymmetricMissingInternal

-- [TABLET NODE: ScheideReplacementUnionClosed]
theorem ScheideReplacementUnionClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetClosed G phi (TreeSequenceVertexSet T ∪ {R.u1, R.u2}) := by
-- BODY
  sorry
