import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDepartureReturn

-- [TABLET NODE: ScheideDefectiveChainDepartureReturn]
theorem ScheideDefectiveChainDepartureReturn {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p) :
    ∃ (i1 i2 : Fin (p.length + 1)) (v1 v2 : V),
      ScheideDepartureReturn T i1 i2 v1 v2 := by
-- BODY
  sorry
