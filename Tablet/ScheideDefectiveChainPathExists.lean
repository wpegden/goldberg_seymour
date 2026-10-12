import Tablet.P2968_T1_DefectiveColorComponentPath
import Tablet.TreeFreeColors

-- [TABLET NODE: ScheideDefectiveChainPathExists]
theorem ScheideDefectiveChainPathExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u) :
    ∃ (z : V)
      (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
        (Sum.inl u) (Sum.inl z)),
      ScheideDefectiveChainPath T phi alpha gamma u z p := by
-- BODY
  exact P2968_T1_DefectiveColorComponentPath G k e0 phi T hglobal alpha gamma halpha u hu hgamma
