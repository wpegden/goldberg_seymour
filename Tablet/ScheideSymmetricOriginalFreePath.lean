import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideSymmetricOriginalFreePath]
theorem ScheideSymmetricOriginalFreePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∃ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phi d.1 beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1} ∧
      beta ∈ MissingColors G phi v ∧
      beta ∈ TreeFreeColors phi T ∧
      beta ≠ C.gamma (D.gammaIndex d) ∧
      ScheideDefectiveChainPath T phi d.1 beta v z p := by
-- BODY
  sorry
