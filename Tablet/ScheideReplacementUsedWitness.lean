import Tablet.MissingColors
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideReplacementData
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideReplacementUsedWitness]
theorem ScheideReplacementUsedWitness {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}) :
    ∀ c ∈ TreeUsedColors
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) (R d).replacementTree,
      ∃ z ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1},
        c ∈ MissingColors G
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) z := by
-- BODY
  sorry
