import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideReplacementData
import Tablet.ScheideStructuralInternalPair

-- [TABLET NODE: ScheideReplacementFamilyExists]
theorem ScheideReplacementFamilyExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    Nonempty (∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) := by
-- BODY
  sorry
