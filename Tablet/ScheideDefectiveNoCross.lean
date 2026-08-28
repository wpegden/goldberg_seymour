import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumUnused
import Tablet.ScheideStructuralInternalPair
import Tablet.OutsideTreeColorSwap
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideDefectiveNoCross]
theorem ScheideDefectiveNoCross {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      ∀ f : E, phi f = some d.1 →
        ¬ (∃ x ∈ ({C.blockVertex (D.gammaIndex d) 0,
                    C.blockVertex (D.gammaIndex d) 1} : Finset V),
          Incident G x f ∧
            ∃ z ∈ TreeSequenceVertexSet T \
                {C.blockVertex (D.gammaIndex d) 0,
                  C.blockVertex (D.gammaIndex d) 1}, Incident G z f) := by
-- BODY
  sorry
