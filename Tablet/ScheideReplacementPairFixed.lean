import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideReplacementData

-- [TABLET NODE: ScheideReplacementPairFixed]
theorem ScheideReplacementPairFixed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ f : E, (Incident G R.u1 f ∨ Incident G R.u2 f) →
      TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) f = phi f := by
-- BODY
  sorry
