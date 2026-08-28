import Tablet.IsOneEdgeUncolored
import Tablet.ScheideDefectiveTailExternal
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideDefectiveSwitchEffect]
theorem ScheideDefectiveSwitchEffect {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      let phiD := TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
        phiD (D.f0 d) = some (C.gamma (D.gammaIndex d)) ∧
        MissingColors G phiD (D.v0 d) =
          insert d.1 ((MissingColors G phi (D.v0 d)).erase
            (C.gamma (D.gammaIndex d))) ∧
        (∀ f : E, (∃ v ∈ TreeSequenceVertexSet T, Incident G v f) →
          f ≠ D.f0 d → phiD f = phi f) ∧
        (∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d →
          MissingColors G phiD v = MissingColors G phi v) ∧
        ∀ v : V,
          Sum.inl v ∉ TwoColorComponent G phi
            (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d)) →
          MissingColors G phiD v = MissingColors G phi v := by
-- BODY
  sorry
