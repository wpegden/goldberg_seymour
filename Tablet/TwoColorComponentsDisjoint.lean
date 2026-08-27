import Tablet.TwoColorComponent

-- [TABLET NODE: TwoColorComponentsDisjoint]
theorem TwoColorComponentsDisjoint {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (z w : Sum V E) :
    TwoColorComponent G phi alpha beta z = TwoColorComponent G phi alpha beta w ∨
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta w) := by
-- BODY
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  by_cases h : H.connectedComponentMk z = H.connectedComponentMk w
  · left
    simpa [TwoColorComponent, H, h]
  · right
    exact SimpleGraph.pairwise_disjoint_supp_connectedComponent H h
