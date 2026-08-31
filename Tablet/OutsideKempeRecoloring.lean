import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent

-- [TABLET NODE: OutsideKempeRecoloring]
def OutsideKempeRecoloring {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k)
    (alpha beta : Fin k) : Prop := by
-- BODY
  classical
  exact alpha ≠ beta ∧
    ∃ roots : Finset (Sum V E),
      (∀ z ∈ roots, ∀ v : V,
        Sum.inl v ∈ TwoColorComponent G phi alpha beta z →
        v ∉ TreeSequenceVertexSet T) ∧
      ∀ f : E,
        sigma f =
          if ∃ z ∈ roots,
              Sum.inr f ∈ TwoColorComponent G phi alpha beta z then
            if phi f = some alpha then some beta
            else if phi f = some beta then some alpha
            else phi f
          else phi f
