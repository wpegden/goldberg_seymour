import Tablet.AdjacentEdges
import Tablet.PartialEdgeColoring

-- [TABLET NODE: IsProperEdgeColoring]
def IsProperEdgeColoring {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (φ : PartialEdgeColoring E k) : Prop :=
-- BODY
  ∀ ⦃e f c⦄, e ≠ f → AdjacentEdges G e f → φ e = some c → φ f ≠ some c
