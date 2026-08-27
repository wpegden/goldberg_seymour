import Tablet.IsFullEdgeColoring
import Tablet.IsProperEdgeColoring

-- [TABLET NODE: HasKEdgeColoring]
def HasKEdgeColoring {V E : Type*} (G : LooplessMultigraph V E) (k : ℕ) : Prop :=
-- BODY
  ∃ φ : PartialEdgeColoring E k, IsProperEdgeColoring G φ ∧ IsFullEdgeColoring φ
