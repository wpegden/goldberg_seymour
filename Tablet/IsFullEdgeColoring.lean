import Tablet.PartialEdgeColoring

-- [TABLET NODE: IsFullEdgeColoring]
def IsFullEdgeColoring {E : Type*} {k : ℕ} (φ : PartialEdgeColoring E k) : Prop :=
-- BODY
  ∀ e, ∃ c, φ e = some c
