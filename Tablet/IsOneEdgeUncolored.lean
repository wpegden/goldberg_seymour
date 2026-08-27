import Tablet.PartialEdgeColoring

-- [TABLET NODE: IsOneEdgeUncolored]
def IsOneEdgeUncolored {E : Type*} {k : ℕ} (φ : PartialEdgeColoring E k)
    (e0 : E) : Prop :=
-- BODY
  φ e0 = none ∧ ∀ e, e ≠ e0 → ∃ c, φ e = some c
