import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Tablet.Incident
import Tablet.PartialEdgeColoring

-- [TABLET NODE: TwoColorIncidenceGraph]
def TwoColorIncidenceGraph {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) :
    SimpleGraph (Sum V E) where
-- BODY
  Adj x y :=
    match x, y with
    | Sum.inl v, Sum.inr e =>
        Incident G v e ∧ (phi e = some alpha ∨ phi e = some beta)
    | Sum.inr e, Sum.inl v =>
        Incident G v e ∧ (phi e = some alpha ∨ phi e = some beta)
    | _, _ => False
  symm.symm := by
    intro x y
    cases x <;> cases y <;> simp_all
  loopless.irrefl := by
    intro x
    cases x <;> simp
