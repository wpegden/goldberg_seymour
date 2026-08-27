import Tablet.StableColoring
import Tablet.sc1

-- [TABLET NODE: sc2]
theorem sc2 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k)) :
    Equivalence
      (fun phi pi : {psi : PartialEdgeColoring E k //
          IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} =>
        StableColoring T C phi.1 pi.1) := by
-- BODY
  sorry
