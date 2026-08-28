import Tablet.ScheideBalancedExists
import Tablet.TrunkRotation

-- [TABLET NODE: ScheideTrunkRotationPreserves]
theorem ScheideTrunkRotationPreserves {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k)
      (T' : TreeSequence G e1)
      (N' : NormalGlobalMaximumTriple G k e1 psi T'),
      TrunkRotation N j e1 psi T' N' ∧
        BalancedGlobalMaximumTriple N' := by
-- BODY
  sorry
