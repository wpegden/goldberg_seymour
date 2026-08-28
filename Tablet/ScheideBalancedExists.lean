import Tablet.ScheideBalancedFromMaxNormal
import Tablet.ScheideNormalisation

-- [TABLET NODE: ScheideBalancedExists]
theorem ScheideBalancedExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k)
      (T' : TreeSequence G e1)
      (N' : NormalGlobalMaximumTriple G k e1 psi T'),
      BalancedGlobalMaximumTriple N' := by
-- BODY
  sorry
