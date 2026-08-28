import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideGraphHeight

-- [TABLET NODE: BalancedGlobalMaximumTriple]
def BalancedGlobalMaximumTriple {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
    (N : NormalGlobalMaximumTriple G k e0 phi T) : Prop :=
-- BODY
  N.height = ScheideGraphHeight G ∧
    ∀ j : ℕ, ∀ hlow : N.height < 2 * j,
      ∀ hupp : 2 * j < T.length + 1,
        phi (T.edge ⟨2 * j - 2, by omega⟩) =
          phi (T.edge ⟨2 * j - 1, by omega⟩)
