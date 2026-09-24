import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideHeightFiveGammaEdges
import Tablet.ScheideHeightFiveOutsideLinks
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideTrunkRotationPreserves
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideOrderNineBlockStructure]
theorem ScheideOrderNineBlockStructure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (horder : TashkinovOrder G = 9)
    (hgraphHeight : ScheideGraphHeight G = 5) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1)
      (M : NormalGlobalMaximumTriple G k e1 psi S),
      ∃ (_ : BalancedGlobalMaximumTriple M) (_ : S.length = 8)
        (_ : M.height = 5) (gamma : Fin 2 → Fin k),
      Function.Injective gamma ∧
      (∀ (i : Fin 2) (j : Fin 2),
        ∃ q : Fin 5,
          G.ends (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
            s(S.vertex ⟨q.val, by omega⟩,
              S.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (∀ (i : Fin 2) (j : Fin 2),
        psi (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
          some (gamma i)) ∧
      (∀ i : Fin 2, ∃ q : Fin 5,
        gamma i ∈ MissingColors G psi (S.vertex ⟨q.val, by omega⟩)) ∧
      (∀ i : Fin 4, 1 ≤ i.val →
        ∀ c : Fin k, psi (S.edge ⟨i.val, by omega⟩) = some c →
          ∀ r : Fin 2, c ≠ gamma r) := by
-- BODY
  sorry
