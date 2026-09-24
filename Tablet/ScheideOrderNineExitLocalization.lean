import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideOrderNineExitLocalization]
theorem ScheideOrderNineExitLocalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (hlength : T.length = 8) (hheight : N.height = 5)
    (gamma : Fin 2 → Fin k)
    (hgamma : Function.Injective gamma)
    (hblockColor : ∀ (i : Fin 2) (j : Fin 2),
      phi (T.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
        some (gamma i))
    (hblockMissing : ∀ i : Fin 2, ∃ q : Fin 5,
      gamma i ∈ MissingColors G phi (T.vertex ⟨q.val, by omega⟩))
    (hbaseAvoids : ∀ i : Fin 4, 1 ≤ i.val →
      ∀ c : Fin k, phi (T.edge ⟨i.val, by omega⟩) = some c →
        ∀ r : Fin 2, c ≠ gamma r) :
    ∀ v ∈ ScheideExitVertices T phi,
      ∃ i : Fin 2, gamma i ∈ MissingColors G phi v := by
-- BODY
  sorry
