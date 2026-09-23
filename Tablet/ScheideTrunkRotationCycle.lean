import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideGraphHeight
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideTrunkRotationCycle]
theorem ScheideTrunkRotationCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N) :
    3 ≤ N.height ∧ Odd N.height ∧
      Function.Injective (NormalCycleEdge N) ∧
      (∀ i : Fin N.height,
        G.ends (NormalCycleEdge N i) =
          s(T.vertex (Fin.castLE N.height_upper i),
            T.vertex (Fin.castLE N.height_upper
              ⟨(i.val + 1) % N.height, by
                exact Nat.mod_lt _ (by
                  have hp := N.height_lower
                  omega)⟩))) ∧
      ∀ i : Fin N.height, 1 ≤ i.val →
        phi (NormalCycleEdge N i) =
          if Odd i.val then some N.alpha else some N.beta := by
-- BODY
  sorry
