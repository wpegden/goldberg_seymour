import Tablet.BalancedGlobalMaximumTriple
import Tablet.AdjacentEdges
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideTrunkRotationCycle
import Tablet.TreeSequence

-- [TABLET NODE: ScheideTrunkRotationColoring]
theorem ScheideTrunkRotationColoring {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) :
    ∃ (psi : PartialEdgeColoring E k) (A B : Fin k),
      A ≠ B ∧
      A = (if Odd j.val then N.beta else N.alpha) ∧
      B = (if Odd j.val then N.alpha else N.beta) ∧
      IsProperEdgeColoring G psi ∧
      IsOneEdgeUncolored psi (NormalCycleEdge N j) ∧
      A ∈ MissingColors G psi
        (T.vertex (Fin.castLE N.height_upper j)) ∧
      B ∈ MissingColors G psi
        (T.vertex (Fin.castLE N.height_upper
          ⟨(j.val + 1) % N.height, by
            exact Nat.mod_lt _ (by
              have hp := N.height_lower
              omega)⟩)) ∧
      (∀ i : Fin j.val,
        psi (NormalCycleEdge N
            (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
          phi (NormalCycleEdge N
            ⟨i.val + 1, by
              have hi := i.isLt
              have hjlt := j.isLt
              omega⟩)) ∧
      (∀ f : E,
        (∀ i : Fin (j.val + 1),
          f ≠ NormalCycleEdge N
            (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
        psi f = phi f) ∧
      ∀ r : Fin T.length, N.height - 1 ≤ r.val →
        psi (T.edge r) = phi (T.edge r) := by
-- BODY
  sorry
