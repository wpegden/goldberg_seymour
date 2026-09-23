import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideTrunkRotationColoring
import Tablet.ScheideTrunkRotationCycle
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideTrunkRotationTree]
theorem ScheideTrunkRotationTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (hAB : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
    (hproper : IsProperEdgeColoring G psi)
    (hone : IsOneEdgeUncolored psi (NormalCycleEdge N j))
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
    (hshift : ∀ i : Fin j.val,
      psi (NormalCycleEdge N
          (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        phi (NormalCycleEdge N
          ⟨i.val + 1, by
            have hi := i.isLt
            have hjlt := j.isLt
            omega⟩))
    (hfixed : ∀ f : E,
      (∀ i : Fin (j.val + 1),
        f ≠ NormalCycleEdge N
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
      psi f = phi f) :
    ∃ T' : TreeSequence G (NormalCycleEdge N j),
      GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' ∧
      T'.length = T.length ∧
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ r : Fin (T'.length + 1), r.val < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.vertex r = T.vertex (Fin.castLE N.height_upper i)) ∧
      (∀ r : Fin (T'.length + 1), N.height ≤ r.val →
        ∃ s : Fin (T.length + 1),
          s.val = r.val ∧ T'.vertex r = T.vertex s) ∧
      (∀ r : Fin T'.length, r.val + 1 < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.edge r = NormalCycleEdge N i) ∧
      ∀ r : Fin T'.length, N.height - 1 ≤ r.val →
        ∃ s : Fin T.length,
          s.val = r.val ∧ T'.edge r = T.edge s := by
-- BODY
  sorry
