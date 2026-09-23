import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideTrunkRotationCycle
import Tablet.ScheideTrunkRotationTree
import Tablet.TreeSequenceVertexSet
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideTrunkRotationNormal]
theorem ScheideTrunkRotationNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (hAB : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
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
      psi f = phi f)
    (T' : TreeSequence G (NormalCycleEdge N j))
    (hglobal : GlobalMaximumTriple G k (NormalCycleEdge N j) psi T')
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
    (hlength : T'.length = T.length)
    (hvertex : ∀ r : Fin (T'.length + 1), r.val < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.vertex r = T.vertex (Fin.castLE N.height_upper i))
    (hedge : ∀ r : Fin T'.length, r.val + 1 < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.edge r = NormalCycleEdge N i) :
    ∃ N' : NormalGlobalMaximumTriple G k (NormalCycleEdge N j) psi T',
      N'.height = N.height ∧
      N'.alpha = A ∧ N'.beta = B ∧
      ∃ pred : Fin N.height,
        pred.val = (j.val + N.height - 1) % N.height ∧
          N'.closingEdge = NormalCycleEdge N pred := by
-- BODY
  sorry
