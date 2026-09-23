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
import Tablet.ScheideTrunkRotationColoring
import Tablet.ScheideTrunkRotationNormal
import Tablet.ScheideTrunkRotationTree
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorIncidenceGraph

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
  classical
  obtain ⟨psi, A, B, hAB, hA, hB, hproper, hone, hmissA, hmissB,
      hshift, hfixed, htailColor⟩ :=
    ScheideTrunkRotationColoring G k e0 phi T N hbalanced j hj
  obtain ⟨T', hglobal, hlength, hvertices, htrunkVertices,
      htailVertices, htrunkEdges, htailEdges⟩ :=
    ScheideTrunkRotationTree G k e0 phi psi T N hbalanced j hj A B hAB
      hA hB hproper hone hmissA hmissB hshift hfixed
  obtain ⟨N', hheight, halpha, hbeta, pred, hpred, hclosing⟩ :=
    ScheideTrunkRotationNormal G k e0 phi psi T N hbalanced j hj A B
      hAB hA hB hshift hfixed T' hglobal hmissA hmissB hlength
      htrunkVertices htrunkEdges
  refine ⟨NormalCycleEdge N j, psi, T', N', ?_, ?_⟩
  · exact ⟨hj, rfl, hone.1, hshift, hfixed, hlength, hheight,
      hvertices, htrunkVertices, htailVertices, htrunkEdges,
      htailEdges, pred, hpred, hclosing⟩
  · constructor
    · rw [hheight]
      exact hbalanced.1
    · intro q hlow hupp
      have hlow' : N.height < 2 * q := by
        rw [hheight] at hlow
        exact hlow
      have hupp' : 2 * q < T.length + 1 := by
        rw [hlength] at hupp
        exact hupp
      let r1 : Fin T'.length := ⟨2 * q - 2, by omega⟩
      let r2 : Fin T'.length := ⟨2 * q - 1, by omega⟩
      have hr1 : N.height - 1 ≤ r1.val := by
        dsimp [r1]
        omega
      have hr2 : N.height - 1 ≤ r2.val := by
        dsimp [r2]
        omega
      obtain ⟨s1, hs1val, hs1edge⟩ := htailEdges r1 hr1
      obtain ⟨s2, hs2val, hs2edge⟩ := htailEdges r2 hr2
      have hs1tail : N.height - 1 ≤ s1.val := by omega
      have hs2tail : N.height - 1 ≤ s2.val := by omega
      have hs1eq : s1 = (⟨2 * q - 2, by omega⟩ : Fin T.length) := by
        apply Fin.ext
        simpa [r1] using hs1val
      have hs2eq : s2 = (⟨2 * q - 1, by omega⟩ : Fin T.length) := by
        apply Fin.ext
        simpa [r2] using hs2val
      change psi (T'.edge r1) = psi (T'.edge r2)
      calc
        psi (T'.edge r1) = psi (T.edge s1) := congrArg psi hs1edge
        _ = phi (T.edge s1) := htailColor s1 hs1tail
        _ = phi (T.edge s2) := by
          rw [hs1eq, hs2eq]
          exact hbalanced.2 q hlow' hupp'
        _ = psi (T.edge s2) := (htailColor s2 hs2tail).symm
        _ = psi (T'.edge r2) := congrArg psi hs2edge.symm
