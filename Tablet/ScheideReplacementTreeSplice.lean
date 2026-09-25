import Tablet.ScheideDefectiveSetup
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

open scoped Sym2

-- [TABLET NODE: ScheideReplacementTreeSplice]
theorem ScheideReplacementTreeSplice {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f1 f2 : E) (v1 v2 u1 u2 : V),
      f1 ≠ f2 → u1 ≠ u2 →
      v1 ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} →
      v2 ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} →
      u1 ∉ TreeSequenceVertexSet T → u2 ∉ TreeSequenceVertexSet T →
      G.ends f1 = s(v1, u1) → G.ends f2 = s(v2, u2) →
      ∃ replacementTree : TreeSequence G e0,
        ∃ replacement_length : replacementTree.length = T.length,
        (∀ q : ℕ,
          q < C.p - 1 + 2 * (D.gammaIndex d).val →
          ∀ hq : q < T.length,
            replacementTree.edge ⟨q, by omega⟩ = T.edge ⟨q, hq⟩) ∧
        (∀ q : ℕ,
          q ≤ C.p - 1 + 2 * (D.gammaIndex d).val →
          ∀ hq : q < T.length + 1,
            replacementTree.vertex ⟨q, by omega⟩ = T.vertex ⟨q, hq⟩) ∧
        (∀ q : ℕ,
          C.p - 1 + 2 * (D.gammaIndex d).val ≤ q →
          ∀ hq : q + 2 < T.length,
            replacementTree.edge ⟨q, by omega⟩ = T.edge ⟨q + 2, hq⟩) ∧
        (∀ q : ℕ,
          C.p - 1 + 2 * (D.gammaIndex d).val < q →
          ∀ hq : q + 2 < T.length + 1,
            replacementTree.vertex ⟨q, by omega⟩ = T.vertex ⟨q + 2, hq⟩) ∧
        (replacementTree.edge ⟨T.length - 2, by
            have hi := (D.gammaIndex d).isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hl := replacement_length
            omega⟩ = f1 ∧
          replacementTree.edge ⟨T.length - 1, by
            have hi := (D.gammaIndex d).isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hl := replacement_length
            omega⟩ = f2) ∧
        (replacementTree.vertex ⟨T.length - 1, by
            have hi := (D.gammaIndex d).isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hl := replacement_length
            omega⟩ = u1 ∧
          replacementTree.vertex ⟨T.length, by
            have hl := replacement_length
            omega⟩ = u2) ∧
        TreeSequenceVertexSet replacementTree =
          (TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) 0,
              C.blockVertex (D.gammaIndex d) 1}) ∪ {u1, u2} ∧
        Finset.univ.image replacementTree.edge =
          (((Finset.univ.image T.edge).erase
            (C.blockEdge (D.gammaIndex d) 0)).erase
              (C.blockEdge (D.gammaIndex d) 1)) ∪ {f1, f2} := by
-- BODY
  sorry
