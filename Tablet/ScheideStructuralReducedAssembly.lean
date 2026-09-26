import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralReorderingData
import Tablet.ScheideStructuralSelectionData
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideStructuralReducedAssembly]
theorem ScheideStructuralReducedAssembly {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C)
    (T' : TreeSequence G e0)
    (Q : ScheideStructuralReorderingData G k e0 phi T C D T') :
    ∃ R : ScheideReducedConfiguration G k e0 phi T',
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
      (∀ i : Fin C.s,
        (∃ r : Fin R.s, C.gamma i = R.gamma r ∧
          ∀ j : Fin 2, C.blockVertex i j = R.blockVertex r j ∧
            C.blockEdge i j = R.blockEdge r j) ∨
        ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
-- BODY
  let newP := C.p + 2 * D.absorbedCount
  let newS := D.retainedCount
  let newVertex : Fin newP → V := fun q =>
    T'.vertex ⟨q.val, by
      have hq := q.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newGamma : Fin newS → Fin k := fun t => C.gamma (D.retained t)
  let newBlockVertex : Fin newS → Fin 2 → V := fun t j =>
    T'.vertex ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBaseEdge : Fin (newP - 1) → E := fun q =>
    T'.edge ⟨q.val, by
      have hq := q.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBlockEdge : Fin newS → Fin 2 → E := fun t j =>
    T'.edge ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  have oldExitBase : ∀ v ∈ ScheideExitVertices T phi,
      ∃ q : Fin C.p, C.y q = v := by
    intro v hv
    have hstructure := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
    have helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
      hstructure.2.2.2.1
    have hvertex : v ∈ TreeSequenceVertexSet T := by
      letI : DecidablePred (fun w : V => ScheideExitVertex T phi w) := Classical.decPred _
      rcases (Finset.mem_filter.mp hv).2 with ⟨u, color, defect, hu, hmiss, hdefect,
        z, path, hpath, index, hindex, hvertex, hafter⟩
      exact hvertex
    have baseInTree : ∀ q : Fin C.p, C.y q ∈ TreeSequenceVertexSet T := by
      intro q
      have hlength := C.length_eq
      have witness :=
        (@Finset.mem_image (Fin (T.length + 1)) V (Classical.decEq V)).mpr
          (⟨⟨q.val, by omega⟩, Finset.mem_univ _, C.base_vertex_position q⟩ :
            ∃ a ∈ (Finset.univ : Finset (Fin (T.length + 1))), T.vertex a = C.y q)
      simpa only [TreeSequenceVertexSet] using witness
    obtain ⟨colorIndex, hcolor⟩ := C.exit_covered v hv
    obtain ⟨base, hbase⟩ := C.block_color_missing_on_base colorIndex
    have hne : v = C.y base := by
      by_contra hne
      have hdisjoint := helementary hvertex (baseInTree base) hne
      exact (Finset.disjoint_left.mp hdisjoint) hcolor hbase
    exact ⟨base, hne.symm⟩
  let assembled : ScheideReducedConfiguration G k e0 phi T' := {
    p := newP,
    s := newS,
    p_ge_two := by have hp := C.p_ge_two; dsimp [newP]; omega,
    gamma := newGamma,
    gamma_injective := by
      intro a b hab
      apply D.retained_injective
      apply C.gamma_injective
      exact hab,
    y := newVertex,
    baseEdge := newBaseEdge,
    blockVertex := newBlockVertex,
    blockEdge := newBlockEdge,
    length_eq := by
      dsimp [newP, newS]
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega,
    base_vertex_position := by
      intro q
      rfl,
    block_vertex_position := by
      intro t j
      rfl,
    base_edge_position := by
      intro q
      rfl,
    block_edge_position := by
      intro t j
      dsimp [newBlockEdge, newP]
      apply congrArg T'.edge
      apply Fin.ext
      change C.p + 2 * D.absorbedCount - 1 + 2 * t.val + j.val =
        C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val
      have hp := C.p_ge_two
      omega,
    block_attaches_to_base := by
      intro t j
      have h := C.block_attaches_to_base (D.retained t) j
      obtain ⟨q, hq⟩ := h
      let qnew : Fin newP := ⟨q.val, by
        dsimp [newP]
        omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [show newBlockVertex t j = C.blockVertex (D.retained t) j by
        dsimp [newBlockVertex]
        exact Q.retained_vertex_position t j]
      exact hq,
    block_color := by
      intro t j
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      exact C.block_color (D.retained t) j,
    block_color_missing_on_base := by
      intro t
      let v := (D.exitEquiv t).1
      have hv : v ∈ ScheideExitVertices T phi := (D.exitEquiv t).2
      obtain ⟨q, hq⟩ := oldExitBase v hv
      let qnew : Fin newP := ⟨q.val, by dsimp [newP]; omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newGamma t = C.gamma (D.retained t) by rfl]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [hq]
      exact D.retained_missing t,
    initial_nonfirst_avoids_blocks := by
      intro q hq c hc r
      let split : Fin ((C.p - 1) + 2 * D.absorbedCount) := ⟨q.val, by
        dsimp [newP] at q ⊢
        omega⟩
      have core : ∀ n : Fin ((C.p - 1) + 2 * D.absorbedCount),
          1 ≤ n.val → ∀ d : Fin k,
            phi (T'.edge ⟨n.val, by
              have hn := n.isLt
              have hp := C.p_ge_two
              have hl := C.length_eq
              have hd := D.count_eq
              rw [Q.length_eq]
              omega⟩) = some d →
            ∀ r : Fin D.retainedCount, d ≠ C.gamma (D.retained r) := by
        intro n hn d hdedge rr
        refine Fin.addCases ?_ ?_ n hn d hdedge rr
        · intro u hn d hdedge rr
          have hold := Q.base_edge_position u
          change 1 ≤ u.val at hn
          apply C.initial_nonfirst_avoids_blocks u hn d (by
            rw [← hold]
            exact hdedge) (D.retained rr)
        · intro u hn d hdedge rr
          let paired : Fin (D.absorbedCount * 2) :=
            Fin.cast (Nat.mul_comm 2 D.absorbedCount) u
          let h := paired.divNat
          let j := paired.modNat
          have huv : u.val = 2 * h.val + j.val := by
            dsimp [h, j, paired, Fin.divNat, Fin.modNat]
            omega
          have hedge := Q.absorbed_edge_position h j
          have hblock : phi (C.blockEdge (D.absorbedEquiv h).1 j) = some d := by
            rw [← hedge]
            simpa [huv, Nat.add_assoc] using hdedge
          have hcolor := C.block_color (D.absorbedEquiv h).1 j
          have heq : d = C.gamma (D.absorbedEquiv h).1 := by
            rw [hcolor] at hblock
            simpa using hblock.symm
          intro hbad
          apply (D.absorbedEquiv h).2
          refine ⟨rr, ?_⟩
          apply C.gamma_injective
          rw [← heq, hbad]
      apply core split (by exact hq) c
      · simpa [split, newBaseEdge] using hc
    exit_covered := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := (D.exitEquiv.surjective ⟨v, hv⟩)
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_⟩
      rw [← htv]
      exact D.retained_missing t,
    no_isolated := C.no_isolated,
    globally_maximum := by
      refine ⟨C.globally_maximum.1, Q.tashkinov, ?_⟩
      rw [Q.vertex_set_eq]
      exact C.globally_maximum.2.2,
    exit_card_eq := by
      rw [Q.exit_set_eq]
      exact D.exit_count_eq.symm,
    exit_exactly_one := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := D.exitEquiv.surjective ⟨v, hv⟩
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_, ?_⟩
      · rw [← htv]
        exact D.retained_missing t
      · intro t' hm
        apply D.selected_unique t t'
        rw [← htv] at hm
        exact hm,
    every_block_color_at_exit := by
      intro t
      refine ⟨(D.exitEquiv t).1, ?_, ?_⟩
      · rw [Q.exit_set_eq]
        exact (D.exitEquiv t).2
      · exact D.retained_missing t
    }
  refine ⟨assembled, Q.vertex_set_eq, ?_, ?_⟩
  · intro q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨q.val, ?_⟩, ?_⟩
    · have hq := q.isLt
      change q.val < C.p + 2 * D.absorbedCount
      omega
    · dsimp [assembled, newVertex]
      exact Q.base_vertex_position q
  · intro i
    rcases D.partition i with ha | hr
    · obtain ⟨h, hi, _⟩ := ha
      right
      intro j
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨C.p + 2 * h.val + j.val, ?_⟩, ?_⟩
      · change C.p + 2 * h.val + j.val < C.p + 2 * D.absorbedCount
        have hh := h.isLt
        have hj := j.isLt
        omega
      · dsimp [assembled, newVertex]
        rw [Q.absorbed_vertex_position h j]
        rw [hi]
    · obtain ⟨t, ht, _⟩ := hr
      left
      refine ⟨t, ?_, ?_⟩
      · dsimp [assembled, newGamma]
        rw [ht]
      · intro j
        constructor
        · dsimp [assembled, newBlockVertex]
          rw [← ht]
          exact (Q.retained_vertex_position t j).symm
        · dsimp [assembled, newBlockEdge]
          rw [← ht]
          exact (Q.retained_edge_position t j).symm
