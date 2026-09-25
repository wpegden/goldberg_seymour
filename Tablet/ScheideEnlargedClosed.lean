import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedElementary
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairsLaminar
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideStructuralConfiguration
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideEnlargedClosed]
theorem ScheideEnlargedClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetClosed G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  classical
  let VT := TreeSequenceVertexSet T
  let X := ScheideEnlargedVertexSet R
  let Def := DefectiveColors G phi VT
  have htreeClosed : ColoredVertexSetClosed G phi VT :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  unfold ColoredVertexSetClosed at htreeClosed ⊢
  intro f alpha x hf hx hfalpha hmiss
  by_cases hdef : Def.Nonempty
  · have hfEnds : ∃ u ∈ X, ∃ w ∉ X, G.ends f = s(u, w) := by
      simpa [X, BoundaryEdges, Sym2.mem_iff] using hf
    obtain ⟨u, huX, w, hwX, hfends⟩ := hfEnds
    obtain ⟨d, huXd⟩ : ∃ d : {delta // delta ∈ Def},
        u ∈ VT ∪ {(R d).u1, (R d).u2} := by
      by_cases huT : u ∈ VT
      · obtain ⟨delta, hdelta⟩ := hdef
        exact ⟨⟨delta, hdelta⟩, Finset.mem_union_left _ huT⟩
      · have huPairs : u ∈ Finset.univ.biUnion
            (fun d : {delta // delta ∈ Def} => {(R d).u1, (R d).u2}) := by
          simpa [X, VT, Def, ScheideEnlargedVertexSet, huT] using huX
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at huPairs
        obtain ⟨d, hud⟩ := huPairs
        exact ⟨d, Finset.mem_union_right _ hud⟩
    let Xd : Finset V := VT ∪ {(R d).u1, (R d).u2}
    have hXdSub : Xd ⊆ X := by
      intro v hv
      simp only [Xd, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with hvT | hv1 | hv2
      · exact Finset.mem_union_left _ hvT
      · unfold X ScheideEnlargedVertexSet
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨d, Finset.mem_univ _, by simp [hv1]⟩
      · unfold X ScheideEnlargedVertexSet
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨d, Finset.mem_univ _, by simp [hv2]⟩
    have hwXd : w ∉ Xd := fun hw => hwX (hXdSub hw)
    have hfXd : f ∈ BoundaryEdges G Xd := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, huXd, w, hwXd, hfends⟩
    have hclosedD : ColoredVertexSetClosed G phi Xd := by
      unfold ColoredVertexSetClosed
      intro g c v hg hv hgc
      exact ScheideReplacementUnionClosed G k e0 phi T C D d (R d)
        (by simpa only [Xd, VT] using hg)
        (by simpa only [Xd, VT] using hv) hgc
    have hxNotXd : x ∉ Xd := by
      intro hxXd
      exact (hclosedD hfXd hxXd hfalpha) hmiss
    have hxNotT : x ∉ VT := by
      intro hxT
      exact hxNotXd (Finset.mem_union_left _ hxT)
    have hxPairs : x ∈ Finset.univ.biUnion
        (fun d : {delta // delta ∈ Def} => {(R d).u1, (R d).u2}) := by
      simpa [X, VT, Def, ScheideEnlargedVertexSet, hxNotT] using hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hxPairs
    obtain ⟨d', hxd'⟩ := hxPairs
    have hpairsDisjoint : Disjoint ({(R d).u1, (R d).u2} : Finset V)
        ({(R d').u1, (R d').u2} : Finset V) := by
      rcases ScheideReplacementPairsLaminar G k e0 phi T C D R d d' with
        heq | hdisj
      · exfalso
        apply hxNotXd
        apply Finset.mem_union_right
        rw [heq]
        exact hxd'
      · exact hdisj
    let Xd' : Finset V := VT ∪ {(R d').u1, (R d').u2}
    have hXd'Sub : Xd' ⊆ X := by
      intro v hv
      simp only [Xd', Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with hvT | hv1 | hv2
      · exact Finset.mem_union_left _ hvT
      · unfold X ScheideEnlargedVertexSet
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨d', Finset.mem_univ _, by simp [hv1]⟩
      · unfold X ScheideEnlargedVertexSet
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨d', Finset.mem_univ _, by simp [hv2]⟩
    have hwXd' : w ∉ Xd' := fun hw => hwX (hXd'Sub hw)
    have hclosedD' : ColoredVertexSetClosed G phi Xd' := by
      unfold ColoredVertexSetClosed
      intro g c v hg hv hgc
      exact ScheideReplacementUnionClosed G k e0 phi T C D d' (R d')
        (by simpa only [Xd', VT] using hg)
        (by simpa only [Xd', VT] using hv) hgc
    have hxXd' : x ∈ Xd' := Finset.mem_union_right _ hxd'
    have huNotT : u ∉ VT := by
      intro huT
      have hfXd' : f ∈ BoundaryEdges G Xd' := by
        unfold BoundaryEdges
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, Finset.mem_union_left _ huT, w, hwXd', hfends⟩
      exact (hclosedD' hfXd' hxXd' hfalpha) hmiss
    have hud : u ∈ ({(R d).u1, (R d).u2} : Finset V) := by
      simpa [Xd, huNotT] using huXd
    have huNotPairD' : u ∉ ({(R d').u1, (R d').u2} : Finset V) :=
      fun hu' => Finset.disjoint_left.mp hpairsDisjoint hud hu'
    have huNotXd' : u ∉ Xd' := by
      intro hu
      rcases Finset.mem_union.mp hu with huT | huPair
      · exact huNotT huT
      · exact huNotPairD' huPair
    let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    have hy0T : y0 ∈ VT := by
      have hpos : (0 : ℕ) < T.length + 1 := by omega
      have hv := C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
      simpa [y0, VT, TreeSequenceVertexSet] using
        (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
          ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
    have hy0X : y0 ∈ X := hXdSub (Finset.mem_union_left _ hy0T)
    have hy0Xd' : y0 ∈ Xd' := Finset.mem_union_left _ hy0T
    have hy0neX : y0 ≠ x := by
      intro h
      exact hxNotT (h ▸ hy0T)
    have ha0alpha : D.alpha0 ≠ alpha := by
      intro h
      have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
        hy0X hx hy0neX
      exact (Finset.disjoint_left.mp hdisj) D.alpha0_missing_at_y0
        (h ▸ hmiss)
    let K := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
    have havoid := ClosedSetTwoColorComponentAvoidance G phi D.alpha0 alpha
      Xd' u y0 x hclosedD' huNotXd' hy0Xd' hxXd'
      D.alpha0_missing_at_y0 hmiss
    have hKavoidV : ∀ v ∈ Xd', Sum.inl v ∉ K := by
      simpa [K] using havoid.1
    have hKavoidE : ∀ e : E, (∃ v ∈ Xd', Incident G v e) →
        Sum.inr e ∉ K := by
      simpa [K] using havoid.2
    have alphaNotBlock : ∀ i : Fin C.s, alpha ≠ C.gamma i := by
      intro i h
      obtain ⟨q, hq⟩ := C.block_color_missing_on_base i
      have hyqT : C.y q ∈ VT := by
        have hlen := C.length_eq
        have hpos : q.val < T.length + 1 := by omega
        have hv := C.base_vertex_position q
        simpa [VT, TreeSequenceVertexSet] using
          (show ∃ j : Fin (T.length + 1), T.vertex j = C.y q from
            ⟨⟨q.val, hpos⟩, by simpa using hv⟩)
      have hyqX : C.y q ∈ X := hXdSub (Finset.mem_union_left _ hyqT)
      have hyqne : C.y q ≠ x := by
        intro heq
        exact hxNotT (heq ▸ hyqT)
      have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
        hyqX hx hyqne
      exact (Finset.disjoint_left.mp hdisj) hq (h.symm ▸ hmiss)
    have pairDOutsideD' : ∀ v ∈ ({(R d).u1, (R d).u2} : Finset V),
        v ∉ Xd' := by
      intro v hvD hvD'
      simp only [Xd', Finset.mem_union] at hvD'
      rcases hvD' with hvT | hvPair
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hvD
        rcases hvD with rfl | rfl
        · exact (R d).u1_outside hvT
        · exact (R d).u2_outside hvT
      · exact (Finset.disjoint_left.mp hpairsDisjoint) hvD hvPair
    have hf1Boundary : (R d).f1 ∈ BoundaryEdges G Xd' := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(R d).v1, Finset.mem_union_left _
          (Finset.mem_sdiff.mp (R d).v1_in_remainder).1,
        (R d).u1, ?_, (R d).f1_ends⟩
      exact pairDOutsideD' (R d).u1 (by simp)
    have alphaNeDelta : alpha ≠ d.1 := by
      intro h
      exact (hclosedD' hf1Boundary hxXd' (h.symm ▸ (R d).f1_color)) hmiss
    have alpha0NeDelta : D.alpha0 ≠ d.1 := by
      intro h
      exact (hclosedD' hf1Boundary hy0Xd'
        (h.symm ▸ (R d).f1_color)) D.alpha0_missing_at_y0
    have gammaNeDelta : C.gamma (D.gammaIndex d) ≠ d.1 := by
      intro h
      have hnotPresent : C.gamma (D.gammaIndex d) ∉
          PresentColors G phi (D.v0 d) := by
        simpa [MissingColors] using D.gamma_missing_at_v0 d
      apply hnotPresent
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨D.f0 d, ?_, ?_⟩
      · unfold Incident
        rw [D.f0_ends]
        simp
      · exact h.symm ▸ D.f0_color d
    have alpha0NeGamma : D.alpha0 ≠ C.gamma (D.gammaIndex d) :=
      D.alpha0_not_block (D.gammaIndex d)
    have alphaNeGamma : alpha ≠ C.gamma (D.gammaIndex d) :=
      alphaNotBlock (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
    have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d (R d)
    dsimp only at hmaximum
    change IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
      GlobalMaximumTriple G k e0 phiD (R d).replacementTree at hmaximum
    have hfirstOther : ∀ (e : E) (c : Fin k),
        c ≠ C.gamma (D.gammaIndex d) → c ≠ d.1 →
        (phiD e = some c ↔ phi e = some c) := by
      intro e c hcGamma hcDelta
      by_cases he : Sum.inr e ∈ TwoColorComponent G phi
          (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      · by_cases heGamma : phi e = some (C.gamma (D.gammaIndex d))
        · have hvalue : phiD e = some d.1 := by
            simp [phiD, TwoColorComponentSwap, he, heGamma]
          rw [hvalue, heGamma]
          simp [hcGamma.symm, hcDelta.symm]
        · by_cases heDelta : phi e = some d.1
          · have hvalue : phiD e = some (C.gamma (D.gammaIndex d)) := by
              simp [phiD, TwoColorComponentSwap, he, heGamma, heDelta,
                gammaNeDelta.symm]
            rw [hvalue, heDelta]
            simp [hcGamma.symm, hcDelta.symm]
          · simp [phiD, TwoColorComponentSwap, he, heGamma, heDelta]
      · simp [phiD, TwoColorComponentSwap, he]
    have hfirstFixed : ∀ e : E,
        (phiD e = some D.alpha0 ↔ phi e = some D.alpha0) ∧
          (phiD e = some alpha ↔ phi e = some alpha) := by
      intro e
      exact ⟨hfirstOther e D.alpha0 alpha0NeGamma alpha0NeDelta,
        hfirstOther e alpha alphaNeGamma alphaNeDelta⟩
    have hgraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
        TwoColorIncidenceGraph G phi D.alpha0 alpha := by
      ext z z'
      cases z with
      | inl v =>
          cases z' with
          | inl w => simp [TwoColorIncidenceGraph]
          | inr e =>
              simp only [TwoColorIncidenceGraph]
              rw [(hfirstFixed e).1, (hfirstFixed e).2]
      | inr e =>
          cases z' with
          | inl v =>
              simp only [TwoColorIncidenceGraph]
              rw [(hfirstFixed e).1, (hfirstFixed e).2]
          | inr g => simp [TwoColorIncidenceGraph]
    have hcomponent : TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K := by
      change ((TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl u)).supp =
        ((TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl u)).supp
      rw [hgraph]
    have hrepEdgeAvoid : ∀ r : Fin (R d).replacementTree.length,
        Sum.inr ((R d).replacementTree.edge r) ∉ K := by
      intro r
      apply hKavoidE ((R d).replacementTree.edge r)
      have hmem : (R d).replacementTree.edge r ∈
          Finset.univ.image (R d).replacementTree.edge := by simp
      rw [(R d).replacement_edges] at hmem
      rcases Finset.mem_union.mp hmem with hold | hnew
      · have hold' : (R d).replacementTree.edge r ∈
            Finset.univ.image T.edge :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hold).2).2
        obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hold'
        obtain ⟨i, hi⟩ := T.attaches q
        refine ⟨T.vertex q.succ, Finset.mem_union_left _ ?_, ?_⟩
        · simp [VT, TreeSequenceVertexSet]
        · unfold Incident
          rw [← hq, hi]
          simp
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hnew
        rcases hnew with hnew | hnew
        · refine ⟨(R d).v1, Finset.mem_union_left _
              (Finset.mem_sdiff.mp (R d).v1_in_remainder).1, ?_⟩
          unfold Incident
          rw [hnew, (R d).f1_ends]
          simp
        · refine ⟨(R d).v2, Finset.mem_union_left _
              (Finset.mem_sdiff.mp (R d).v2_in_remainder).1, ?_⟩
          unfold Incident
          rw [hnew, (R d).f2_ends]
          simp
    have hrepEdgeAvoidD : ∀ r : Fin (R d).replacementTree.length,
        Sum.inr ((R d).replacementTree.edge r) ∉
          TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      intro r hr
      apply hrepEdgeAvoid r
      rw [← hcomponent]
      exact hr
    have hproper : IsProperEdgeColoring G phi :=
      C.globally_maximum.1.2.2.2.1
    have hbehaviorD := TwoColorComponentSwapMissingBehavior G phi
      (C.gamma (D.gammaIndex d)) d.1 gammaNeDelta hproper
      (Sum.inl (D.v0 d))
    dsimp only at hbehaviorD
    have pairNotMissing : ∀ q ∈ ({(R d).u1, (R d).u2} : Finset V),
        D.alpha0 ∉ MissingColors G phiD q ∧
          alpha ∉ MissingColors G phiD q := by
      intro q hq
      have hqT : q ∉ VT := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact (R d).u1_outside
        · exact (R d).u2_outside
      have hqX : q ∈ X := hXdSub (Finset.mem_union_right _ hq)
      have hy0q : y0 ≠ q := by
        intro h
        exact hqT (h ▸ hy0T)
      have hxq : x ≠ q := by
        intro h
        exact pairDOutsideD' q hq (h ▸ hxXd')
      have ha0Old : D.alpha0 ∉ MissingColors G phi q := by
        intro hqmiss
        have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
          hy0X hqX hy0q
        exact (Finset.disjoint_left.mp hdisj) D.alpha0_missing_at_y0 hqmiss
      have halphaOld : alpha ∉ MissingColors G phi q := by
        intro hqmiss
        have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
          hx hqX hxq
        exact (Finset.disjoint_left.mp hdisj) hmiss hqmiss
      constructor
      · intro hnew
        exact ha0Old ((hbehaviorD.2.2.2 q D.alpha0 alpha0NeGamma
          alpha0NeDelta).mp hnew)
      · intro hnew
        exact halphaOld ((hbehaviorD.2.2.2 q alpha alphaNeGamma
          alphaNeDelta).mp hnew)
    let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
    have hbehaviorPsi := TwoColorComponentSwapMissingBehavior G phiD
      D.alpha0 alpha ha0alpha hmaximum.1 (Sum.inl u)
    dsimp only at hbehaviorPsi
    have pairMissingFixed : ∀ q ∈ ({(R d).u1, (R d).u2} : Finset V),
        MissingColors G psi q = MissingColors G phiD q := by
      intro q hq
      by_cases hqK : Sum.inl q ∈ K
      · have hqKD : Sum.inl q ∈
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
          rw [hcomponent]
          exact hqK
        have hnotOld := pairNotMissing q hq
        have alphaPresent : alpha ∈ PresentColors G phiD q := by
          simpa [MissingColors] using hnotOld.2
        obtain ⟨ea, heaInc, heaColor⟩ := by
          simpa [PresentColors] using alphaPresent
        have heaK : Sum.inr ea ∈
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
          change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
              (Sum.inr ea) =
            (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
              (Sum.inl u)
          have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
              (Sum.inr ea) (Sum.inl q) := by
            simp [TwoColorIncidenceGraph, heaInc, heaColor]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
            hqKD
        have alpha0PresentNew : D.alpha0 ∈ PresentColors G psi q := by
          unfold PresentColors
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨ea, heaInc, ?_⟩
          simp [psi, TwoColorComponentSwap, heaK, heaColor, ha0alpha]
        have alpha0NotNew : D.alpha0 ∉ MissingColors G psi q := by
          simpa [MissingColors] using alpha0PresentNew
        have alpha0Present : D.alpha0 ∈ PresentColors G phiD q := by
          simpa [MissingColors] using hnotOld.1
        obtain ⟨e0, he0Inc, he0Color⟩ := by
          simpa [PresentColors] using alpha0Present
        have he0K : Sum.inr e0 ∈
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
          change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
              (Sum.inr e0) =
            (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
              (Sum.inl u)
          have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
              (Sum.inr e0) (Sum.inl q) := by
            simp [TwoColorIncidenceGraph, he0Inc, he0Color]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
            hqKD
        have alphaPresentNew : alpha ∈ PresentColors G psi q := by
          unfold PresentColors
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨e0, he0Inc, ?_⟩
          simp [psi, TwoColorComponentSwap, he0K, he0Color]
        have alphaNotNew : alpha ∉ MissingColors G psi q := by
          simpa [MissingColors] using alphaPresentNew
        apply Finset.ext
        intro c
        by_cases hc0 : c = D.alpha0
        · subst c
          simp [hnotOld.1, alpha0NotNew]
        · by_cases hca : c = alpha
          · subst c
            simp [hnotOld.2, alphaNotNew]
          · exact hbehaviorPsi.2.2.2 q c hc0 hca
      · apply hbehaviorPsi.1
        rw [hcomponent]
        exact hqK
    have hrepMissingFixed : ∀ q ∈ TreeSequenceVertexSet (R d).replacementTree,
        MissingColors G psi q = MissingColors G phiD q := by
      intro q hq
      rw [(R d).replacement_vertices] at hq
      rcases Finset.mem_union.mp hq with hqOld | hqPair
      · apply hbehaviorPsi.1
        rw [hcomponent]
        apply hKavoidV q
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hqOld).1
      · exact pairMissingFixed q hqPair
    have hrepEdgeFixed : ∀ r : Fin (R d).replacementTree.length,
        psi ((R d).replacementTree.edge r) =
          phiD ((R d).replacementTree.edge r) := by
      intro r
      simp [psi, TwoColorComponentSwap, hrepEdgeAvoidD r]
    have hTashPsi : TashkinovTree G e0 psi (R d).replacementTree := by
      intro r hr
      obtain ⟨i, c, hc, hm⟩ := hmaximum.2.2.2.1 r hr
      refine ⟨i, c, (hrepEdgeFixed r).trans hc, ?_⟩
      rw [hrepMissingFixed]
      · exact hm
      · simp [TreeSequenceVertexSet]
    have hproperPsi : IsProperEdgeColoring G psi :=
      TwoColorComponentSwapProper G phiD D.alpha0 alpha ha0alpha
        hmaximum.1 (Sum.inl u)
    have honePsi : IsOneEdgeUncolored psi e0 := by
      constructor
      · by_cases heK : Sum.inr e0 ∈
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
        · have he0none : phiD e0 = none := hmaximum.2.1.1
          simp [psi, TwoColorComponentSwap, heK, he0none]
        · have he0none : phiD e0 = none := hmaximum.2.1.1
          simp [psi, TwoColorComponentSwap, heK, he0none]
      · intro e he0
        obtain ⟨c, hc⟩ := hmaximum.2.1.2 e he0
        change phiD e = some c at hc
        by_cases heK : Sum.inr e ∈
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
        · by_cases hc0 : c = D.alpha0
          · refine ⟨alpha, ?_⟩
            simp only [psi, TwoColorComponentSwap, heK, if_pos]
            rw [hc0] at hc
            rw [hc]
            simp [ha0alpha]
          · by_cases hca : c = alpha
            · refine ⟨D.alpha0, ?_⟩
              simp only [psi, TwoColorComponentSwap, heK, if_pos]
              rw [hca] at hc
              rw [hc]
              simp
            · refine ⟨c, ?_⟩
              simp only [psi, TwoColorComponentSwap, heK, if_pos]
              rw [hc]
              simp [hc0, hca]
        · refine ⟨c, ?_⟩
          simp only [psi, TwoColorComponentSwap, heK, if_neg]
          exact hc
    have hglobalPsi : GlobalMaximumTriple G k e0 psi (R d).replacementTree := by
      refine ⟨?_, hTashPsi, hmaximum.2.2.2.2⟩
      exact ⟨hmaximum.2.2.1.1, hmaximum.2.2.1.2.1,
        hmaximum.2.2.1.2.2.1, hproperPsi, honePsi⟩
    have hy0Rep : y0 ∈ TreeSequenceVertexSet (R d).replacementTree := by
      have hposOld : (0 : ℕ) < T.length + 1 := by omega
      have hposNew : (0 : ℕ) < (R d).replacementTree.length + 1 := by omega
      have hzeroBound : (0 : ℕ) ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by
        have hp := C.p_ge_two
        omega
      have hvertex : (R d).replacementTree.vertex ⟨0, hposNew⟩ = y0 := by
        calc
          (R d).replacementTree.vertex ⟨0, hposNew⟩ =
              T.vertex ⟨0, hposOld⟩ :=
            (R d).retained_vertices_before 0 hzeroBound hposOld
          _ = y0 := by
            simpa [y0] using C.base_vertex_position
              ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
      simpa [TreeSequenceVertexSet] using
        (show ∃ i : Fin ((R d).replacementTree.length + 1),
            (R d).replacementTree.vertex i = y0 from
          ⟨⟨0, hposNew⟩, hvertex⟩)
    have hrepSubX : TreeSequenceVertexSet (R d).replacementTree ⊆ X := by
      intro v hv
      rw [(R d).replacement_vertices] at hv
      rcases Finset.mem_union.mp hv with hvOld | hvPair
      · exact hXdSub (Finset.mem_union_left _ (Finset.mem_sdiff.mp hvOld).1)
      · exact hXdSub (Finset.mem_union_right _ hvPair)
    have huRep : u ∈ TreeSequenceVertexSet (R d).replacementTree := by
      rw [(R d).replacement_vertices]
      exact Finset.mem_union_right _ hud
    have hwRep : w ∉ TreeSequenceVertexSet (R d).replacementTree :=
      fun hw => hwX (hrepSubX hw)
    have hfRep : f ∈ BoundaryEdges G (TreeSequenceVertexSet (R d).replacementTree) := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, huRep, w, hwRep, hfends⟩
    have hy0MissingD : D.alpha0 ∈ MissingColors G phiD y0 :=
      (hbehaviorD.2.2.2 y0 D.alpha0 alpha0NeGamma alpha0NeDelta).2
        D.alpha0_missing_at_y0
    have hy0MissingPsi : D.alpha0 ∈ MissingColors G psi y0 := by
      rw [hrepMissingFixed y0 hy0Rep]
      exact hy0MissingD
    have hfK : Sum.inr f ∈ K := by
      change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl u)
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, Incident, hfends, hfalpha]
    have hfKD : Sum.inr f ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      rw [hcomponent]
      exact hfK
    have hfalphaD : phiD f = some alpha := (hfirstFixed f).2.2 hfalpha
    have hfalpha0Psi : psi f = some D.alpha0 := by
      simp [psi, TwoColorComponentSwap, hfKD, hfalphaD]
    have hfinalClosed : ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet (R d).replacementTree) :=
      (ScheideGlobalMaximumOrder G k e0 psi (R d).replacementTree
        hglobalPsi).2.2.2.2
    exact (hfinalClosed hfRep hy0Rep hfalpha0Psi) hy0MissingPsi
  · letI : IsEmpty {delta // delta ∈
        DefectiveColors G phi (TreeSequenceVertexSet T)} :=
      ⟨fun d => hdef ⟨d.1, by simpa [Def, VT] using d.2⟩⟩
    have hXeq : X = VT := by
      unfold X ScheideEnlargedVertexSet
      simp [VT]
    exact htreeClosed (by simpa [X, hXeq] using hf)
      (by simpa [X, hXeq] using hx) hfalpha hmiss
