import Tablet.BoundaryEdges
import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.LooplessMultigraph
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralInternalPair
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideReplacementMissingDeletedInternal]
theorem ScheideReplacementMissingDeletedInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈ MissingColors G phi R.u2) →
      ∃ f : E, phi f = some alpha ∧
        G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1) := by
-- BODY
  classical
  intro alpha hAlpha
  let X := TreeSequenceVertexSet T
  let gamma := C.gamma (D.gammaIndex d)
  let ug0 := C.blockVertex (D.gammaIndex d) 0
  let ug1 := C.blockVertex (D.gammaIndex d) 1
  let Z := X \ {ug0, ug1}
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let XD := TreeSequenceVertexSet R.replacementTree

  have hOriginalOrder :=
    ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hXElementary : ColoredVertexSetElementary G phi X := by
    change ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)
    exact hOriginalOrder.2.2.2.1
  have hXClosed : ColoredVertexSetClosed G phi X := by
    change ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
    exact hOriginalOrder.2.2.2.2
  have hReplacementMaximum :=
    ScheideReplacementMaximum G k e0 phi T C D d R
  have hReplacementGlobal : GlobalMaximumTriple G k e0 phiD R.replacementTree := by
    simpa [phiD, gamma] using hReplacementMaximum.2.2
  have hReplacementOrder :=
    ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hReplacementGlobal
  have hXDElementary : ColoredVertexSetElementary G phiD XD := by
    change ColoredVertexSetElementary G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact hReplacementOrder.2.2.2.1
  have hXDClosed : ColoredVertexSetClosed G phiD XD := by
    change ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact hReplacementOrder.2.2.2.2

  have hug0X : ug0 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 0 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hug1X : ug1 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 1 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hug01 : ug0 ≠ ug1 := by
    intro h
    have hv :=
      (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
  have hy0X : y0 ∈ X := by
    change C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
      TreeSequenceVertexSet T
    rw [← C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩]
    simp [TreeSequenceVertexSet]
  have hy0ne0 : y0 ≠ ug0 := by
    intro h
    have hv :=
      (C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
    have hp := C.p_ge_two
    omega
  have hy0ne1 : y0 ≠ ug1 := by
    intro h
    have hv :=
      (C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
  have hy0Z : y0 ∈ Z := by
    simp [Z, hy0X, hy0ne0, hy0ne1]
  have hy0XD : y0 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    exact Finset.mem_union_left _ (by simpa [X, Z, ug0, ug1] using hy0Z)
  have hu1XD : R.u1 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp
  have hu2XD : R.u2 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp
  have hug0NotXD : ug0 ∉ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_sdiff]
    rintro (⟨-, hpair⟩ | h | h)
    · exact hpair (by simp [ug0])
    · exact R.u1_outside (h ▸ hug0X)
    · exact R.u2_outside (h ▸ hug0X)

  have hf1u1 : Incident G R.u1 R.f1 := by
    change R.u1 ∈ G.ends R.f1
    rw [R.f1_ends]
    simp [Incident]
  have hf2u2 : Incident G R.u2 R.f2 := by
    change R.u2 ∈ G.ends R.f2
    rw [R.f2_ends]
    simp [Incident]
  have hAlphaDelta : alpha ≠ d.1 := by
    intro h
    rcases hAlpha with hAlpha | hAlpha
    · have hnot : alpha ∉ PresentColors G phi R.u1 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨R.f1, hf1u1, by simpa [h] using R.f1_color⟩
    · have hnot : alpha ∉ PresentColors G phi R.u2 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨R.f2, hf2u2, by simpa [h] using R.f2_color⟩
  obtain ⟨fGamma, hfGammaColor, hfGammaEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d R).2
  have hfGammaU1 : Incident G R.u1 fGamma := by
    simp [Incident, hfGammaEnds]
  have hfGammaU2 : Incident G R.u2 fGamma := by
    simp [Incident, hfGammaEnds]
  have hAlphaGamma : alpha ≠ gamma := by
    intro h
    rcases hAlpha with hAlpha | hAlpha
    · have hnot : alpha ∉ PresentColors G phi R.u1 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fGamma, hfGammaU1, by simpa [gamma, h] using hfGammaColor⟩
    · have hnot : alpha ∉ PresentColors G phi R.u2 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fGamma, hfGammaU2, by simpa [gamma, h] using hfGammaColor⟩
  have hGammaDelta : gamma ≠ d.1 := by
    intro h
    have hnot : gamma ∉ PresentColors G phi (D.v0 d) := by
      simpa [MissingColors, gamma] using D.gamma_missing_at_v0 d
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨D.f0 d, ?_, ?_⟩
    · change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp [Incident]
    · simpa [h] using D.f0_color d
  have hAlpha0Gamma : D.alpha0 ≠ gamma := by
    simpa [gamma] using D.alpha0_not_block (D.gammaIndex d)

  have hDeltaBoundary : ∃ f : E,
      f ∈ BoundaryEdges G X ∧ phi f = some d.1 := by
    have hdcard : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
      have hd := (Finset.mem_filter.mp d.2).2
      simpa [DefectiveColor, X] using hd
    have hdnonempty : (BoundaryColorEdges G phi X d.1).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hdcard)
    obtain ⟨f, hf⟩ := hdnonempty
    exact ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
  obtain ⟨fDelta, hfDeltaBoundary, hfDeltaColor⟩ := hDeltaBoundary
  have hDeltaNotMissingY0 : d.1 ∉ MissingColors G phi y0 :=
    hXClosed hfDeltaBoundary hy0X hfDeltaColor
  have hAlpha0Delta : D.alpha0 ≠ d.1 := by
    intro h
    apply hDeltaNotMissingY0
    simpa [y0, h] using D.alpha0_missing_at_y0

  have hPhiDAlpha0 : ∀ f : E,
      phiD f = some D.alpha0 ↔ phi f = some D.alpha0 := by
    intro f
    simp only [phiD, TwoColorComponentSwap]
    by_cases hf : Sum.inr f ∈
        TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
    · by_cases hfg : phi f = some gamma
      · simp only [hf, if_pos, hfg, Option.some.injEq]
        constructor
        · intro h
          exact False.elim (hAlpha0Delta h.symm)
        · intro h
          exact False.elim (hAlpha0Gamma h.symm)
      · by_cases hfd : phi f = some d.1
        · simp [hf, hfg, hfd, hGammaDelta.symm, hAlpha0Gamma,
            hAlpha0Gamma.symm, hAlpha0Delta, hAlpha0Delta.symm]
        · simp [hf, hfg, hfd]
    · simp [hf]
  have hPhiDAlpha : ∀ f : E,
      phiD f = some alpha ↔ phi f = some alpha := by
    intro f
    simp only [phiD, TwoColorComponentSwap]
    by_cases hf : Sum.inr f ∈
        TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
    · by_cases hfg : phi f = some gamma
      · simp only [hf, if_pos, hfg, Option.some.injEq]
        constructor
        · intro h
          exact False.elim (hAlphaDelta h.symm)
        · intro h
          exact False.elim (hAlphaGamma h.symm)
      · by_cases hfd : phi f = some d.1
        · simp [hf, hfg, hfd, hGammaDelta.symm, hAlphaGamma,
            hAlphaGamma.symm, hAlphaDelta, hAlphaDelta.symm]
        · simp [hf, hfg, hfd]
    · simp [hf]
  have hGraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    ext x z
    cases x <;> cases z <;>
      simp [TwoColorIncidenceGraph, hPhiDAlpha0, hPhiDAlpha]

  have hPairMissingFixed : ∀ u : V,
      (u = R.u1 ∨ u = R.u2) →
        MissingColors G phiD u = MissingColors G phi u := by
    intro u hu
    simp only [MissingColors]
    congr 1
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, huf, hfc⟩
      refine ⟨f, huf, ?_⟩
      have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
        rcases hu with rfl | rfl
        · exact Or.inl huf
        · exact Or.inr huf)
      simpa [phiD, gamma] using hfixed.symm.trans hfc
    · rintro ⟨f, huf, hfc⟩
      refine ⟨f, huf, ?_⟩
      have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
        rcases hu with rfl | rfl
        · exact Or.inl huf
        · exact Or.inr huf)
      simpa [phiD, gamma] using hfixed.trans hfc
  have hAlphaD :
      alpha ∈ MissingColors G phiD R.u1 ∨
        alpha ∈ MissingColors G phiD R.u2 := by
    rcases hAlpha with hAlpha | hAlpha
    · exact Or.inl (by
        rw [hPairMissingFixed R.u1 (Or.inl rfl)]
        exact hAlpha)
    · exact Or.inr (by
        rw [hPairMissingFixed R.u2 (Or.inr rfl)]
        exact hAlpha)
  have hAlpha0D : D.alpha0 ∈ MissingColors G phiD y0 := by
    have hOld := D.alpha0_missing_at_y0
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and] at hOld ⊢
    intro hpresent
    apply hOld
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hpresent ⊢
    obtain ⟨f, hyf, hfc⟩ := hpresent
    exact ⟨f, hyf, (hPhiDAlpha0 f).mp hfc⟩
  have hAlphaNeAlpha0 : alpha ≠ D.alpha0 := by
    intro h
    rcases hAlphaD with hAlphaD | hAlphaD
    · have hyu : y0 ≠ R.u1 := by
        intro hyu
        exact R.u1_outside (hyu ▸ hy0X)
      have hdj := hXDElementary hy0XD hu1XD hyu
      exact (Finset.disjoint_left.mp hdj) hAlpha0D (by simpa [h] using hAlphaD)
    · have hyu : y0 ≠ R.u2 := by
        intro hyu
        exact R.u2_outside (hyu ▸ hy0X)
      have hdj := hXDElementary hy0XD hu2XD hyu
      exact (Finset.disjoint_left.mp hdj) hAlpha0D (by simpa [h] using hAlphaD)

  obtain ⟨fAlpha0, hfAlpha0Color, hfAlpha0Ends⟩ :=
    ScheideStructuralInternalPair G k e0 phi T C (D.gammaIndex d) D.alpha0
      (by simpa [gamma] using hAlpha0Gamma)
      ⟨y0, by simpa [X, Z, ug0, ug1] using hy0Z,
        by simpa [y0] using D.alpha0_missing_at_y0⟩
  let K := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0)
  have hug0K : Sum.inl ug0 ∈ K := by
    rfl
  have hfAlpha0Ug0 : Incident G ug0 fAlpha0 := by
    simp [Incident, hfAlpha0Ends, ug0, ug1]
  have hfAlpha0Ug1 : Incident G ug1 fAlpha0 := by
    simp [Incident, hfAlpha0Ends, ug0, ug1]
  have hfAlpha0K : Sum.inr fAlpha0 ∈ K := by
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inr fAlpha0) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl ug0) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0Ug0, hfAlpha0Color]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hug1K : Sum.inl ug1 ∈ K := by
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug1) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl ug1) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0Ug1, hfAlpha0Color]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
      hfAlpha0K

  have hAvoidD :
      (∀ v ∈ XD, Sum.inl v ∉
          TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0)) ∧
        ∀ f : E, (∃ v ∈ XD, Incident G v f) →
          Sum.inr f ∉
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0) := by
    rcases hAlphaD with hAlphaD | hAlphaD
    · exact ClosedSetTwoColorComponentAvoidance G phiD D.alpha0 alpha XD
        ug0 y0 R.u1 hXDClosed hug0NotXD hy0XD hu1XD hAlpha0D hAlphaD
    · exact ClosedSetTwoColorComponentAvoidance G phiD D.alpha0 alpha XD
        ug0 y0 R.u2 hXDClosed hug0NotXD hy0XD hu2XD hAlpha0D hAlphaD
  have hAvoid :
      (∀ v ∈ XD, Sum.inl v ∉ K) ∧
        ∀ f : E, (∃ v ∈ XD, Incident G v f) → Sum.inr f ∉ K := by
    constructor
    · intro v hv hmem
      apply hAvoidD.1 v hv
      change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl v) =
        (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl ug0)
      rw [hGraph]
      exact hmem
    · intro f hf hmem
      apply hAvoidD.2 f hf
      change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl ug0)
      rw [hGraph]
      exact hmem

  let psi := TwoColorComponentSwap G phi D.alpha0 alpha (Sum.inl ug0)
  have hProperPsi : IsProperEdgeColoring G psi := by
    exact TwoColorComponentSwapProper G phi D.alpha0 alpha hAlphaNeAlpha0.symm
      C.globally_maximum.1.2.2.2.1 (Sum.inl ug0)
  have hOnePsi : IsOneEdgeUncolored psi e0 := by
    have hOne := C.globally_maximum.1.2.2.2.2
    constructor
    · simp [psi, TwoColorComponentSwap, hOne.1]
    · intro f hf
      obtain ⟨c, hfc⟩ := hOne.2 f hf
      by_cases hmem : Sum.inr f ∈ K
      · by_cases hc0 : c = D.alpha0
        · exact ⟨alpha, by
            simp [psi, TwoColorComponentSwap, K, hmem, hfc, hc0,
              hAlphaNeAlpha0, hAlphaNeAlpha0.symm]⟩
        · by_cases hca : c = alpha
          · exact ⟨D.alpha0, by
              simp [psi, TwoColorComponentSwap, K, hmem, hfc, hc0, hca,
                hAlphaNeAlpha0, hAlphaNeAlpha0.symm]⟩
          · exact ⟨c, by
              simp [psi, TwoColorComponentSwap, K, hmem, hfc, hc0, hca]⟩
      · exact ⟨c, by
          simp [psi, TwoColorComponentSwap, K, hmem, hfc]⟩

  have hPsiFixedAt : ∀ v : V, v ∈ XD →
      ∀ f : E, Incident G v f → psi f = phi f := by
    intro v hv f hvf
    have hnot := hAvoid.2 f ⟨v, hv, hvf⟩
    simp [psi, K, TwoColorComponentSwap, hnot]
  have hMissingPsiFixed : ∀ v : V, v ∈ XD →
      MissingColors G psi v = MissingColors G phi v := by
    intro v hv
    simp only [MissingColors]
    congr 1
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨f, hvf, hfc⟩
    · exact ⟨f, hvf, (hPsiFixedAt v hv f hvf).symm.trans hfc⟩
    · exact ⟨f, hvf, (hPsiFixedAt v hv f hvf).trans hfc⟩

  have hBaseInZ : ∀ q : Fin C.p, C.y q ∈ Z := by
    intro q
    have hqX : C.y q ∈ X := by
      change C.y q ∈ TreeSequenceVertexSet T
      rw [← C.base_vertex_position q]
      simp [TreeSequenceVertexSet]
    have hq0 : C.y q ≠ ug0 := by
      intro h
      have hv := (C.base_vertex_position q).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).symm)
      have hi := congrArg Fin.val (T.vertex_injective hv)
      simp at hi
      omega
    have hq1 : C.y q ≠ ug1 := by
      intro h
      have hv := (C.base_vertex_position q).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
      have hi := congrArg Fin.val (T.vertex_injective hv)
      simp at hi
      omega
    simp [Z, hqX, hq0, hq1]
  have hZInXD : ∀ v : V, v ∈ Z → v ∈ XD := by
    intro v hv
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    exact Finset.mem_union_left _ (by simpa [X, Z, ug0, ug1] using hv)

  have hTreePsi : TashkinovTree G e0 psi T := by
    intro j hj
    by_cases hbase : j.val < C.p - 1
    · obtain ⟨i, c, hedge, hmissing⟩ := C.globally_maximum.2.1 j hj
      let q : Fin C.p := ⟨i.val, by omega⟩
      have hqVertex : T.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = C.y q := by
        have hind : Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) =
              ⟨q.val, by
                have hq := q.isLt
                have hl := C.length_eq
                omega⟩ := by
          apply Fin.ext
          rfl
        rw [hind]
        exact C.base_vertex_position q
      let next : Fin C.p := ⟨j.val + 1, by omega⟩
      have hnextZ : C.y next ∈ Z := hBaseInZ next
      have hnextVertex : T.vertex j.succ = C.y next := by
        have hind : j.succ = ⟨next.val, by
            have hn := next.isLt
            have hl := C.length_eq
            omega⟩ := by
          apply Fin.ext
          rfl
        rw [hind]
        exact C.base_vertex_position next
      have hedgeIncident : Incident G (C.y next) (T.edge j) := by
        obtain ⟨r, hr⟩ := T.attaches j
        change C.y next ∈ G.ends (T.edge j)
        rw [hr, hnextVertex]
        simp
      have hedgeFixed := hPsiFixedAt (C.y next) (hZInXD _ hnextZ)
        (T.edge j) hedgeIncident
      refine ⟨i, c, ?_, ?_⟩
      · exact hedgeFixed.trans hedge
      · rw [hMissingPsiFixed _ (by
            rw [hqVertex]
            exact hZInXD _ (hBaseInZ q))]
        exact hmissing
    · let r : Fin C.s := ⟨(j.val - (C.p - 1)) / 2, by
          have hj := j.isLt
          have hi := (D.gammaIndex d).isLt
          have hl := C.length_eq
          omega⟩
      let l : Fin 2 := ⟨(j.val - (C.p - 1)) % 2, Nat.mod_lt _ (by omega)⟩
      have hjDecomp : C.p - 1 + 2 * r.val + l.val = j.val := by
        dsimp [r, l]
        have hmod := Nat.mod_add_div (j.val - (C.p - 1)) 2
        omega
      have hedgeEq : T.edge j = C.blockEdge r l := by
        rw [← C.block_edge_position r l]
        apply congrArg T.edge
        apply Fin.ext
        exact hjDecomp.symm
      obtain ⟨q, hends⟩ := C.block_attaches_to_base r l
      have hqZ : C.y q ∈ Z := hBaseInZ q
      have hinc : Incident G (C.y q) (T.edge j) := by
        change C.y q ∈ G.ends (T.edge j)
        rw [hedgeEq, hends]
        simp [Incident]
      have hedgeFixed := hPsiFixedAt (C.y q) (hZInXD _ hqZ) (T.edge j) hinc
      obtain ⟨w, hwMissing⟩ := C.block_color_missing_on_base r
      let i : Fin (j.val + 1) := ⟨w.val, by
        have hw := w.isLt
        omega⟩
      refine ⟨i, C.gamma r, ?_, ?_⟩
      · rw [hedgeFixed, hedgeEq]
        exact C.block_color r l
      · have hvertex : T.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = C.y w := by
          have hind : Fin.castLT i
              (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) =
                ⟨w.val, by
                  have hw := w.isLt
                  have hl := C.length_eq
                  omega⟩ := by
            apply Fin.ext
            rfl
          rw [hind]
          exact C.base_vertex_position w
        rw [hMissingPsiFixed _ (by
          rw [hvertex]
          exact hZInXD _ (hBaseInZ w))]
        rw [hvertex]
        exact hwMissing

  have hGlobalPsi : GlobalMaximumTriple G k e0 psi T := by
    refine ⟨?_, hTreePsi, C.globally_maximum.2.2⟩
    exact ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hProperPsi, hOnePsi⟩
  have hPsiOrder := ScheideGlobalMaximumOrder G k e0 psi T hGlobalPsi
  have hXPsiClosed : ColoredVertexSetClosed G psi X := by
    change ColoredVertexSetClosed G psi (TreeSequenceVertexSet T)
    exact hPsiOrder.2.2.2.2
  have hAlpha0PsiY0 : D.alpha0 ∈ MissingColors G psi y0 := by
    rw [hMissingPsiFixed y0 hy0XD]
    simpa [y0] using D.alpha0_missing_at_y0

  have hAlphaEdgeInK : ∀ x : V, Sum.inl x ∈ K → ∀ f : E,
      Incident G x f → phi f = some alpha → Sum.inr f ∈ K := by
    intro x hx f hxf hcolor
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl x) (Sum.inr f) := by
      simp [TwoColorIncidenceGraph, hxf, hcolor]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hx
  have hAlphaBoundaryZ : ∀ x : V, (x = ug0 ∨ x = ug1) → ∀ f : E,
      Incident G x f → phi f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∈ Z → False := by
    intro x hx f hxf hcolor w hends hwZ
    have hxNotXD : x ∉ XD := by
      rcases hx with rfl | rfl
      · exact hug0NotXD
      · rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
          R.replacement_vertices]
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_sdiff]
        rintro (⟨-, hpair⟩ | h | h)
        · exact hpair (by simp [ug1])
        · exact R.u1_outside (h ▸ hug1X)
        · exact R.u2_outside (h ▸ hug1X)
    have hfBoundary : f ∈ BoundaryEdges G XD := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hZInXD w hwZ, x, hxNotXD, hends.trans Sym2.eq_swap⟩
    have hcolorD : phiD f = some alpha := (hPhiDAlpha f).mpr hcolor
    rcases hAlphaD with hAlphaD | hAlphaD
    · exact (hXDClosed hfBoundary hu1XD hcolorD) hAlphaD
    · exact (hXDClosed hfBoundary hu2XD hcolorD) hAlphaD
  have hAlphaBoundaryOutside : ∀ x : V, (x = ug0 ∨ x = ug1) → ∀ f : E,
      Incident G x f → phi f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∉ X → False := by
    intro x hx f hxf hcolor w hends hwX
    have hxX : x ∈ X := by
      rcases hx with rfl | rfl
      · exact hug0X
      · exact hug1X
    have hfK : Sum.inr f ∈ K := by
      apply hAlphaEdgeInK x
      · rcases hx with rfl | rfl
        · exact hug0K
        · exact hug1K
      · exact hxf
      · exact hcolor
    have hcolorPsi : psi f = some D.alpha0 := by
      simp [psi, K, TwoColorComponentSwap, hfK, hcolor,
        hAlphaNeAlpha0, hAlphaNeAlpha0.symm]
    have hfBoundary : f ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxX, w, hwX, hends⟩
    exact (hXPsiClosed hfBoundary hy0X hcolorPsi) hAlpha0PsiY0

  by_contra hnone
  have hNoIncident : ∀ x : V, (x = ug0 ∨ x = ug1) →
      ∀ f : E, Incident G x f → phi f ≠ some alpha := by
    intro x hx f hxf hcolor
    obtain ⟨w, hends⟩ := Sym2.mem_iff_exists.mp hxf
    have hwne : w ≠ x := by
      intro h
      apply G.loopless f x
      simpa [h] using hends
    by_cases hwZ : w ∈ Z
    · exact hAlphaBoundaryZ x hx f hxf hcolor w hends hwZ
    by_cases hwX : w ∈ X
    · have hwPair : w = ug0 ∨ w = ug1 := by
        have : w ∈ ({ug0, ug1} : Finset V) := by
          by_contra hp
          exact hwZ (by simp [Z, hwX, hp])
        simpa using this
      have hinterior : G.ends f = s(ug0, ug1) := by
        rcases hx with rfl | rfl <;> rcases hwPair with rfl | rfl
        · exact False.elim (hwne rfl)
        · exact hends
        · simpa [Sym2.eq_swap] using hends
        · exact False.elim (hwne rfl)
      exact hnone ⟨f, hcolor, by simpa [ug0, ug1] using hinterior⟩
    · exact hAlphaBoundaryOutside x hx f hxf hcolor w hends hwX
  have hMissingUg0 : alpha ∈ MissingColors G phi ug0 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident ug0 (Or.inl rfl) f hinc hcolor
  have hMissingUg1 : alpha ∈ MissingColors G phi ug1 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident ug1 (Or.inr rfl) f hinc hcolor
  have hdj := hXElementary hug0X hug1X hug01
  exact (Finset.disjoint_left.mp hdj) hMissingUg0 hMissingUg1
