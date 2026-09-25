import Tablet.BoundaryEdges
import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.LooplessMultigraph
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReplacementInternalMissing
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairFixed
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideDeletedMissingReplacementInternal]
theorem ScheideDeletedMissingReplacementInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨
        alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 1)) →
      ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
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
  have hu12 : R.u1 ≠ R.u2 := by
    intro h
    have hi := R.replacementTree.vertex_injective
      (R.replacement_last_vertices.1.trans
        (h.trans R.replacement_last_vertices.2.symm))
    have hv : T.length - 1 = T.length := by
      simpa using congrArg Fin.val hi
    have ht := T.positive
    omega

  have hAlphaGamma : alpha ≠ gamma := by
    intro h
    rcases hAlpha with hAlpha | hAlpha
    · have hnot : alpha ∉ PresentColors G phi ug0 := by
        simpa [MissingColors] using hAlpha
      obtain ⟨q, hends⟩ := C.block_attaches_to_base (D.gammaIndex d) (0 : Fin 2)
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨C.blockEdge (D.gammaIndex d) 0, ?_, ?_⟩
      · change ug0 ∈ G.ends (C.blockEdge (D.gammaIndex d) 0)
        rw [hends]
        simp [ug0, Incident]
      · simpa [gamma, h] using C.block_color (D.gammaIndex d) (0 : Fin 2)
    · have hnot : alpha ∉ PresentColors G phi ug1 := by
        simpa [MissingColors] using hAlpha
      obtain ⟨q, hends⟩ := C.block_attaches_to_base (D.gammaIndex d) (1 : Fin 2)
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨C.blockEdge (D.gammaIndex d) 1, ?_, ?_⟩
      · change ug1 ∈ G.ends (C.blockEdge (D.gammaIndex d) 1)
        rw [hends]
        simp [ug1, Incident]
      · simpa [gamma, h] using C.block_color (D.gammaIndex d) (1 : Fin 2)
  obtain ⟨fDeltaPair, hfDeltaPairColor, hfDeltaPairEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d R).1
  have hfDeltaUg0 : Incident G ug0 fDeltaPair := by
    simp [Incident, hfDeltaPairEnds, ug0, ug1]
  have hfDeltaUg1 : Incident G ug1 fDeltaPair := by
    simp [Incident, hfDeltaPairEnds, ug0, ug1]
  have hAlphaDelta : alpha ≠ d.1 := by
    intro h
    rcases hAlpha with hAlpha | hAlpha
    · have hnot : alpha ∉ PresentColors G phi ug0 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fDeltaPair, hfDeltaUg0, by simpa [h] using hfDeltaPairColor⟩
    · have hnot : alpha ∉ PresentColors G phi ug1 := by
        simpa [MissingColors] using hAlpha
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fDeltaPair, hfDeltaUg1, by simpa [h] using hfDeltaPairColor⟩
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
    rcases hAlpha with hAlpha | hAlpha
    · have hdj := hXElementary hy0X hug0X hy0ne0
      exact (Finset.disjoint_left.mp hdj)
        (by simpa [y0] using D.alpha0_missing_at_y0) (by simpa [h] using hAlpha)
    · have hdj := hXElementary hy0X hug1X hy0ne1
      exact (Finset.disjoint_left.mp hdj)
        (by simpa [y0] using D.alpha0_missing_at_y0) (by simpa [h] using hAlpha)

  obtain ⟨fAlpha0, hfAlpha0Color, hfAlpha0Ends⟩ :=
    ScheideReplacementInternalMissing G k e0 phi T C D d R D.alpha0
      (by simpa [gamma] using hAlpha0Gamma)
      ⟨y0, by simpa [X, Z, ug0, ug1] using hy0Z,
        by simpa [y0] using D.alpha0_missing_at_y0⟩
  have hfAlpha0DColor : phiD fAlpha0 = some D.alpha0 := by
    have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R fAlpha0
      (Or.inl (by simp [Incident, hfAlpha0Ends]))
    simpa [phiD, gamma] using hfixed.trans hfAlpha0Color
  let K := TwoColorComponent G phiD D.alpha0 alpha (Sum.inl R.u1)
  have hu1K : Sum.inl R.u1 ∈ K := by
    rfl
  have hfAlpha0U1 : Incident G R.u1 fAlpha0 := by
    simp [Incident, hfAlpha0Ends]
  have hfAlpha0U2 : Incident G R.u2 fAlpha0 := by
    simp [Incident, hfAlpha0Ends]
  have hfAlpha0K : Sum.inr fAlpha0 ∈ K := by
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inr fAlpha0) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl R.u1)
    have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
        (Sum.inl R.u1) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0U1, hfAlpha0DColor]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hu2K : Sum.inl R.u2 ∈ K := by
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl R.u2) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl R.u1)
    have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
        (Sum.inl R.u2) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0U2, hfAlpha0DColor]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
      hfAlpha0K

  have hAvoidOld :
      (∀ v ∈ X, Sum.inl v ∉
          TwoColorComponent G phi D.alpha0 alpha (Sum.inl R.u1)) ∧
        ∀ f : E, (∃ v ∈ X, Incident G v f) →
          Sum.inr f ∉
            TwoColorComponent G phi D.alpha0 alpha (Sum.inl R.u1) := by
    rcases hAlpha with hAlpha | hAlpha
    · exact ClosedSetTwoColorComponentAvoidance G phi D.alpha0 alpha X
        R.u1 y0 ug0 hXClosed R.u1_outside hy0X hug0X
        (by simpa [y0] using D.alpha0_missing_at_y0) hAlpha
    · exact ClosedSetTwoColorComponentAvoidance G phi D.alpha0 alpha X
        R.u1 y0 ug1 hXClosed R.u1_outside hy0X hug1X
        (by simpa [y0] using D.alpha0_missing_at_y0) hAlpha
  have hAvoid :
      (∀ v ∈ X, Sum.inl v ∉ K) ∧
        ∀ f : E, (∃ v ∈ X, Incident G v f) → Sum.inr f ∉ K := by
    constructor
    · intro v hv hmem
      apply hAvoidOld.1 v hv
      change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl v) =
        (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl R.u1)
      rw [← hGraph]
      exact hmem
    · intro f hf hmem
      apply hAvoidOld.2 f hf
      change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl R.u1)
      rw [← hGraph]
      exact hmem

  let theta := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl R.u1)
  have hProperTheta : IsProperEdgeColoring G theta := by
    exact TwoColorComponentSwapProper G phiD D.alpha0 alpha hAlphaNeAlpha0.symm
      hReplacementMaximum.1 (Sum.inl R.u1)
  have hOneTheta : IsOneEdgeUncolored theta e0 := by
    have hOne : IsOneEdgeUncolored phiD e0 := by
      simpa [phiD, gamma] using hReplacementMaximum.2.1
    constructor
    · simp [theta, TwoColorComponentSwap, hOne.1]
    · intro f hf
      obtain ⟨c, hfc⟩ := hOne.2 f hf
      by_cases hmem : Sum.inr f ∈ K
      · by_cases hc0 : c = D.alpha0
        · exact ⟨alpha, by
            simp [theta, TwoColorComponentSwap, K, hmem, hfc, hc0,
              hAlphaNeAlpha0, hAlphaNeAlpha0.symm]⟩
        · by_cases hca : c = alpha
          · exact ⟨D.alpha0, by
              simp [theta, TwoColorComponentSwap, K, hmem, hfc, hc0, hca,
                hAlphaNeAlpha0, hAlphaNeAlpha0.symm]⟩
          · exact ⟨c, by
              simp [theta, TwoColorComponentSwap, K, hmem, hfc, hc0, hca]⟩
      · exact ⟨c, by
          simp [theta, TwoColorComponentSwap, K, hmem, hfc]⟩
  have hThetaFixedAtX : ∀ v : V, v ∈ X →
      ∀ f : E, Incident G v f → theta f = phiD f := by
    intro v hv f hvf
    have hnot := hAvoid.2 f ⟨v, hv, hvf⟩
    simp [theta, K, TwoColorComponentSwap, hnot]
  have hMissingThetaFixed : ∀ v : V, v ∈ X →
      MissingColors G theta v = MissingColors G phiD v := by
    intro v hv
    simp only [MissingColors]
    congr 1
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨f, hvf, hfc⟩
    · exact ⟨f, hvf, (hThetaFixedAtX v hv f hvf).symm.trans hfc⟩
    · exact ⟨f, hvf, (hThetaFixedAtX v hv f hvf).trans hfc⟩

  have hReplacementEdgeIncidentX : ∀ j : Fin R.replacementTree.length,
      ∃ v ∈ X, Incident G v (R.replacementTree.edge j) := by
    intro j
    have hjmem : R.replacementTree.edge j ∈
        Finset.univ.image R.replacementTree.edge := by
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [R.replacement_edges] at hjmem
    rcases Finset.mem_union.mp hjmem with hold | hnew
    · have holdImage : R.replacementTree.edge j ∈ Finset.univ.image T.edge :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hold).2).2
      obtain ⟨q, -, hq⟩ := Finset.mem_image.mp holdImage
      obtain ⟨i, hi⟩ := T.attaches q
      refine ⟨T.vertex q.succ, ?_, ?_⟩
      · simp [X, TreeSequenceVertexSet]
      · change T.vertex q.succ ∈ G.ends (R.replacementTree.edge j)
        rw [← hq, hi]
        simp [Incident]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hnew
      rcases hnew with hnew | hnew
      · refine ⟨R.v1, ?_, ?_⟩
        · exact (Finset.mem_sdiff.mp R.v1_in_remainder).1
        · change R.v1 ∈ G.ends (R.replacementTree.edge j)
          rw [hnew, R.f1_ends]
          simp [Incident]
      · refine ⟨R.v2, ?_, ?_⟩
        · exact (Finset.mem_sdiff.mp R.v2_in_remainder).1
        · change R.v2 ∈ G.ends (R.replacementTree.edge j)
          rw [hnew, R.f2_ends]
          simp [Incident]

  have hEffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp at hEffect
  have hTreeTheta : TashkinovTree G e0 theta R.replacementTree := by
    intro j hj
    have hlen : R.replacementTree.length = T.length := R.replacement_length
    by_cases hbefore : j.val + 2 < T.length
    · obtain ⟨i, c, hedge, hmissing⟩ := hReplacementGlobal.2.1 j hj
      obtain ⟨v, hvX, hvEdge⟩ := hReplacementEdgeIncidentX j
      refine ⟨i, c, ?_, ?_⟩
      · exact (hThetaFixedAtX v hvX _ hvEdge).trans hedge
      · let w := R.replacementTree.vertex
          (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))
        have hwXD : w ∈ XD := by
          simp [w, XD, TreeSequenceVertexSet]
        have hwX : w ∈ X := by
          rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
            R.replacement_vertices] at hwXD
          rcases Finset.mem_union.mp hwXD with hwZ | hwPair
          · exact (Finset.mem_sdiff.mp hwZ).1
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
            rcases hwPair with hw1 | hw2
            · have hw1' : R.replacementTree.vertex
                  (Fin.castLT i (Nat.lt_trans i.isLt
                    (Nat.succ_lt_succ j.isLt))) = R.u1 := by
                simpa [w] using hw1
              have hind := R.replacementTree.vertex_injective
                  (hw1'.trans R.replacement_last_vertices.1.symm)
              have hiv := congrArg Fin.val hind
              change i.val = T.length - 1 at hiv
              have hi := i.isLt
              omega
            · have hw2' : R.replacementTree.vertex
                  (Fin.castLT i (Nat.lt_trans i.isLt
                    (Nat.succ_lt_succ j.isLt))) = R.u2 := by
                simpa [w] using hw2
              have hind := R.replacementTree.vertex_injective
                  (hw2'.trans R.replacement_last_vertices.2.symm)
              have hiv := congrArg Fin.val hind
              change i.val = T.length at hiv
              have hi := i.isLt
              omega
        rw [hMissingThetaFixed w hwX]
        exact hmissing
    · have hbaseMem :=
          (ScheideStructuralExitsInBase G k e0 phi T C) (D.v0_is_exit d)
      obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp hbaseMem
      have haLt := a.isLt
      have hbound : a.val ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by
        omega
      have haTree : a.val < T.length + 1 := by
        have hc := C.length_eq
        omega
      have hvbase : T.vertex ⟨a.val, haTree⟩ = D.v0 d := by
        rw [C.base_vertex_position a]
        exact hva
      have hv0X : D.v0 d ∈ X := by
        rw [← hva]
        change C.y a ∈ TreeSequenceVertexSet T
        rw [← C.base_vertex_position a]
        simp [TreeSequenceVertexSet]
      have hmissD : d.1 ∈ MissingColors G phiD (D.v0 d) := by
        change d.1 ∈ MissingColors G
          (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
            (Sum.inl (D.v0 d))) (D.v0 d)
        rw [hEffect.2.2.2.1]
        simp
      have hmissTheta : d.1 ∈ MissingColors G theta (D.v0 d) := by
        rw [hMissingThetaFixed (D.v0 d) hv0X]
        exact hmissD
      have hf1D : phiD R.f1 = some d.1 := by
        have hp := ScheideReplacementPairFixed G k e0 phi T C D d R R.f1
          (Or.inl (by
            change R.u1 ∈ G.ends R.f1
            rw [R.f1_ends]
            simp [Incident]))
        simpa [phiD, gamma] using hp.trans R.f1_color
      have hf2D : phiD R.f2 = some d.1 := by
        have hp := ScheideReplacementPairFixed G k e0 phi T C D d R R.f2
          (Or.inr (by
            change R.u2 ∈ G.ends R.f2
            rw [R.f2_ends]
            simp [Incident]))
        simpa [phiD, gamma] using hp.trans R.f2_color
      have hf1Theta : theta R.f1 = some d.1 := by
        have hv1X : R.v1 ∈ X := (Finset.mem_sdiff.mp R.v1_in_remainder).1
        have hv1f : Incident G R.v1 R.f1 := by
          change R.v1 ∈ G.ends R.f1
          rw [R.f1_ends]
          simp [Incident]
        exact (hThetaFixedAtX R.v1 hv1X R.f1 hv1f).trans hf1D
      have hf2Theta : theta R.f2 = some d.1 := by
        have hv2X : R.v2 ∈ X := (Finset.mem_sdiff.mp R.v2_in_remainder).1
        have hv2f : Incident G R.v2 R.f2 := by
          change R.v2 ∈ G.ends R.f2
          rw [R.f2_ends]
          simp [Incident]
        exact (hThetaFixedAtX R.v2 hv2X R.f2 hv2f).trans hf2D
      have hjlast : j.val = T.length - 2 ∨ j.val = T.length - 1 := by
        have hjlt := j.isLt
        omega
      rcases hjlast with hjlast | hjlast
      · have haearly : a.val < j.val + 1 := by
          have hc := C.length_eq
          omega
        refine ⟨⟨a.val, haearly⟩, d.1, ?_, ?_⟩
        · rw [show R.replacementTree.edge j =
              R.replacementTree.edge ⟨T.length - 2, by rw [← hlen]; omega⟩ by
                apply congrArg R.replacementTree.edge
                apply Fin.ext
                omega]
          rw [R.replacement_last_edges.1]
          exact hf1Theta
        · have hvrep := R.retained_vertices_before a.val hbound (by omega)
          have hidx : (⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega) =
              (⟨a.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
          rw [hidx, hvrep, hvbase]
          exact hmissTheta
      · have haearly : a.val < j.val + 1 := by
          have hc := C.length_eq
          omega
        refine ⟨⟨a.val, haearly⟩, d.1, ?_, ?_⟩
        · rw [show R.replacementTree.edge j =
              R.replacementTree.edge ⟨T.length - 1, by rw [← hlen]; omega⟩ by
                apply congrArg R.replacementTree.edge
                apply Fin.ext
                omega]
          rw [R.replacement_last_edges.2]
          exact hf2Theta
        · have hvrep := R.retained_vertices_before a.val hbound (by omega)
          have hidx : (⟨a.val, haearly⟩ : Fin (j.val + 1)).castLT (by omega) =
              (⟨a.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
          rw [hidx, hvrep, hvbase]
          exact hmissTheta

  have hGlobalTheta : GlobalMaximumTriple G k e0 theta R.replacementTree := by
    refine ⟨?_, hTreeTheta, hReplacementGlobal.2.2⟩
    exact ⟨hReplacementGlobal.1.1, hReplacementGlobal.1.2.1,
      hReplacementGlobal.1.2.2.1, hProperTheta, hOneTheta⟩
  have hThetaOrder :=
    ScheideGlobalMaximumOrder G k e0 theta R.replacementTree hGlobalTheta
  have hXDThetaClosed : ColoredVertexSetClosed G theta XD := by
    change ColoredVertexSetClosed G theta
      (TreeSequenceVertexSet R.replacementTree)
    exact hThetaOrder.2.2.2.2
  have hAlpha0ThetaY0 : D.alpha0 ∈ MissingColors G theta y0 := by
    rw [hMissingThetaFixed y0 hy0X]
    exact hAlpha0D

  have hAlphaEdgeInK : ∀ x : V, Sum.inl x ∈ K → ∀ f : E,
      Incident G x f → phiD f = some alpha → Sum.inr f ∈ K := by
    intro x hx f hxf hcolor
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl R.u1)
    have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
        (Sum.inl x) (Sum.inr f) := by
      simp [TwoColorIncidenceGraph, hxf, hcolor]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hx
  have hAlphaBoundaryZ : ∀ x : V, (x = R.u1 ∨ x = R.u2) → ∀ f : E,
      Incident G x f → phiD f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∈ Z → False := by
    intro x hx f hxf hcolor w hends hwZ
    have hcolorOld : phi f = some alpha := by
      have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
        rcases hx with rfl | rfl
        · exact Or.inl hxf
        · exact Or.inr hxf)
      simpa [phiD, gamma] using hfixed.symm.trans hcolor
    have hfBoundary : f ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨w, (Finset.mem_sdiff.mp hwZ).1, x, ?_, hends.trans Sym2.eq_swap⟩
      rcases hx with rfl | rfl
      · exact R.u1_outside
      · exact R.u2_outside
    rcases hAlpha with hAlpha | hAlpha
    · exact (hXClosed hfBoundary hug0X hcolorOld) hAlpha
    · exact (hXClosed hfBoundary hug1X hcolorOld) hAlpha
  have hAlphaBoundaryOutside : ∀ x : V, (x = R.u1 ∨ x = R.u2) → ∀ f : E,
      Incident G x f → phiD f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∉ XD → False := by
    intro x hx f hxf hcolor w hends hwXD
    have hxXD : x ∈ XD := by
      rcases hx with rfl | rfl
      · exact hu1XD
      · exact hu2XD
    have hfK : Sum.inr f ∈ K := by
      apply hAlphaEdgeInK x
      · rcases hx with rfl | rfl
        · exact hu1K
        · exact hu2K
      · exact hxf
      · exact hcolor
    have hcolorTheta : theta f = some D.alpha0 := by
      simp [theta, K, TwoColorComponentSwap, hfK, hcolor,
        hAlphaNeAlpha0, hAlphaNeAlpha0.symm]
    have hfBoundary : f ∈ BoundaryEdges G XD := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxXD, w, hwXD, hends⟩
    exact (hXDThetaClosed hfBoundary hy0XD hcolorTheta) hAlpha0ThetaY0

  by_contra hnone
  have hNoIncident : ∀ x : V, (x = R.u1 ∨ x = R.u2) →
      ∀ f : E, Incident G x f → phiD f ≠ some alpha := by
    intro x hx f hxf hcolor
    obtain ⟨w, hends⟩ := Sym2.mem_iff_exists.mp hxf
    have hwne : w ≠ x := by
      intro h
      apply G.loopless f x
      simpa [h] using hends
    by_cases hwZ : w ∈ Z
    · exact hAlphaBoundaryZ x hx f hxf hcolor w hends hwZ
    by_cases hwXD : w ∈ XD
    · have hwPair : w = R.u1 ∨ w = R.u2 := by
        have hw := hwXD
        rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
          R.replacement_vertices] at hw
        rcases Finset.mem_union.mp hw with hwOld | hwPair
        · exact False.elim (hwZ (by simpa [X, Z, ug0, ug1] using hwOld))
        · simpa using hwPair
      have hinterior : G.ends f = s(R.u1, R.u2) := by
        rcases hx with rfl | rfl <;> rcases hwPair with rfl | rfl
        · exact False.elim (hwne rfl)
        · exact hends
        · simpa [Sym2.eq_swap] using hends
        · exact False.elim (hwne rfl)
      have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
        rcases hx with rfl | rfl
        · exact Or.inl hxf
        · exact Or.inr hxf)
      apply hnone
      exact ⟨f, by simpa [phiD, gamma] using hfixed.symm.trans hcolor,
        hinterior⟩
    · exact hAlphaBoundaryOutside x hx f hxf hcolor w hends hwXD
  have hMissingU1 : alpha ∈ MissingColors G phiD R.u1 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident R.u1 (Or.inl rfl) f hinc hcolor
  have hMissingU2 : alpha ∈ MissingColors G phiD R.u2 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident R.u2 (Or.inr rfl) f hinc hcolor
  have hdj := hXDElementary hu1XD hu2XD hu12
  exact (Finset.disjoint_left.mp hdj) hMissingU1 hMissingU2
