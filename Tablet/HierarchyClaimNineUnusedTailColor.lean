import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CorrespondingExtendedTashkinovTreeTrans
import Tablet.HierarchyClaimNinePENormalization
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.StableColoring
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeIncidentEdge
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.HierarchyWeaklyStable
import Tablet.TreeMissingColors
import Tablet.P2813_T1_BaseControl
import Tablet.P2752_T2_HierarchyMeasures
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: HierarchyClaimNineUnusedTailColor]
theorem HierarchyClaimNineUnusedTailColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (hsituation : HierarchyPathNumber P.counterexample.hierarchy = 1)
    (alpha : Fin k)
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnormalized :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧ alpha ∈ TreeMissingColors P.coloring Tn))
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (hunused :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) ≠ some alpha) :
    HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx := by
-- BODY
  classical
  let mu := P.coloring
  let em := P.corresponding.replacementETT
  let bm := P.replacementBase
  let Cm := P.counterexample
  let cm := P.minimumContext
  let H := Cm.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength Cm
  let B := HierarchyFullTailPrefix Cm (ell - 1)
  let y := T.vertex (Fin.last T.length)
  have hstar := (P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1).1
  have hell : HierarchyFullTailLength C = ell := by
    simp only [HierarchyFullTailLength, hstar]
    rfl
  have hprefix (i : ℕ) : HierarchyFullTailPrefix C i =
      HierarchyFullTailPrefix Cm i := by
    simp only [HierarchyFullTailPrefix, hstar]
    rfl
  have htwo : 2 ≤ ell :=
    HierarchyCounterexampleTailAtLeastTwo G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have hAT : TreeSequenceInitialSegment A T := by
    have hs : TreeSequenceInitialSegment (HierarchyStarredStage H q) (H.stage q.succ) := by
      refine Fin.cases ?_ (fun i => ?_) q
      · exact H.coreInsideFirst
      · exact H.nested i.succ
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa only [hlast, H.terminalStage] using hs
  have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAT.1
  have hBlen : B.length = T.length - 1 := by
    dsimp [B, HierarchyFullTailPrefix]
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩ <;> intro i <;> rfl
  have hAB : TreeSequenceInitialSegment A B := by
    have hlen : A.length ≤ B.length := by omega
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hBT.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hAT.2.1 i)
    · intro i
      exact (hBT.2.2 (Fin.castLE hlen i)).symm.trans (hAT.2.2 i)
  let ip : Fin (T.length + 1) := ⟨B.length, by have := hBT.1; omega⟩
  let yp := T.vertex ip
  have hyp : B.vertex (Fin.last B.length) = yp := (hBT.2.1 _).symm
  have hypB : yp ∈ TreeSequenceVertexSet B := by
    rw [← hyp]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, rfl⟩
  have hyNotB : y ∉ TreeSequenceVertexSet B := by
    intro hy
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi⟩ := hy
    have he := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hv := congrArg Fin.val he
    have := i.isLt
    simp only [Fin.val_castLE, Fin.val_last] at hv
    omega
  have hinterval : ell - 1 ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1) := by
    rw [hell]
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨beta, hbeta⟩ := hvertexMissing mu cm.proper cm.oneEdgeUncolored yp
  have hbNotY : beta ∉ MissingColors G mu y := by
    have hd := hnoCommon (ell - 1) hinterval
    rw [hprefix, hyp] at hd
    exact Finset.disjoint_left.mp hd hbeta
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have haY : alpha ∈ MissingColors G mu y := hstart.2
  have hne : alpha ≠ beta := by
    intro he
    exact hbNotY (he ▸ haY)
  have firstSpec (rho : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1)) (hi : c ∈ MissingColors G rho (T.vertex i)) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        HierarchyFirstMissingPosition rho T c ≤ i := by
    let s : Finset (Fin (T.length + 1)) :=
      Finset.univ.filter fun j => c ∈ MissingColors G rho (T.vertex j)
    have his : i ∈ s := by simp [s, hi]
    have hs : s.Nonempty := ⟨i, his⟩
    have hp : HierarchyFirstMissingPosition rho T c = s.min' hs := by
      simp only [HierarchyFirstMissingPosition, s, dif_pos hs]
    rw [hp]
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem s hs)).2, Finset.min'_le s i his⟩
  obtain ⟨va, hvaA, hava⟩ := Finset.mem_biUnion.mp haA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvaA
  obtain ⟨iaA, hiaA⟩ := hvaA
  let iaT := Fin.castLE (Nat.succ_le_succ hAT.1) iaA
  have haia : alpha ∈ MissingColors G mu (T.vertex iaT) := by
    rw [hAT.2.1 iaA, hiaA]
    exact hava
  let ia := HierarchyFirstMissingPosition mu T alpha
  let ib := HierarchyFirstMissingPosition mu T beta
  let a := T.vertex ia
  have ha : alpha ∈ MissingColors G mu a := (firstSpec mu alpha iaT haia).1
  have hia : ia.val ≤ A.length := by
    have hm := (firstSpec mu alpha iaT haia).2
    change ia.val ≤ iaA.val at hm
    have := iaA.isLt
    omega
  have hib : ib = ip := by
    have hs := firstSpec mu beta ip hbeta
    have hbound : ib.val ≤ B.length := hs.2
    let j : Fin (B.length + 1) := ⟨ib.val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = ib := Fin.ext rfl
    have hbB : T.vertex ib ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
    have hv : T.vertex ib = yp := by
      by_contra hn
      exact Finset.disjoint_left.mp (helem hbB hypB hn) hs.1 hbeta
    exact T.vertex_injective hv
  have haB : a ∈ TreeSequenceVertexSet B := by
    let j : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hAT.1) j = ia := Fin.ext rfl
    apply TreeSequenceInitialSegmentVertexSetSubset hAB
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, (hAT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
  have hab : a ≠ yp := by
    intro h
    have hv := congrArg Fin.val (T.vertex_injective h)
    change ia.val = B.length at hv
    omega
  have hmissing : alpha ∈ TreeMissingColors mu B ∧ beta ∈ TreeMissingColors mu B := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨a, haB, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨yp, hypB, hbeta⟩
  have hordered :
      (alpha ∉ TreeMissingColors mu A ∨ beta ∉ TreeMissingColors mu A) →
        TreeVertexOrder T a (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < ib.val ∧ mu (T.edge t) = some c) := by
    intro _
    refine ⟨⟨ia, ib, rfl, rfl, ?_⟩, ?_⟩
    · rw [hib]
      change ia.val < B.length
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨t, ht, _, he⟩
      exact hunused t ht he
  have changeResult := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing hordered
  have hsame : TwoColorComponent G mu alpha beta (Sum.inl a) =
      TwoColorComponent G mu alpha beta (Sum.inl yp) := by
    have hc : TwoColorComponent G mu alpha beta (Sum.inl a) =
        TwoColorComponent G mu alpha beta (Sum.inl (T.vertex ib)) := by
      rcases hnormalized with hp | hz
      · exact changeResult.1 ⟨hp.1, Or.inl hp.2⟩
      · exact changeResult.2.1 ⟨hz.1, Or.inl hz.2⟩
    simpa only [hib] using hc
  let J := TwoColorIncidenceGraph G mu alpha beta
  let Q := TwoColorComponent G mu alpha beta (Sum.inl y)
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v) := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl v)
    rfl
  have leaf (v : V) (hv : alpha ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v) :
      Set.Subsingleton (J.neighborSet (Sum.inl v)) := by
    have hd : @SimpleGraph.degree _ J (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hv with hv | hv
      · exact MissingColorIncidenceEndpoint G mu alpha beta hne cm.proper v hv
      · have hj : J = TwoColorIncidenceGraph G mu beta alpha := by
          ext x z
          cases x <;> cases z <;> simp [J, TwoColorIncidenceGraph, or_comm]
        rw [hj]
        exact MissingColorIncidenceEndpoint G mu beta alpha hne.symm cm.proper v hv
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx z hz
    exact Finset.card_le_one_iff.mp hd
      (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hx)
      (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hz)
  have hay : a ≠ y := fun he => hyNotB (he ▸ haB)
  have hypy : yp ≠ y := fun he => hyNotB (he ▸ hypB)
  -- Three distinct missing-color endpoints cannot share one spanning path.
  have hdisjoint : Disjoint Q (TwoColorComponent G mu alpha beta (Sum.inl a)) := by
    rcases TwoColorComponentsDisjoint G mu alpha beta (Sum.inl y) (Sum.inl a) with heq | hd
    · obtain ⟨u, v, path, hp, hs⟩ :=
        TwoColorComponentSpanningPath G mu alpha beta cm.proper (Sum.inl y)
      have endpoint (w : V) (hw : Sum.inl w ∈ Q)
          (hl : Set.Subsingleton (J.neighborSet (Sum.inl w))) :
          Sum.inl w = u ∨ Sum.inl w = v := by
        have hm : Sum.inl w ∈ path.support := by
          change Sum.inl w ∈ {x | x ∈ path.support}
          rw [hs]
          exact hw
        by_contra hn
        push_neg at hn
        exact hp.isTrail.not_mem_support_of_subsingleton_neighborSet hn.1 hn.2 hl hm
      change Q = TwoColorComponent G mu alpha beta (Sum.inl a) at heq
      have haQ : Sum.inl a ∈ Q := by rw [heq]; exact self a
      have hbQ : Sum.inl yp ∈ Q := by rw [heq, hsame]; exact self yp
      have hae := endpoint a haQ (leaf a (Or.inl ha))
      have hbe := endpoint yp hbQ (leaf yp (Or.inr hbeta))
      have hye := endpoint y (self y) (leaf y (Or.inl haY))
      have hnab : (Sum.inl a : Sum V E) ≠ Sum.inl yp := fun h => hab (Sum.inl.inj h)
      have hnay : (Sum.inl a : Sum V E) ≠ Sum.inl y := fun h => hay (Sum.inl.inj h)
      have hnby : (Sum.inl yp : Sum V E) ≠ Sum.inl y := fun h => hypy (Sum.inl.inj h)
      rcases hae with hae | hae <;> rcases hbe with hbe | hbe <;>
        rcases hye with hye | hye <;> simp_all
    · exact hd
  have hpath : TwoColorPathComponent G mu alpha beta (Sum.inl y) :=
    ⟨hne, Sum.inl y, self y, leaf y (Or.inl haY)⟩
  let sigma := TwoColorComponentSwap G mu alpha beta (Sum.inl y)
  have hcase :
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors mu
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨
          (alpha ∈ TreeMissingColors mu A ∧
            alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧
            beta ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds)))) := by
    rcases hnormalized with hp | hz
    · exact Or.inl hp
    · exact Or.inr ⟨hz.1, Or.inl hz.2⟩
  obtain ⟨hbaseStable, hmissingA, hsproper, hsone, houtside⟩ :=
    P2813_T1_BaseControl G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      helem alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint
  obtain ⟨missingOutside, missingAlphaToBeta, missingBetaToAlpha, missingOther⟩ :=
    TwoColorComponentSwapMissingBehavior G mu alpha beta hne cm.proper (Sum.inl y)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ Q)
      (hf : Incident G v f) (hc : mu f = some alpha ∨ mu f = some beta) :
      Sum.inr f ∈ Q := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl y) at hv
    change J.connectedComponentMk (Sum.inr f) = J.connectedComponentMk (Sum.inl y)
    have hadj : J.Adj (Sum.inr f) (Sum.inl v) := by
      simpa only [J, TwoColorIncidenceGraph] using And.intro hf hc
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  -- Internal component vertices in B retain both affected colors as present.
  have hmissingB : ∀ v ∈ TreeSequenceVertexSet B,
      MissingColors G sigma v = MissingColors G mu v := by
    intro v hv
    by_cases hvQ : Sum.inl v ∈ Q
    · have hva : v ≠ a := by
        intro he
        subst v
        exact Set.disjoint_left.mp hdisjoint hvQ (self a)
      have hvb : v ≠ yp := by
        intro he
        subst v
        apply Set.disjoint_left.mp hdisjoint hvQ
        rw [hsame]
        exact self yp
      have hna : alpha ∉ MissingColors G mu v := fun hm =>
        Finset.disjoint_left.mp (helem hv haB hva) hm ha
      have hnb : beta ∉ MissingColors G mu v := fun hm =>
        Finset.disjoint_left.mp (helem hv hypB hvb) hm hbeta
      obtain ⟨fa, hfa, hfca⟩ : ∃ f, Incident G v f ∧ mu f = some alpha := by
        simpa [MissingColors, PresentColors] using hna
      obtain ⟨fb, hfb, hfcb⟩ : ∃ f, Incident G v f ∧ mu f = some beta := by
        simpa [MissingColors, PresentColors] using hnb
      have hfaQ := edgeOfVertex hvQ hfa (Or.inl hfca)
      have hfbQ := edgeOfVertex hvQ hfb (Or.inr hfcb)
      simp only [Q] at hfaQ hfbQ
      have hnewa : sigma fb = some alpha := by
        simp [sigma, TwoColorComponentSwap, hfbQ, hfcb, hne.symm]
      have hnewb : sigma fa = some beta := by
        simp [sigma, TwoColorComponentSwap, hfaQ, hfca]
      have hnsa : alpha ∉ MissingColors G sigma v := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fb, hfb, hnewa⟩
      have hnsb : beta ∉ MissingColors G sigma v := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fa, hfa, hnewb⟩
      ext c
      by_cases hca : c = alpha
      · subst c; simp only [hna, hnsa]
      by_cases hcb : c = beta
      · subst c; simp only [hnb, hnsb]
      exact missingOther v c hca hcb
    · exact missingOutside v hvQ
  have hbetaNewY : beta ∈ MissingColors G sigma y :=
    missingAlphaToBeta y (self y) haY
  -- Recover incidence of the individual stored seed from its certified step.
  have seedIncident (f : E)
      (hstep : TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds))
      (hkind : em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.SE ∨
        em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.RE)
      (hedges : em.series.data.connectingEdges (Fin.last em.rounds) = {f}) :
      TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f := by
    generalize hn : Fin.last em.rounds = j at hstep hkind hedges ⊢
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        rw [initialKind] at hkind
        simp at hkind
    | SE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        have he : choice.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
        rw [← he]
        exact ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    | PE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
        rw [currentKind] at hkind
        simp at hkind
    | RE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
        have he : available.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
        rw [← he]
        refine ⟨available.insideEndpoint, available.insideInCurrent, ?_⟩
        simp only [Incident, available.edgeEnds, Sym2.mem_iff, true_or]
  have hlastEnds : ∀ t : Fin T.length, t.val = B.length → Incident G yp (T.edge t) := by
    let candidates := (Finset.Icc 1 ell).filter fun i =>
      ∀ r : Fin T.length, A.length + i ≤ r.val →
        G.ends (T.edge r) = Sym2.mk (T.vertex r.castSucc) (T.vertex r.succ)
    have hpathNumber : (if hc : candidates.Nonempty then candidates.min' hc else ell) = 1 :=
      hsituation
    have hc : candidates.Nonempty := by
      by_contra hc
      rw [dif_neg hc] at hpathNumber
      omega
    have hmin : candidates.min' hc = 1 := by simpa only [dif_pos hc] using hpathNumber
    have hmem : 1 ∈ candidates := hmin ▸ Finset.min'_mem candidates hc
    have hconsecutive := (Finset.mem_filter.mp hmem).2
    intro t ht
    have hends := hconsecutive t (by omega)
    have hi : t.castSucc = ip := Fin.ext ht
    unfold Incident
    rw [hends, hi]
    exact Sym2.mem_mk_left _ _
  have htail : ∀ t : Fin T.length, A.length ≤ t.val → sigma (T.edge t) = mu (T.edge t) := by
    intro t ht
    have hna : mu (T.edge t) ≠ some alpha := hunused t ht
    by_cases hb : mu (T.edge t) = some beta
    · by_cases htB : t.val < B.length
      · let tB : Fin B.length := ⟨t.val, htB⟩
        have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
        have heB : mu (B.edge tB) = some beta := by
          rw [← hBT.2.2 tB, hcast]
          exact hb
        obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, hedge, hcolor, hstored⟩ :=
          HierarchyTailMissingColorExclusion G k e0 P.corresponding.replacementInput T mu em bm H
            helem (ell - 1) (by omega) (by change ell - 1 < ell; omega)
            beta (hyp.symm ▸ hbeta) tB ht
            (by change t.val < A.length + (ell - 1); omega) heB
        have hnotPE : em.series.data.kind (Fin.last em.rounds) ≠
            some TashkinovExtensionKind.PE := by
          rcases hkind with hs | hr
          · rw [hs]; simp
          · rw [hr]; simp
        have hstable : StableColoring (em.series.data.tree (Fin.last em.rounds).castSucc)
            (TashkinovStoredColors em.series.data (Fin.last em.rounds)) mu sigma := by
          simpa only [if_neg hnotPE] using hbaseStable
        have hf := hstable.1 f (seedIncident f hstep hkind hedges)
          ⟨beta, Finset.mem_union_right _ hstored, hcolor⟩
        have he : T.edge t = f := by rw [← hcast, hBT.2.2 tB]; exact hedge
        simpa only [he] using hf
      · have hlast : t.val = B.length := by have := t.isLt; omega
        have hinc := hlastEnds t hlast
        have hnot : beta ∉ PresentColors G mu yp := by simpa [MissingColors] using hbeta
        exact (hnot (by simp [PresentColors]; exact ⟨T.edge t, hinc, hb⟩)).elim
    · simp [sigma, TwoColorComponentSwap, hna, hb]
  -- Stored colors other than beta are unaffected; beta's first vertex remains yp.
  have hstoredFirst : ∀ eta ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition mu T eta := by
    intro eta heta
    have hnotA : eta ∉ TreeMissingColors mu A := (Finset.mem_sdiff.mp heta).2
    have hna : eta ≠ alpha := by intro he; exact hnotA (he.symm ▸ haA)
    by_cases heb : eta = beta
    · subst eta
      have hbnew : beta ∈ MissingColors G sigma yp := by rw [hmissingB yp hypB]; exact hbeta
      have hs := firstSpec sigma beta ip hbnew
      let is := HierarchyFirstMissingPosition sigma T beta
      have hbound : is.val ≤ B.length := hs.2
      let j : Fin (B.length + 1) := ⟨is.val, by omega⟩
      have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = is := Fin.ext rfl
      have hvB : T.vertex is ∈ TreeSequenceVertexSet B := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨j, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
      have hbOld : beta ∈ MissingColors G mu (T.vertex is) := by
        rw [← hmissingB _ hvB]
        exact hs.1
      have hv : T.vertex is = yp := by
        by_contra hn
        exact Finset.disjoint_left.mp (helem hvB hypB hn) hbOld hbeta
      exact (T.vertex_injective hv).trans hib.symm
    · have heq : (Finset.univ.filter fun i : Fin (T.length + 1) =>
            eta ∈ MissingColors G sigma (T.vertex i)) =
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            eta ∈ MissingColors G mu (T.vertex i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact missingOther _ eta hna heb
      simp only [HierarchyFirstMissingPosition, heq]
  -- Reconstruct only after the exact tail and first-position agreements hold.
  obtain ⟨_, _, _, _, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoFullTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint htail hmissingB hstoredFirst
  have hypT : yp ∈ TreeSequenceVertexSet T := TreeSequenceInitialSegmentVertexSetSubset hBT hypB
  have hyT : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  let Cs : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact Cm.positive
    hierarchy := K
    good := good
    maximum := hmax
    notElementary := by
      intro he
      have hbnew : beta ∈ MissingColors G sigma yp := by rw [hmissingB yp hypB]; exact hbeta
      exact Finset.disjoint_left.mp (he hypT hyT hypy) hbnew hbetaNewY }
  -- This registered composition also transports all six minimum-context fields.
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  apply Finset.mem_filter.mpr
  refine ⟨?_, Pnew, beta, ?_, ?_⟩
  · simpa only [hell] using hinterval
  · rw [hPnew, hell, hprefix, hyp, hmissingB yp hypB]
    exact hbeta
  · rw [hPnew]
    exact hbetaNewY
