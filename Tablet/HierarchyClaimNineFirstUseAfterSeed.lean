import Tablet.HierarchyClaimNineUnusedTailColor
import Tablet.ChangeLemma
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyClaimNinePENormalization
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.sc2
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeIncidentEdge
import Tablet.TreeColoringInvariant
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.TreeMissingColors
import Tablet.P2752_T2_HierarchyMeasures
import Tablet.P2813_T1_BaseControl
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceInitialSegment

-- [TABLET NODE: HierarchyClaimNineFirstUseAfterSeed]
theorem HierarchyClaimNineFirstUseAfterSeed {V E : Type*}
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
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      (0 < H.dividerCount ∧
          alpha ∈ TreeMissingColors P.coloring
            (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧
          alpha ∈ TreeMissingColors P.coloring
            (P.corresponding.replacementETT.series.data.tree n.castSucc)))
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (j : ℕ) (hjLower : 2 ≤ j) (hjUpper : j ≤ HierarchyFullTailLength C)
    (ej : Fin T.length)
    (hej :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ej.val = A.length + (j - 1))
    (hfirst : P.coloring (T.edge ej) = some alpha ∧
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < ej.val →
        P.coloring (T.edge t) ≠ some alpha) :
    j - 1 ∈ HierarchyEligibleCommonMissingIndices
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
  let X := HierarchyFullTailPrefix Cm (j - 1)
  let y := T.vertex (Fin.last T.length)
  have hstar := (P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1).1
  have hell : HierarchyFullTailLength C = ell := by
    simp only [HierarchyFullTailLength, hstar]
    rfl
  have hprefix (i : ℕ) : HierarchyFullTailPrefix C i =
      HierarchyFullTailPrefix Cm i := by
    simp only [HierarchyFullTailPrefix, hstar]
    rfl
  have hj : j ≤ ell := by simpa only [hell] using hjUpper
  have htwo : 2 ≤ ell := by omega
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
  have hXlen : X.length = A.length + (j - 1) := by
    dsimp [X, HierarchyFullTailPrefix]
    change min (A.length + (j - 1)) T.length = A.length + (j - 1)
    omega
  have hAXstrict : A.length < X.length := by omega
  have hXleB : X.length ≤ B.length := by omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hXT : TreeSequenceInitialSegment X T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have hAX : TreeSequenceInitialSegment A X := commonPrefix hAT hXT (by omega)
  have hXB : TreeSequenceInitialSegment X B := commonPrefix hXT hBT hXleB
  have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT hBT (by omega)
  let ip : Fin (T.length + 1) := ⟨X.length, by have := hXT.1; omega⟩
  let x := T.vertex ip
  have hx : X.vertex (Fin.last X.length) = x := (hXT.2.1 _).symm
  have hxX : x ∈ TreeSequenceVertexSet X := by
    rw [← hx]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last X.length, rfl⟩
  have hxB : x ∈ TreeSequenceVertexSet B :=
    TreeSequenceInitialSegmentVertexSetSubset hXB hxX
  have hyNotB : y ∉ TreeSequenceVertexSet B := by
    intro hy
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi⟩ := hy
    have he := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hv := congrArg Fin.val he
    have := i.isLt
    simp only [Fin.val_castLE, Fin.val_last] at hv
    omega
  have hinterval : j - 1 ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1) := by
    rw [hell]
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨beta, hbeta⟩ := hvertexMissing mu cm.proper cm.oneEdgeUncolored x
  have hbNotY : beta ∉ MissingColors G mu y := by
    have hd := hnoCommon (j - 1) hinterval
    rw [hprefix, hx] at hd
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
    have hbound : ib.val ≤ B.length := le_trans hs.2 hXleB
    let i : Fin (B.length + 1) := ⟨ib.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i = ib := Fin.ext rfl
    have hbB : T.vertex ib ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, (hBT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
    have hv : T.vertex ib = x := by
      by_contra hn
      exact Finset.disjoint_left.mp (helem hbB hxB hn) hs.1 hbeta
    exact T.vertex_injective hv
  have haInA : a ∈ TreeSequenceVertexSet A := by
    let i : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ia := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (hAT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
  have haB : a ∈ TreeSequenceVertexSet B :=
    TreeSequenceInitialSegmentVertexSetSubset hAB haInA
  have hab : a ≠ x := by
    intro h
    have hv := congrArg Fin.val (T.vertex_injective h)
    change ia.val = X.length at hv
    omega
  have hmissing : alpha ∈ TreeMissingColors mu B ∧ beta ∈ TreeMissingColors mu B := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨a, haB, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨x, hxB, hbeta⟩
  have hejX : ej.val = X.length := hej.trans hXlen.symm
  have hordered :
      (alpha ∉ TreeMissingColors mu A ∨ beta ∉ TreeMissingColors mu A) →
        TreeVertexOrder T a (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < ib.val ∧ mu (T.edge t) = some c) := by
    intro _
    refine ⟨⟨ia, ib, rfl, rfl, ?_⟩, ?_⟩
    · rw [hib]
      change ia.val < X.length
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨t, ht, hlt, he⟩
      have hltX : t.val < X.length := by simpa only [hib] using hlt
      exact hfirst.2 t ht (by omega) he
  have changeResult := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing hordered
  have hsame : TwoColorComponent G mu alpha beta (Sum.inl a) =
      TwoColorComponent G mu alpha beta (Sum.inl x) := by
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
  have hxy : x ≠ y := fun he => hyNotB (he ▸ hxB)
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
      have hbQ : Sum.inl x ∈ Q := by rw [heq, hsame]; exact self x
      have hae := endpoint a haQ (leaf a (Or.inl ha))
      have hbe := endpoint x hbQ (leaf x (Or.inr hbeta))
      have hye := endpoint y (self y) (leaf y (Or.inl haY))
      have hnab : (Sum.inl a : Sum V E) ≠ Sum.inl x := fun h => hab (Sum.inl.inj h)
      have hnay : (Sum.inl a : Sum V E) ≠ Sum.inl y := fun h => hay (Sum.inl.inj h)
      have hnby : (Sum.inl x : Sum V E) ≠ Sum.inl y := fun h => hxy (Sum.inl.inj h)
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
  have changed := StableChangeCasesOneTwo G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint
  have hweak : HierarchyWeaklyStable H q sigma := changed.1
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
  have hmissingB : ∀ v ∈ TreeSequenceVertexSet B,
      MissingColors G sigma v = MissingColors G mu v := by
    intro v hv
    by_cases hvQ : Sum.inl v ∈ Q
    · have hva : v ≠ a := by
        intro he
        subst v
        exact Set.disjoint_left.mp hdisjoint hvQ (self a)
      have hvb : v ≠ x := by
        intro he
        subst v
        apply Set.disjoint_left.mp hdisjoint hvQ
        rw [hsame]
        exact self x
      have hna : alpha ∉ MissingColors G mu v := fun hm =>
        Finset.disjoint_left.mp (helem hv haB hva) hm ha
      have hnb : beta ∉ MissingColors G mu v := fun hm =>
        Finset.disjoint_left.mp (helem hv hxB hvb) hm hbeta
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
  -- Recover the exact stored seed, the only possible beta edge before the split.
  have seedIncident (f : E)
      (hstep : TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds))
      (hkind : em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.SE ∨
        em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.RE)
      (hedges : em.series.data.connectingEdges (Fin.last em.rounds) = {f}) :
      TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f := by
    generalize hn : Fin.last em.rounds = r at hstep hkind hedges ⊢
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
  have hfixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = mu (T.edge t) := by
    intro t ht hlt
    have hna : mu (T.edge t) ≠ some alpha := hfirst.2 t ht (by omega)
    by_cases hb : mu (T.edge t) = some beta
    · let tX : Fin X.length := ⟨t.val, hlt⟩
      have hcast : Fin.castLE hXT.1 tX = t := Fin.ext rfl
      have heX : mu (X.edge tX) = some beta := by
        rw [← hXT.2.2 tX, hcast]
        exact hb
      obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, hedge, hcolor, hstored⟩ :=
        HierarchyTailMissingColorExclusion G k e0 P.corresponding.replacementInput T mu em bm H
          helem (j - 1) (by omega) (by change j - 1 < ell; omega)
          beta (hx.symm ▸ hbeta) tX ht (by change t.val < A.length + (j - 1); omega) heX
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
      have he : T.edge t = f := by rw [← hcast, hXT.2.2 tX]; exact hedge
      simpa only [he] using hf
    · simp [sigma, TwoColorComponentSwap, hna, hb]
  have hstoredFirst : ∀ eta ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition mu T eta := by
    intro eta heta
    have hnotA : eta ∉ TreeMissingColors mu A := (Finset.mem_sdiff.mp heta).2
    have hna : eta ≠ alpha := by intro he; exact hnotA (he.symm ▸ haA)
    by_cases heb : eta = beta
    · subst eta
      have hbnew : beta ∈ MissingColors G sigma x := by rw [hmissingB x hxB]; exact hbeta
      have hs := firstSpec sigma beta ip hbnew
      let is := HierarchyFirstMissingPosition sigma T beta
      have hbound : is.val ≤ B.length := le_trans hs.2 hXleB
      let i : Fin (B.length + 1) := ⟨is.val, by omega⟩
      have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i = is := Fin.ext rfl
      have hvB : T.vertex is ∈ TreeSequenceVertexSet B := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, (hBT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
      have hbOld : beta ∈ MissingColors G mu (T.vertex is) := by
        rw [← hmissingB _ hvB]
        exact hs.1
      have hv : T.vertex is = x := by
        by_contra hn
        exact Finset.disjoint_left.mp (helem hvB hxB hn) hbOld hbeta
      exact (T.vertex_injective hv).trans hib.symm
    · have heq : (Finset.univ.filter fun i : Fin (T.length + 1) =>
            eta ∈ MissingColors G sigma (T.vertex i)) =
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            eta ∈ MissingColors G mu (T.vertex i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact missingOther _ eta hna heb
      simp only [HierarchyFirstMissingPosition, heq]
  let n := Fin.last em.rounds
  let Tn := em.series.data.tree n.castSucc
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have lastZero (hz : H.dividerCount = 0) : A = bm.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last, bm]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      simp [q] at hv
      exact (hz hv).elim
    · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
      congr 1
      apply Fin.ext
      have hv := congrArg Fin.val hr
      simpa [q] using hv.symm
  have coreToA : TreeSequenceInitialSegment bm.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
    by_cases hp : em.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (bm.parallel hp).2.2).leftSegment
    · rw [bm.nonparallel hp]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hTnA := segTrans TnToCore coreToA
  have hbetaNotA : beta ∉ TreeMissingColors mu A := by
    intro hbA
    obtain ⟨v, hvA, hbv⟩ := Finset.mem_biUnion.mp hbA
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
    have hvx : v ≠ x := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvA
      obtain ⟨i, hi⟩ := hvA
      intro he
      have hinj := T.vertex_injective ((hAT.2.1 i).trans (hi.trans he))
      have hval := congrArg Fin.val hinj
      have := i.isLt
      change i.val = X.length at hval
      omega
    exact Finset.disjoint_left.mp (helem hvB hxB hvx) hbv hbeta
  have stageMissingSub : HierarchyStageMissingColors H q ⊆ TreeMissingColors mu A := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      simp only [HierarchyStageMissingColors, hq, Fin.cases_zero]
      intro c hc
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hcv⟩
    · obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
      · have hv := congrArg Fin.val hzero
        simp [q] at hv
        exact (hz hv).elim
      · simp only [HierarchyStageMissingColors, hr, Fin.cases_succ,
          A, HierarchyStarredStage]
        exact Finset.Subset.refl _
  have hgammaCutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
      (alpha ∈ Cm.good.gamma q eta ∨ beta ∈ Cm.good.gamma q eta) →
        (HierarchyFirstMissingPosition mu T eta).val ≤ X.length := by
    intro eta heta hgamma
    have havoid := Cm.good.avoidance q eta heta
    rcases hgamma with haGamma | hbGamma
    · by_contra hnot
      have hp : X.length < (HierarchyFirstMissingPosition mu T eta).val := by omega
      have hlast : H.stage q.succ = T := by
        have hq : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
        rw [hq, H.terminalStage]
      have hsegment : alpha ∈ HierarchySegmentColors H q eta := by
        change alpha ∈ (Finset.univ.filter fun c =>
          ∃ r : Fin (H.stage q.succ).length, A.length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition mu T eta).val (H.stage q.succ).length ∧
              mu ((H.stage q.succ).edge r) = some c)
        rw [hlast]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨ej, ?_, ?_, hfirst.1⟩
        · change A.length ≤ ej.val
          omega
        · have := ej.isLt
          omega
      exact (Finset.mem_sdiff.mp (havoid haGamma)).2 hsegment
    · exact (hbetaNotA (stageMissingSub (Finset.mem_sdiff.mp (havoid hbGamma)).1)).elim
  have hfixedA : ∀ t : Fin A.length, sigma (A.edge t) = mu (A.edge t) := by
    obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
    · have hAcore : A = bm.core := by
        change HierarchyStarredStage H q = bm.core
        rw [hzero]
        rfl
      rw [hAcore]
      exact P2813_T1_BaseDisplayedEdges G k e0 P.corresponding.replacementInput T mu em bm
        sigma cm.oneEdgeUncolored hsone hbaseStable
    · have hinvariant : TreeColoringInvariant A mu sigma := by
        have hw := hweak
        simp only [HierarchyWeaklyStable, hr, Fin.cases_succ] at hw
        simpa only [A, hr, HierarchyStarredStage, Fin.cases_succ] using hw.2
      intro t
      by_cases ht : t.val = 0
      · have he : A.edge t = e0 := by
          rw [show t = ⟨0, A.positive⟩ from Fin.ext ht]
          exact A.first_edge
        rw [he]
        exact hsone.1.trans cm.oneEdgeUncolored.1.symm
      · exact hinvariant.1 t (by omega)
  have hfixedX : ∀ t : Fin X.length, sigma (X.edge t) = mu (X.edge t) := by
    intro t
    by_cases ht : t.val < A.length
    · let tA : Fin A.length := ⟨t.val, ht⟩
      have hcast : Fin.castLE hAX.1 tA = t := Fin.ext rfl
      rw [← hcast, hAX.2.2 tA]
      exact hfixedA tA
    · have hf := hfixedPrefix (Fin.castLE hXT.1 t) (by simp only [Fin.val_castLE]; omega)
        (by simpa only [Fin.val_castLE] using t.isLt)
      simpa only [hXT.2.2 t] using hf
  -- Transport only the prefix route; the suffix is retained in the old coloring.
  have transportRoute (S : TreeSequence G e0) (hroute : TashkinovAugmentationSequence mu S X) :
      TashkinovAugmentationSequence sigma S X := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    refine Relation.ReflTransGen.head_induction_on hroute ?_ ?_
    · exact Relation.ReflTransGen.refl
    · intro U W hstep htail ih
      obtain ⟨hlen, hUW, c, hcolor, hc⟩ := hstep
      have hWX := TashkinovAugmentationSequenceInitialSegment mu W X htail
      have hUX := segTrans hUW hWX
      have hcNew : c ∈ TreeMissingColors sigma U := by
        obtain ⟨v, hvU, hcv⟩ := Finset.mem_biUnion.mp hc
        have hvB := TreeSequenceInitialSegmentVertexSetSubset hXB
          (TreeSequenceInitialSegmentVertexSetSubset hUX hvU)
        exact Finset.mem_biUnion.mpr ⟨v, hvU, (hmissingB v hvB).symm ▸ hcv⟩
      let tW : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
      have hf := hfixedX (Fin.castLE hWX.1 tW)
      rw [hWX.2.2 tW] at hf
      exact Relation.ReflTransGen.head ⟨hlen, hUW, c, hf.trans hcolor, hcNew⟩ ih
  have routes :
      ((em.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn X) ∨
        ((em.series.data.kind n = some TashkinovExtensionKind.SE ∨
            em.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            em.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed X)) ∧
        TashkinovAugmentationSequence mu X T := by
    have old := P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu em
    rcases old with ⟨hkind, hroute⟩ | ⟨hkind, f, seed, hedges, hadjoin, hincident, hcolor, hroute⟩
    · have hTnX := segTrans hTnA hAX
      have hrouteX := TashkinovAugmentationSequenceRestrict mu Tn X T hroute hTnX hXT
      exact ⟨Or.inl ⟨hkind, transportRoute Tn hrouteX⟩,
        TashkinovAugmentationSequenceSuffix mu Tn X T hroute hTnX hXT⟩
    · have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T hroute
      have hseedX : TreeSequenceInitialSegment seed X := commonPrefix hseedT hXT (by
        have hl := hadjoin.1
        have htn := hTnA.1
        change seed.length = Tn.length + 1 at hl
        omega)
      have hrouteX := TashkinovAugmentationSequenceRestrict mu seed X T hroute hseedX hXT
      exact ⟨Or.inr ⟨hkind, f, seed, hedges, hadjoin, transportRoute seed hrouteX⟩,
        TashkinovAugmentationSequenceSuffix mu seed X T hroute hseedX hXT⟩
  have hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧ beta ∈ TreeMissingColors sigma X := by
    constructor
    · exact Finset.mem_biUnion.mpr
        ⟨a, TreeSequenceInitialSegmentVertexSetSubset hAX haInA, (hmissingB a haB).symm ▸ ha⟩
    · exact Finset.mem_biUnion.mpr ⟨x, hxX, (hmissingB x hxB).symm ▸ hbeta⟩
  obtain ⟨_, _, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint X hAX hAXstrict hXB
      hfixedPrefix routes.1 routes.2 hsplitMissing hmissingB hstoredFirst hgammaCutoff
  have hxT : x ∈ TreeSequenceVertexSet T := TreeSequenceInitialSegmentVertexSetSubset hXT hxX
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
      have hbnew : beta ∈ MissingColors G sigma x := by rw [hmissingB x hxB]; exact hbeta
      exact Finset.disjoint_left.mp (he hxT hyT hxy) hbnew hbetaNewY }
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  apply Finset.mem_filter.mpr
  refine ⟨hinterval, Pnew, beta, ?_, ?_⟩
  · rw [hPnew, hprefix, hx, hmissingB x hxB]
    exact hbeta
  · rw [hPnew]
    exact hbetaNewY
