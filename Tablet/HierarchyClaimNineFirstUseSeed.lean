import Tablet.TreeColorSetMinusClosed
import Tablet.CertifiedETTPredecessor
import Tablet.BoundaryEdges
import Tablet.P2752_T2_HierarchyMeasures
import Tablet.P2813_T1_TerminalRoute
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.PresentColors
import Tablet.TreeIncidentEdge
import Tablet.HierarchyClaimNineFirstUseAfterSeed
import Tablet.HierarchyClaimNineUnusedTailColor
import Tablet.ChangeLemma
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyClaimNinePENormalization
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.HierarchySegmentColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.MaximumDefectiveChoice
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.ParallelCommonMissingClosed
import Tablet.OrderedTreeUnion
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeColoringInvariant
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TreeMissingColors
import Tablet.sc2

-- [TABLET NODE: HierarchyClaimNineFirstUseSeed]
theorem HierarchyClaimNineFirstUseSeed {V E : Type*}
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
    (e1 : Fin T.length)
    (he1 :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      e1.val = A.length)
    (hfirst : P.coloring (T.edge e1) = some alpha) :
    (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty := by
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
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := by
    have hlen : A.length ≤ B.length := by omega
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hBT.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hAT.2.1 i)
    · intro i
      exact (hBT.2.2 (Fin.castLE hlen i)).symm.trans (hAT.2.2 i)
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have haY : alpha ∈ MissingColors G mu y := hstart.2
  have hmissingB : alpha ∈ TreeMissingColors mu B := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp haA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hmv⟩
  let n : Fin (em.rounds + 1) := Fin.last em.rounds
  let Tn := em.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  let R := D.biUnion (Cm.good.gamma q)
  have hDcard : D.card ≤ em.rounds := by
    change (HierarchyStoredColorsAt H q).card ≤ em.rounds
    exact HierarchyStoredColorsCardinality H q
  have hRcard : R.card ≤ 2 * em.rounds := by
    calc
      R.card ≤ ∑ eta ∈ D, (Cm.good.gamma q eta).card := Finset.card_biUnion_le
      _ = 2 * D.card := by
        rw [Finset.sum_congr rfl (fun eta heta => Cm.good.twoColors q eta heta)]
        change (∑ eta ∈ HierarchyStoredColorsAt H q, (2 : ℕ)) =
          2 * (HierarchyStoredColorsAt H q).card
        simp [Nat.mul_comm]
      _ ≤ 2 * em.rounds := Nat.mul_le_mul_left 2 hDcard
  have hAcore (hz : H.dividerCount = 0) : A = bm.core := by
    have hq : q = 0 := Fin.ext (by simp [q, hz])
    simp [A, H, q, bm, HierarchyStarredStage, hq]
  have hgammaZero (hz : H.dividerCount = 0) : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧ TreeColorSetClosed G mu A {gamma} := by as_aux_lemma =>
    clear * - P mu em bm Cm cm H q A Tn R hRcard hAcore hz alpha
    have hAcore : A = bm.core := by simpa [bm] using hAcore hz
    have hq0 : q = 0 := Fin.ext (by simp [q, hz])
    have lowerElementary :
        let p : Fin em.rounds := ⟨em.rounds - 1, by have := em.roundsPositive; omega⟩
        ColoredVertexSetElementary G (em.series.data.coloring p.castSucc)
          (TreeSequenceVertexSet Tn) := by
      dsimp only
      dsimp only [Tn]
      by_cases hr : em.rounds = 1
      · have hp : (⟨em.rounds - 1, by have := em.roundsPositive; omega⟩ : Fin em.rounds).castSucc = 0 := by
          apply Fin.ext
          simp [hr]
        have htree : n.castSucc = (⟨1, by omega⟩ : Fin (em.rounds + 2)) := by
          apply Fin.ext
          simp [n, hr]
        rw [hp, htree]
        exact (TechnicalTheoremBase G k em.rounds e0
          P.corresponding.replacementInput em.series).1
      · have hmore : 1 < em.rounds := by
          have := em.roundsPositive
          omega
        obtain ⟨pred, hround, hmax, _, _⟩ := CertifiedETTPredecessor G k e0
          P.corresponding.replacementInput T mu em (Cm.maximum) hmore
        have htree : n.castSucc = (⟨em.rounds, by omega⟩ : Fin (em.rounds + 2)) := by
          apply Fin.ext
          rfl
        rw [htree]
        have hpredPositive : 0 < pred.rounds := by rw [hround]; omega
        have hpredLower : pred.rounds < em.rounds := by rw [hround]; omega
        exact (cm.lowerRung pred hpredPositive hpredLower hmax).1
    by_cases hpe : em.series.data.kind n = some TashkinovExtensionKind.PE
    · let S := (TreeMissingColors mu Tn ∩ TreeMissingColors mu bm.closure) \ R
      have hScard : 4 ≤ S.card := by
        simpa [S, R, D, n, Tn, H, q, hq0, mu, bm] using
          (Cm.good.parallelBase hpe).2
      have hSsub : S ⊆ {alpha} → S.card ≤ 1 := by
        intro hs
        exact (Finset.card_le_card hs).trans (by simp)
      have hremove : (S \ {alpha}).Nonempty := by
        apply Finset.card_pos.mp
        by_contra h
        have he : S \ {alpha} = ∅ := Finset.card_eq_zero.mp (by omega)
        apply (by omega : ¬ S.card ≤ 1)
        apply hSsub
        intro c hc
        by_contra hca
        have hc' : c ∈ S \ {alpha} := Finset.mem_sdiff.mpr ⟨hc, by simpa using hca⟩
        rw [he] at hc'
        simp at hc'
      obtain ⟨gamma, hg⟩ := hremove
      have hgS : gamma ∈ S := (Finset.mem_sdiff.mp hg).1
      have hgAlpha : gamma ≠ alpha := by
        intro he
        exact (Finset.mem_sdiff.mp hg).2 (by simp [he])
      have hgparts := Finset.mem_sdiff.mp hgS
      have hgint := Finset.mem_inter.mp hgparts.1
      have hgA : gamma ∈ TreeMissingColors mu A := by
        obtain ⟨u⟩ := (bm.parallel hpe).2.2
        have hTnA : TreeSequenceInitialSegment Tn A := by
          rw [hAcore]
          exact u.leftSegment
        obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgint.1
        exact Finset.mem_biUnion.mpr
          ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hmv⟩
      have hclosedCore := ParallelCommonMissingClosed G k e0
        P.corresponding.replacementInput T mu mu em (by
          have := em.roundsPositive
          omega) bm em.generatingColoring hpe lowerElementary
      have hgClosed : TreeColorSetClosed G mu A {gamma} := by
        rw [hAcore]
        intro c hc
        have hcgamma : c = gamma := Finset.mem_singleton.mp hc
        subst c
        exact hclosedCore gamma hgparts.1
      exact ⟨gamma, hgA, hgparts.2, hgAlpha, hgint.1, hgClosed⟩
    · have hAeq : A = Tn := by
        rw [hAcore]
        exact bm.nonparallel hpe
      let S := TreeMissingColors mu Tn \ (R ∪ {alpha})
      have hlarge : 2 * em.rounds + 11 ≤ (TreeMissingColors mu Tn).card := by
        simpa [Tn, n] using cm.largeMissingSet
      have hSne : S.Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff]
        have hi : ((TreeMissingColors mu Tn) ∩ (R ∪ {alpha})).card ≤
            (R ∪ {alpha}).card := Finset.card_le_card Finset.inter_subset_right
        have hi' : ((R ∪ {alpha}) ∩ (TreeMissingColors mu Tn)).card ≤
            (R ∪ {alpha}).card := by
          simpa [Finset.inter_comm] using hi
        have hru : (R ∪ {alpha}).card ≤ 2 * em.rounds + 1 := by
          calc
            (R ∪ {alpha}).card ≤ R.card + ({alpha} : Finset (Fin k)).card :=
              Finset.card_union_le R {alpha}
            _ ≤ 2 * em.rounds + 1 := by simp; omega
        omega
      obtain ⟨gamma, hg⟩ := hSne
      have hgTn := (Finset.mem_sdiff.mp hg).1
      have hgnot := (Finset.mem_sdiff.mp hg).2
      have hgR : gamma ∉ R := by
        intro hc
        exact hgnot (Finset.mem_union_left _ hc)
      have hgAlpha : gamma ≠ alpha := by
        intro he
        exact hgnot (Finset.mem_union_right _ (by simp [he]))
      have closedSingleton (U : TreeSequence G e0)
          (hc : ColoredVertexSetClosed G mu (TreeSequenceVertexSet U))
          (hm : gamma ∈ TreeMissingColors mu U) :
          TreeColorSetClosed G mu U {gamma} := by
        intro c hcs
        have hcg : c = gamma := Finset.mem_singleton.mp hcs
        subst c
        obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro f hf
        obtain ⟨hb, hcol⟩ := Finset.mem_filter.mp hf
        exact hc hb hv hcol hvm
      have stableClosed (U : TreeSequence G e0) (S : Finset (Fin k))
          (psi pi : PartialEdgeColoring E k)
          (hpsi : IsProperEdgeColoring G psi) (hpsiOne : IsOneEdgeUncolored psi e0)
          (hpi : IsProperEdgeColoring G pi) (hpiOne : IsOneEdgeUncolored pi e0)
          (hs : StableColoring U S psi pi)
          (hc : ColoredVertexSetClosed G psi (TreeSequenceVertexSet U)) :
          ColoredVertexSetClosed G pi (TreeSequenceVertexSet U) := by
        have hr : StableColoring U S pi psi :=
          (sc2 G e0 U S).symm
            (x := ⟨psi, hpsi, hpsiOne⟩) (y := ⟨pi, hpi, hpiOne⟩) hs
        intro f c v hb hv hcol hvm
        have hf : TreeIncidentEdge U f := by
          have hb' : ∃ u ∈ TreeSequenceVertexSet U, ∃ w ∉ TreeSequenceVertexSet U,
              G.ends f = Sym2.mk u w := by
            simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hb
          obtain ⟨u, hu, w, hw, he⟩ := hb'
          refine ⟨u, hu, ?_⟩
          change u ∈ G.ends f
          rw [he]
          simp
        have hm : c ∈ TreeMissingColors pi U := Finset.mem_biUnion.mpr ⟨v, hv, hvm⟩
        have hsame := hr.1 f hf ⟨c, Finset.mem_union_left _ hm, hcol⟩
        have hvm' : c ∈ MissingColors G psi v := by rw [hr.2 v hv]; exact hvm
        exact hc hb hv (hsame.trans hcol) hvm'
      let p : Fin em.rounds := ⟨em.rounds - 1, by have := em.roundsPositive; omega⟩
      have hp : p.succ = n := by
        apply Fin.ext
        change p.val + 1 = em.rounds
        dsimp [p]
        exact Nat.sub_add_cancel em.roundsPositive
      have hphi : mu = em.series.data.coloring p.succ := by
        rw [hp]
        exact em.generatingColoring
      have hTn : Tn = em.series.data.tree p.succ.castSucc := by rw [hp]
      have hclosedTn : TreeColorSetClosed G mu Tn {gamma} := by
        generalize heq : p.succ = target
        cases em.series.certified target with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
          exact (Fin.succ_ne_zero p heq).elim
        | PE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            delta gammaRule secondStable secondStableProper secondStableOneUncolored
            secondStableRelation exitWitness currentColoring currentProper
            currentOneUncolored currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension =>
          have hci : ci = p := Fin.ext (by
            have hv := congrArg Fin.val heq
            simp at hv ⊢
            omega)
          subst ci
          have hfinalPE : em.series.data.kind n = some TashkinovExtensionKind.PE := by
            rw [← hp, currentKind]
          exact (hpe hfinalPE).elim
        | RE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored currentEdges
            currentKind currentVertex currentOutside currentDelta currentGamma adjoined
            adjoinedExactly closedExtension orderedExtension strictExtension =>
          have hci : ci = p := Fin.ext (by
            have hv := congrArg Fin.val heq
            simp at hv ⊢
            omega)
          subst ci
          have hclosedPrev : ColoredVertexSetClosed G mu
              (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) := by
            rw [hphi, currentColoring]
            exact previousClosed
          rw [hTn]
          exact closedSingleton _ hclosedPrev (by simpa [hphi, currentColoring, hTn] using hgTn)
        | SE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
            currentStored currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
          have hci : ci = p := Fin.ext (by
            have hv := congrArg Fin.val heq
            simp at hv ⊢
            omega)
          subst ci
          have hstableClosed : ColoredVertexSetClosed G choice.selected
              (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) :=
            stableClosed (em.series.data.tree p.succ.castSucc)
            (TashkinovStoredColors em.series.data p.castSucc)
            (em.series.data.coloring p.castSucc) choice.selected
            previousProper previousOneUncolored choice.selectedProper
            choice.selectedOneUncolored choice.selectedStable previousClosed
          have hclosedNow : ColoredVertexSetClosed G mu
              (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) := by
            rw [hphi, currentColoring]
            exact hstableClosed
          rw [hTn]
          exact closedSingleton _ hclosedNow (by simpa [hphi, currentColoring, hTn] using hgTn)
      have hclosed : TreeColorSetClosed G mu A {gamma} := by
        rw [hAeq]
        exact hclosedTn
      have hgA : gamma ∈ TreeMissingColors mu A := by rw [hAeq]; exact hgTn
      exact ⟨gamma, hgA, hgR, hgAlpha, hgTn, hclosed⟩
  have hgammaPositive (hz : 0 < H.dividerCount) : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧
        TreeColorSetClosed G mu A {gamma} ∧
        gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
          (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1)))) := by as_aux_lemma =>
    clear * - P mu em bm Cm cm H q A Tn R D alpha hz
    let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hq : q = i.succ := by
      apply Fin.ext
      simp [i, q]
      omega
    have hAeq : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
      · have hv := congrArg Fin.val hzero
        simp [q] at hv
        omega
      · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
        congr 1
        apply Fin.ext
        have hv := congrArg Fin.val hr
        simpa [q] using hv.symm
    have segTrans {S U W : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U)
        (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
      refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
      · intro j
        exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) j)).trans (hSU.2.1 j)
      · intro j
        exact (hUW.2.2 (Fin.castLE hSU.1 j)).trans (hSU.2.2 j)
    have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
        TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
          (H.stage ⟨a + d, by omega⟩) := by
      induction d with
      | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      | succ d ih =>
        exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
    have coreToA : TreeSequenceInitialSegment bm.core A := by
      rw [hAeq]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
    have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
      by_cases hpe : em.series.data.kind n = some TashkinovExtensionKind.PE
      · obtain ⟨u⟩ := (bm.parallel hpe).2.2
        exact u.leftSegment
      · rw [bm.nonparallel hpe]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    have hTnA := segTrans TnToCore coreToA
    let Dprev := HierarchyStoredColorsAt H i.succ
    let Rprev := Dprev.biUnion (Cm.good.gamma i.castSucc)
    obtain ⟨eta, hη, _⟩ := Cm.good.uniqueRefresh i
    rcases hη with ⟨heta, hpair, hcopy⟩
    have hRsub : R ⊆ Rprev ∪ Cm.good.gamma i.succ eta := by
      intro c hc
      obtain ⟨theta, htheta, hc⟩ := Finset.mem_biUnion.mp hc
      have hcNow : c ∈ Cm.good.gamma i.succ theta := by simpa only [hq] using hc
      by_cases hthetaEta : theta = eta
      · subst theta
        exact Finset.mem_union_right _ (by simpa only [hq] using hcNow)
      · have hthetaCurrent : theta ∈ Dprev := by
          simpa [Dprev, D, hq] using htheta
        have hthetaPrev : theta ∈ HierarchyStoredColorsAt H i.castSucc :=
          HierarchyStoredColorsAntitone H i hthetaCurrent
        have hcopyTheta := hcopy theta hthetaCurrent hthetaEta
        apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨theta, hthetaCurrent, by rw [← hcopyTheta]; exact hcNow⟩
    have hRprevCard : Rprev.card ≤ 2 * em.rounds := by
      calc
        Rprev.card ≤ ∑ theta ∈ Dprev, (Cm.good.gamma i.castSucc theta).card :=
          Finset.card_biUnion_le
        _ = 2 * Dprev.card := by
          rw [Finset.sum_congr rfl (fun theta htheta =>
            Cm.good.twoColors i.castSucc theta (HierarchyStoredColorsAntitone H i
              (by simpa [Dprev, D, hq] using htheta)))]
          change (∑ theta ∈ HierarchyStoredColorsAt H i.succ, (2 : ℕ)) =
            2 * (HierarchyStoredColorsAt H i.succ).card
          simp [Nat.mul_comm]
        _ ≤ 2 * em.rounds := by
          exact Nat.mul_le_mul_left 2 (by
            change Dprev.card ≤ em.rounds
            exact HierarchyStoredColorsCardinality H i.succ)
    have hpairCard : (Cm.good.gamma i.succ eta).card ≤ 2 := by
      have hp := Cm.good.twoColors i.succ eta (by simpa [D, hq] using heta)
      exact le_of_eq hp
    have hforbiddenCard : (Rprev ∪ R ∪ {alpha}).card ≤ 2 * em.rounds + 3 := by
      have hsub : Rprev ∪ R ∪ {alpha} ⊆ Rprev ∪ Cm.good.gamma i.succ eta ∪ {alpha} := by
        intro c hc
        simp only [Finset.mem_union] at hc ⊢
        rcases hc with h | h
        · rcases h with h | h
          · exact Or.inl (Or.inl h)
          · have hp := Finset.mem_union.mp (hRsub h)
            rcases hp with hp | hp
            · exact Or.inl (Or.inl hp)
            · exact Or.inl (Or.inr hp)
        · exact Or.inr h
      calc
        (Rprev ∪ R ∪ {alpha}).card ≤
            (Rprev ∪ Cm.good.gamma i.succ eta ∪ {alpha}).card :=
          Finset.card_le_card hsub
        _ ≤ (Rprev ∪ Cm.good.gamma i.succ eta).card + 1 := by
          calc
            _ ≤ (Rprev ∪ Cm.good.gamma i.succ eta).card + ({alpha} : Finset (Fin k)).card :=
              Finset.card_union_le _ _
            _ = _ := by simp
        _ ≤ Rprev.card + (Cm.good.gamma i.succ eta).card + 1 := by
          have := Finset.card_union_le Rprev (Cm.good.gamma i.succ eta)
          omega
        _ ≤ 2 * em.rounds + 3 := by omega
    have hlarge : 2 * em.rounds + 11 ≤ (TreeMissingColors mu Tn).card := by
      simpa [Tn, n] using cm.largeMissingSet
    let S := TreeMissingColors mu Tn \ (Rprev ∪ R ∪ {alpha})
    have hSne : S.Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff]
      have hi : ((Rprev ∪ R ∪ {alpha}) ∩ TreeMissingColors mu Tn).card ≤
          (Rprev ∪ R ∪ {alpha}).card := Finset.card_le_card Finset.inter_subset_left
      omega
    obtain ⟨gamma, hg⟩ := hSne
    have hgparts := Finset.mem_sdiff.mp hg
    have hgnot := hgparts.2
    have hgA : gamma ∈ TreeMissingColors mu A := by
      obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgparts.1
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hmv⟩
    have hgR : gamma ∉ R := by
      intro h
      exact hgnot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hgAlpha : gamma ≠ alpha := by
      intro h
      exact hgnot (Finset.mem_union_right _ (by simp [h]))
    have hgPrev : gamma ∉ Rprev := by
      intro h
      exact hgnot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hminus : TreeColorSetMinusClosed G mu A Rprev := by
      have hstage : i.succ.castSucc =
          (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := by
        apply Fin.ext
        simp [i]
        omega
      rw [hAeq]
      simpa [Rprev, Dprev, q, hq, hstage] using Cm.good.minusClosed i
    have hminusClosed :
        TreeColorSetClosed G mu A (TreeMissingColors mu A \ Rprev) := hminus
    have hgClosed : TreeColorSetClosed G mu A {gamma} := by
      intro c hc
      have hcgamma : c = gamma := Finset.mem_singleton.mp hc
      subst c
      exact hminusClosed gamma (Finset.mem_sdiff.mpr ⟨hgA, hgPrev⟩)
    have hgPrev' : gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
        (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1))) : Finset (Fin k)) := by
      change gamma ∉ ((HierarchyStoredColorsAt H i.succ).biUnion
        (Cm.good.gamma i.castSucc)) at hgPrev
      simpa [q, hq, i] using hgPrev
    exact ⟨gamma, hgA, hgR, hgAlpha, hgparts.1, hgClosed, hgPrev'⟩
  have hgammaData : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧ TreeColorSetClosed G mu A {gamma} ∧
        (H.dividerCount = 0 ∨ gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
          (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1))))) := by as_aux_lemma =>
    by_cases hz : H.dividerCount = 0
    · obtain ⟨gamma, hA, hR, hne, hTn, hclosed⟩ := hgammaZero hz
      exact ⟨gamma, hA, hR, hne, hTn, hclosed, Or.inl hz⟩
    · have hp : 0 < H.dividerCount := Nat.pos_of_ne_zero hz
      obtain ⟨gamma, hA, hR, hne, hTn, hclosed, hprev⟩ := hgammaPositive hp
      exact ⟨gamma, hA, hR, hne, hTn, hclosed, Or.inr hprev⟩
  obtain ⟨gamma, hgammaA, hgammaR, hgammaNe, hgammaTn, hgammaClosed,
    hgammaPrev⟩ := hgammaData
  have hmissingGammaB : gamma ∈ TreeMissingColors mu B := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hmv⟩
  have hmissingAlphaB : alpha ∈ TreeMissingColors mu B := hmissingB
  have hne : gamma ≠ alpha := hgammaNe
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
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem s hs)).2,
      Finset.min'_le s i his⟩
  obtain ⟨vgWitness, hvgA, hvg⟩ := Finset.mem_biUnion.mp hgammaA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvgA
  obtain ⟨igA, higA⟩ := hvgA
  let igT := Fin.castLE (Nat.succ_le_succ hAT.1) igA
  have hgamig : gamma ∈ MissingColors G mu (T.vertex igT) := by
    rw [hAT.2.1 igA, higA]
    exact hvg
  let ig := HierarchyFirstMissingPosition mu T gamma
  let ia := HierarchyFirstMissingPosition mu T alpha
  let vg := T.vertex ig
  have hgamvg : gamma ∈ MissingColors G mu vg := (firstSpec mu gamma igT hgamig).1
  have higBound : ig.val ≤ A.length := by
    have hm := (firstSpec mu gamma igT hgamig).2
    change ig.val ≤ igA.val at hm
    have := igA.isLt
    omega
  have hvgInA : vg ∈ TreeSequenceVertexSet A := by
    let i : Fin (A.length + 1) := ⟨ig.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ig := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (hAT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
  have hAlphaAtFirst : alpha ∈ MissingColors G mu (T.vertex ia) := by
    obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp haA
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨i, hi⟩ := hw
    let iT := Fin.castLE (Nat.succ_le_succ hAT.1) i
    have hwi : alpha ∈ MissingColors G mu (T.vertex iT) := by
      rw [hAT.2.1 i, hi]
      exact hmw
    exact (firstSpec mu alpha iT hwi).1
  have hiaBound : ia.val ≤ A.length := by
    obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp haA
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨i, hi⟩ := hw
    let iT := Fin.castLE (Nat.succ_le_succ hAT.1) i
    have hwi : alpha ∈ MissingColors G mu (T.vertex iT) := by
      rw [hAT.2.1 i, hi]
      exact hmw
    have hs := firstSpec mu alpha iT hwi
    have hv := hs.2
    change ia.val ≤ i.val at hv
    have := i.isLt
    omega
  have hiaInA : T.vertex ia ∈ TreeSequenceVertexSet A := by
    let iA : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hiA : Fin.castLE (Nat.succ_le_succ hAT.1) iA = ia := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨iA, (hAT.2.1 iA).symm.trans (congrArg T.vertex hiA)⟩
  have horderedUnused :
      (gamma ∉ TreeMissingColors mu A ∨ alpha ∉ TreeMissingColors mu A) →
        TreeVertexOrder T vg (T.vertex ia) ∧
          gamma ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < ia.val ∧ mu (T.edge t) = some c) := by
    intro h
    rcases h with h | h
    · exact (h hgammaA).elim
    · exact (h haA).elim
  have htaildiff : T.length - A.length = ell := by omega
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    clear * - hSU hlen
    cases S with
    | mk ls ps vs es vis eis fs aas =>
      cases U with
      | mk lu pu vu eu viu eiu fu aau =>
        simp only at hlen
        subst lu
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.2 i).symm
  let Ty := TreeSequencePrefix T (min (A.length + (T.length - A.length - 1)) T.length)
    (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hsumA : A.length + (T.length - A.length) = T.length :=
    Nat.add_sub_of_le hAT.1
  have hidx : A.length + (T.length - A.length - 1) = T.length - 1 := by
    calc
      A.length + (T.length - A.length - 1) =
          (A.length + (T.length - A.length)) - 1 := by omega
      _ = T.length - 1 := by rw [hsumA]
  have hTyLen : Ty.length = B.length := by
    change min (A.length + (T.length - A.length - 1)) T.length = B.length
    rw [hidx, Nat.min_eq_left (by omega), hBlen]
  have hBToTy : TreeSequenceInitialSegment B Ty := by
    refine ⟨hTyLen.symm.le, ?_, ?_⟩
    · intro i
      let j : Fin (Ty.length + 1) := Fin.cast (congrArg Nat.succ hTyLen.symm) i
      calc
        B.vertex i = T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) i) := hBT.2.1 i
        _ = T.vertex (Fin.castLE (Nat.succ_le_succ hTyT.1) j) := by
          congr 1
        _ = Ty.vertex j := (hTyT.2.1 j).symm
    · intro i
      let j : Fin Ty.length := Fin.cast hTyLen.symm i
      calc
        B.edge i = T.edge (Fin.castLE hBT.1 i) := hBT.2.2 i
        _ = T.edge (Fin.castLE hTyT.1 j) := by
          congr 1
        _ = Ty.edge j := (hTyT.2.2 j).symm
  have hBTy : B = Ty := equalTrees hBToTy hTyLen.symm
  have hchange := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers
    cm.lexicographicMinimality helem cm.largeMissingSet gamma alpha hne
    (by
      change gamma ∈ TreeMissingColors mu Ty ∧ alpha ∈ TreeMissingColors mu Ty
      rw [← hBTy]
      exact ⟨hmissingGammaB, hmissingAlphaB⟩) horderedUnused
  have hchangeClosed := hchange.2.2 ⟨hgammaA, hgammaClosed⟩
  have hsame : TwoColorComponent G mu gamma alpha (Sum.inl vg) =
      TwoColorComponent G mu gamma alpha (Sum.inl (T.vertex ia)) := hchangeClosed.1
  have hinterchangeable : TreeInterchangeable G A mu gamma alpha := hchangeClosed.2
  let J := TwoColorIncidenceGraph G mu gamma alpha
  let Q := TwoColorComponent G mu gamma alpha (Sum.inl y)
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v) := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl v)
    rfl
  have leaf (v : V) (hv : gamma ∈ MissingColors G mu v ∨ alpha ∈ MissingColors G mu v) :
      Set.Subsingleton (J.neighborSet (Sum.inl v)) := by
    have hd : @SimpleGraph.degree _ J (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hv with hv | hv
      · exact MissingColorIncidenceEndpoint G mu gamma alpha hne cm.proper v hv
      · have hj : J = TwoColorIncidenceGraph G mu alpha gamma := by
          ext x z
          cases x <;> cases z <;> simp [J, TwoColorIncidenceGraph, or_comm]
        rw [hj]
        exact MissingColorIncidenceEndpoint G mu alpha gamma hne.symm cm.proper v hv
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx z hz
    exact Finset.card_le_one_iff.mp hd
      (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hx)
      (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hz)
  have hAshort : A.length + 1 < T.length := by omega
  have hyNotA : y ∉ TreeSequenceVertexSet A := by
    intro hy
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi⟩ := hy
    have heq : T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i) =
        T.vertex (Fin.last T.length) := by
      rw [hAT.2.1 i]
      exact hi
    have hidx := congrArg Fin.val (T.vertex_injective heq)
    have hiLt := i.isLt
    simp at hidx
    omega
  have hvgNeY : vg ≠ y := by
    intro h
    exact hyNotA (h ▸ hvgInA)
  have hiaNeY : T.vertex ia ≠ y := by
    intro h
    exact hyNotA (h ▸ hiaInA)
  have hdisjoint : Disjoint Q
      (TwoColorComponent G mu gamma alpha (Sum.inl vg)) := by as_aux_lemma =>
    rcases TwoColorComponentsDisjoint G mu gamma alpha (Sum.inl y) (Sum.inl vg) with heq | hd
    · obtain ⟨u, v, path, hp, hs⟩ :=
        TwoColorComponentSpanningPath G mu gamma alpha cm.proper (Sum.inl y)
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
      change Q = TwoColorComponent G mu gamma alpha (Sum.inl vg) at heq
      have hvgQ : Sum.inl vg ∈ Q := by rw [heq]; exact self vg
      have hyQ : Sum.inl y ∈ Q := self y
      have hevg := endpoint vg hvgQ (leaf vg (Or.inl hgamvg))
      have hey := endpoint y hyQ (leaf y (Or.inr haY))
      by_cases hsameRoot : vg = T.vertex ia
      · have hboth : gamma ∈ MissingColors G mu vg ∧ alpha ∈ MissingColors G mu vg := by
          constructor
          · exact hgamvg
          · simpa [hsameRoot] using hAlphaAtFirst
        have hnoAdj : ∀ w, ¬ J.Adj (Sum.inl vg) w := by
          intro w hadj
          simp only [J, TwoColorIncidenceGraph] at hadj
          rcases w with w | f
          · simp [TwoColorIncidenceGraph] at hadj
          · rcases hadj with ⟨hinc, hcol⟩
            rcases hcol with hc | hc
            · exact (Finset.mem_sdiff.mp hboth.1).2
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f, hinc, hc⟩⟩)
            · exact (Finset.mem_sdiff.mp hboth.2).2
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f, hinc, hc⟩⟩)
        have hmem : Sum.inl vg ∈ J.connectedComponentMk (Sum.inl y) := by
          change Sum.inl vg ∈ Q
          rw [heq]
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        have hreach : J.Reachable (Sum.inl vg) (Sum.inl y) :=
          SimpleGraph.ConnectedComponent.eq.mp hmem
        have hempty : J.neighborSet (Sum.inl vg) = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun w hw =>
            hnoAdj w (by simpa only [SimpleGraph.mem_neighborSet] using hw))
        have hvgY : (Sum.inl vg : Sum V E) ≠ Sum.inl y := by
          intro h
          exact hvgNeY (Sum.inl.inj h)
        exact False.elim
          ((SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (G := J) hvgY hempty) hreach)
      · have hiaQ : Sum.inl (T.vertex ia) ∈ Q := by
          rw [heq, hsame]
          exact self (T.vertex ia)
        have heia := endpoint (T.vertex ia) hiaQ
          (leaf (T.vertex ia) (Or.inr hAlphaAtFirst))
        have hneqGA : vg ≠ T.vertex ia := hsameRoot
        have hneqGY : vg ≠ y := hvgNeY
        have hneqAY : T.vertex ia ≠ y := hiaNeY
        rcases hevg with hgu | hgv
        · rcases heia with hau | hav
          · rcases hey with hyu | hyv
            · exact False.elim (hneqGA (Sum.inl.inj (hgu.trans hau.symm)))
            · exact False.elim (hneqGA (Sum.inl.inj (hgu.trans hau.symm)))
          · rcases hey with hyu | hyv
            · exact False.elim (hneqGY (Sum.inl.inj (hgu.trans hyu.symm)))
            · exact False.elim (hneqAY (Sum.inl.inj (hav.trans hyv.symm)))
        · rcases heia with hau | hav
          · rcases hey with hyu | hyv
            · exact False.elim (hneqAY (Sum.inl.inj (hau.trans hyu.symm)))
            · exact False.elim (hneqGY (Sum.inl.inj (hgv.trans hyv.symm)))
          · rcases hey with hyu | hyv
            · exact False.elim (hneqGA (Sum.inl.inj (hgv.trans hav.symm)))
            · exact False.elim (hneqGA (Sum.inl.inj (hgv.trans hav.symm)))
    · exact hd
  have hpath : TwoColorPathComponent G mu gamma alpha (Sum.inl y) :=
    ⟨hne, Sum.inl y, self y, leaf y (Or.inr haY)⟩
  have hAstage (hp : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      simp [q] at hv
      omega
    · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
      congr 1
      apply Fin.ext
      have hv := congrArg Fin.val hr
      simpa [q] using hv.symm
  have hcase :
      (0 < H.dividerCount ∧ gamma ∈ TreeMissingColors mu
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (gamma ∈ TreeMissingColors mu Tn ∨
          (gamma ∈ TreeMissingColors mu A ∧
            gamma ∉ TashkinovStoredColors em.series.data n ∧
            alpha ∉ TashkinovStoredColors em.series.data n))) := by
    rcases hnormalized with hp | hz
    · exact Or.inl ⟨hp.1, by rw [← hAstage hp.1]; exact hgammaA⟩
    · exact Or.inr ⟨hz.1, Or.inl hgammaTn⟩
  have hvgPath : TwoColorPathComponent G mu gamma alpha (Sum.inl vg) :=
    ⟨hne, Sum.inl vg, self vg, leaf vg (Or.inl hgamvg)⟩
  have hQoutsideA : ∀ w, w ∈ TreeSequenceVertexSet A →
      Sum.inl w ∉ Q := by
    intro w hw hwQ
    have hsameComp := hinterchangeable (Sum.inl y) (Sum.inl vg) hpath hvgPath
      ⟨w, hw, hwQ⟩ ⟨vg, hvgInA, self vg⟩
    have hvgQ : Sum.inl vg ∈ Q := by
      change Sum.inl vg ∈ TwoColorComponent G mu gamma alpha (Sum.inl y)
      rw [hsameComp]
      exact self vg
    exact Set.disjoint_left.mp hdisjoint hvgQ (self vg)
  let sigma := TwoColorComponentSwap G mu gamma alpha (Sum.inl y)
  obtain ⟨missingOutside, missingGammaToAlpha, missingAlphaToGamma, missingOther⟩ :=
    TwoColorComponentSwapMissingBehavior G mu gamma alpha hne cm.proper (Sum.inl y)
  have hmissingBEquality : ∀ v, v ∈ TreeSequenceVertexSet B →
      MissingColors G sigma v = MissingColors G mu v := by as_aux_lemma =>
    clear * - J helem hAB hvgInA hiaInA hdisjoint hsame self hgamvg hAlphaAtFirst missingOther missingOutside hne
    intro w hw
    by_cases hwQ : Sum.inl w ∈ Q
    · have hwGamma : w ≠ vg := by
        intro h
        subst w
        exact Set.disjoint_left.mp hdisjoint hwQ (self vg)
      have hwAlpha : w ≠ T.vertex ia := by
        intro h
        subst w
        exact Set.disjoint_left.mp hdisjoint hwQ (by rw [hsame]; exact self (T.vertex ia))
      have hng : gamma ∉ MissingColors G mu w := fun hm =>
        Finset.disjoint_left.mp (helem hw (TreeSequenceInitialSegmentVertexSetSubset hAB hvgInA)
          hwGamma) hm hgamvg
      have hna : alpha ∉ MissingColors G mu w := fun hm =>
        Finset.disjoint_left.mp (helem hw (TreeSequenceInitialSegmentVertexSetSubset hAB hiaInA)
          hwAlpha) hm hAlphaAtFirst
      obtain ⟨fg, hfg, hfgc⟩ : ∃ f, Incident G w f ∧ mu f = some gamma := by
        simpa [MissingColors, PresentColors] using hng
      obtain ⟨fa, hfa, hfac⟩ : ∃ f, Incident G w f ∧ mu f = some alpha := by
        simpa [MissingColors, PresentColors] using hna
      have edgeOfVertex {v : V} {f : E}
          (hv : Sum.inl v ∈ Q) (hf : Incident G v f)
          (hc : mu f = some gamma ∨ mu f = some alpha) : Sum.inr f ∈ Q := by
        change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl y) at hv
        change J.connectedComponentMk (Sum.inr f) = J.connectedComponentMk (Sum.inl y)
        have hadj : J.Adj (Sum.inr f) (Sum.inl v) := by
          simpa only [J, TwoColorIncidenceGraph] using And.intro hf hc
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
      have hfgQ := edgeOfVertex hwQ hfg (Or.inl hfgc)
      have hfaQ := edgeOfVertex hwQ hfa (Or.inr hfac)
      have hnewAlpha : sigma fg = some alpha := by
        simp [sigma, TwoColorComponentSwap, Q, hfgQ, hfgc, hne.symm]
      have hnewGamma : sigma fa = some gamma := by
        simp [sigma, TwoColorComponentSwap, Q, hfaQ, hfac]
      have hnsGamma : gamma ∉ MissingColors G sigma w := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fa, hfa, hnewGamma⟩
      have hnsAlpha : alpha ∉ MissingColors G sigma w := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fg, hfg, hnewAlpha⟩
      ext c
      by_cases hcg : c = gamma
      · rw [hcg]
        simp only [hng, hnsGamma]
      by_cases hca : c = alpha
      · rw [hca]
        simp only [hna, hnsAlpha]
      exact missingOther w c hcg hca
    · exact missingOutside w hwQ
  have hgammaNewY : gamma ∈ MissingColors G sigma y :=
    missingAlphaToGamma y (self y) haY
  have he1Incident : TreeIncidentEdge A (T.edge e1) := by
    obtain ⟨i, hi⟩ := T.attaches e1
    have hiBound : i.val ≤ A.length := by
      have hiLt := i.isLt
      have heval : e1.val = A.length := by exact he1
      omega
    let iA : Fin (A.length + 1) := ⟨i.val, by omega⟩
    have hindex : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ e1.isLt)) =
        Fin.castLE (Nat.succ_le_succ hAT.1) iA := by
      apply Fin.ext
      rfl
    refine ⟨A.vertex iA, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · change A.vertex iA ∈ G.ends (T.edge e1)
      rw [← hAT.2.1 iA, hindex.symm, hi]
      simp
  have he1notQ : Sum.inr (T.edge e1) ∉ Q := by
    intro hQe
    obtain ⟨w, hwA, hwInc⟩ := he1Incident
    have hadj : J.Adj (Sum.inl w) (Sum.inr (T.edge e1)) := by
      change Incident G w (T.edge e1) ∧
        (mu (T.edge e1) = some gamma ∨ mu (T.edge e1) = some alpha)
      exact ⟨hwInc, Or.inr hfirst⟩
    have hwQ : Sum.inl w ∈ Q := by
      change J.connectedComponentMk (Sum.inl w) = J.connectedComponentMk (Sum.inl y)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hQe
    exact hQoutsideA w hwA hwQ
  have hfixedSeed : sigma (T.edge e1) = mu (T.edge e1) := by
    simp [sigma, TwoColorComponentSwap, Q, he1notQ]
  let X := TreeSequencePrefix T (A.length + 1)
    (by have := A.positive; omega) (by have := hAshort; omega)
  have hXlen : X.length = A.length + 1 := rfl
  have hXT : TreeSequenceInitialSegment X T := by
    refine ⟨hAshort.le, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have prefixOverlap {S U : TreeSequence G e0}
      (hST : TreeSequenceInitialSegment S T)
      (hUT : TreeSequenceInitialSegment U T) (hle : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hle, ?_, ?_⟩
    · intro i
      let j : Fin (U.length + 1) := Fin.castLE (Nat.succ_le_succ hle) i
      calc
        U.vertex j = T.vertex (Fin.castLE (Nat.succ_le_succ hUT.1) j) :=
          (hUT.2.1 j).symm
        _ = T.vertex (Fin.castLE (Nat.succ_le_succ hST.1) i) := by
          congr 1
        _ = S.vertex i := hST.2.1 i
    · intro i
      let j : Fin U.length := Fin.castLE hle i
      calc
        U.edge j = T.edge (Fin.castLE hUT.1 j) := (hUT.2.2 j).symm
        _ = T.edge (Fin.castLE hST.1 i) := by congr 1
        _ = S.edge i := hST.2.2 i
  have hleAX : A.length ≤ X.length := by
    rw [hXlen]
    omega
  have hAX : TreeSequenceInitialSegment A X := prefixOverlap hAT hXT hleAX
  have hAXstrict : A.length < X.length := by rw [hXlen]; omega
  have hXB : TreeSequenceInitialSegment X B := by
    have hlen : X.length ≤ B.length := by
      rw [hBlen]
      rw [hXlen]
      omega
    exact prefixOverlap hXT hBT hlen
  have hfixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = mu (T.edge t) := by
    intro t ht hlt
    have htval : t.val = A.length := by
      rw [hXlen] at hlt
      omega
    have hteq : t = e1 := Fin.ext (by rw [htval, he1])
    rw [hteq]
    exact hfixedSeed
  have hstoredFirst : ∀ eta ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta := by
    intro eta heta
    have hnotA : eta ∉ TreeMissingColors mu A := (Finset.mem_sdiff.mp heta).2
    have hηGamma : eta ≠ gamma := by
      intro he
      exact hnotA (he ▸ hgammaA)
    have hηAlpha : eta ≠ alpha := by
      intro he
      exact hnotA (he ▸ haA)
    have heq : (Finset.univ.filter fun i : Fin (T.length + 1) =>
        eta ∈ MissingColors G sigma (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
        eta ∈ MissingColors G mu (T.vertex i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact missingOther _ eta hηGamma hηAlpha
    simp only [HierarchyFirstMissingPosition, heq]
  have hgammaCutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
      (gamma ∈ Cm.good.gamma q eta ∨ alpha ∈ Cm.good.gamma q eta) →
        (HierarchyFirstMissingPosition mu T eta).val ≤ X.length := by
    clear * - X mu T H q A Cm gamma alpha R hgammaR hfirst e1 he1 hXlen
    intro eta heta hp
    have havoid := Cm.good.avoidance q eta heta
    rcases hp with hg | ha
    · exact False.elim (hgammaR (Finset.mem_biUnion.mpr ⟨eta, heta, hg⟩))
    · by_contra hnot
      have hpast : X.length < (HierarchyFirstMissingPosition mu T eta).val := by omega
      have he1A : e1.val = A.length := by simpa [A, H, q] using he1
      have hterminal : H.stage q.succ = T := by
        have hq : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
        rw [hq, H.terminalStage]
      have hsegment : alpha ∈ HierarchySegmentColors H q eta := by
        change alpha ∈ Finset.univ.filter fun c => ∃ r : Fin (H.stage q.succ).length,
          A.length ≤ r.val ∧ r.val <
            min (HierarchyFirstMissingPosition mu T eta).val (H.stage q.succ).length ∧
              mu ((H.stage q.succ).edge r) = some c
        rw [hterminal]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨e1, ?_, ?_, hfirst⟩
        · change A.length ≤ e1.val
          omega
        · apply Nat.lt_min.mpr
          constructor
          · rw [hXlen] at hpast
            omega
          · exact e1.isLt
      exact (Finset.mem_sdiff.mp (havoid ha)).2 hsegment
  have hfixedA : ∀ t : Fin A.length, sigma (A.edge t) = mu (A.edge t) := by as_aux_lemma =>
    intro t
    obtain ⟨i, hi⟩ := A.attaches t
    have htVertex : A.vertex t.succ ∈ TreeSequenceVertexSet A := by
      simp [TreeSequenceVertexSet]
    have htIncident : Incident G (A.vertex t.succ) (A.edge t) := by
      change A.vertex t.succ ∈ G.ends (A.edge t)
      rw [hi]
      simp
    by_cases hQe : Sum.inr (A.edge t) ∈ Q
    · have hcolor : mu (A.edge t) = some gamma ∨ mu (A.edge t) = some alpha := by
        have hsupp : Sum.inr (A.edge t) ∈ J.support := by
          apply SimpleGraph.mem_support_of_reachable (G := J)
            (u := Sum.inr (A.edge t)) (v := Sum.inl y) (by simp)
          exact SimpleGraph.ConnectedComponent.eq.mp hQe
        obtain ⟨z, hz⟩ := J.mem_support.mp hsupp
        cases z with
        | inl z => exact hz.2
        | inr f => simpa [J, TwoColorIncidenceGraph] using hz
      have hadj : J.Adj (Sum.inl (A.vertex t.succ)) (Sum.inr (A.edge t)) := by
        change Incident G (A.vertex t.succ) (A.edge t) ∧
          (mu (A.edge t) = some gamma ∨ mu (A.edge t) = some alpha)
        exact ⟨htIncident, hcolor⟩
      have hvQ : Sum.inl (A.vertex t.succ) ∈ Q := by
        change J.connectedComponentMk (Sum.inl (A.vertex t.succ)) =
          J.connectedComponentMk (Sum.inl y)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hQe
      exact (hQoutsideA _ htVertex hvQ).elim
    · simp [sigma, TwoColorComponentSwap, Q, hQe]
  have hfixedX : ∀ t : Fin X.length, sigma (X.edge t) = mu (X.edge t) := by
    intro t
    have htbound : t.val < A.length + 1 := by simpa only [hXlen] using t.isLt
    have htval : t.val ≤ A.length := by omega
    by_cases htSeed : t.val = A.length
    · have hteq : Fin.castLE hXT.1 t = e1 := by
        apply Fin.ext
        have hv := he1
        change e1.val = A.length at hv
        simp only [Fin.val_castLE]
        rw [hv]
        exact htSeed
      rw [← hXT.2.2 t, hteq]
      exact hfixedSeed
    · have htA : t.val < A.length := by omega
      let tA : Fin A.length := ⟨t.val, htA⟩
      have he : Fin.castLE hXT.1 t = Fin.castLE hAT.1 tA := by
        apply Fin.ext
        rfl
      rw [← hXT.2.2 t, he, hAT.2.2 tA]
      exact hfixedA tA
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro j
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) j)).trans (hSU.2.1 j)
    · intro j
      exact (hUW.2.2 (Fin.castLE hSU.1 j)).trans (hSU.2.2 j)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have coreToA : TreeSequenceInitialSegment bm.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [hAcore hz]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [hAstage (Nat.pos_of_ne_zero hz)]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
    by_cases hp : em.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (bm.parallel hp).2.2).leftSegment
    · rw [bm.nonparallel hp]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hTnA : TreeSequenceInitialSegment Tn A := segTrans TnToCore coreToA
  have transportRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence mu S X) :
      TashkinovAugmentationSequence sigma S X := by as_aux_lemma =>
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
        exact Finset.mem_biUnion.mpr ⟨v, hvU, (hmissingBEquality v hvB).symm ▸ hcv⟩
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
        TashkinovAugmentationSequence mu X T := by as_aux_lemma =>
    have old := P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu em
    rcases old with ⟨hkind, hroute⟩ |
      ⟨hkind, f, seed, hedges, hadjoin, hincident, hcolor, hroute⟩
    · have hTnX := segTrans hTnA hAX
      have hrouteX := TashkinovAugmentationSequenceRestrict mu Tn X T hroute hTnX hXT
      exact ⟨Or.inl ⟨hkind, transportRoute Tn hrouteX⟩,
        TashkinovAugmentationSequenceSuffix mu Tn X T hroute hTnX hXT⟩
    · have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T hroute
      have hseedX : TreeSequenceInitialSegment seed X :=
        prefixOverlap hseedT hXT (by
          have hseedLen := hadjoin.1
          change seed.length = Tn.length + 1 at hseedLen
          have := hTnA.1
          simp only [X, TreeSequencePrefix]
          omega)
      have hrouteX := TashkinovAugmentationSequenceRestrict mu seed X T hroute hseedX hXT
      exact ⟨Or.inr ⟨hkind, f, seed, hedges, hadjoin, transportRoute seed hrouteX⟩,
        TashkinovAugmentationSequenceSuffix mu seed X T hroute hseedX hXT⟩
  have hsplitMissing : gamma ∈ TreeMissingColors sigma X ∧ alpha ∈ TreeMissingColors sigma X := by
    constructor
    · obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAX hv,
          (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩
    · obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp haA
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAX hv,
          (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩
  obtain ⟨_, _, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      gamma alpha hne
      (by
        change gamma ∈ TreeMissingColors mu
            (HierarchyFullTailPrefix Cm (HierarchyFullTailLength Cm - 1)) ∧
          alpha ∈ TreeMissingColors mu
            (HierarchyFullTailPrefix Cm (HierarchyFullTailLength Cm - 1))
        exact ⟨hmissingGammaB, hmissingAlphaB⟩)
      (Sum.inl y) hpath sigma rfl hcase
      hdisjoint X hAX hAXstrict hXB hfixedPrefix routes.1 routes.2 hsplitMissing
      hmissingBEquality hstoredFirst hgammaCutoff
  have hgammaSigmaA : gamma ∈ TreeMissingColors sigma A := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr
      ⟨v, hv, (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩
  have hvTerminal : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  let Cs : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact Cm.positive
    hierarchy := K
    good := good
    maximum := hmax
    notElementary := by
      intro he
      obtain ⟨v, hvA, hmv⟩ := Finset.mem_biUnion.mp hgammaSigmaA
      have hvT := TreeSequenceInitialSegmentVertexSetSubset hAT hvA
      have hneq : v ≠ y := by
        intro h
        exact hyNotA (h ▸ hvA)
      exact Finset.disjoint_left.mp (he hvT hvTerminal hneq) hmv hgammaNewY }
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  by_cases hnoCommonPnew :
      ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
        Disjoint
          (MissingColors G Pnew.coloring
            ((HierarchyFullTailPrefix C i).vertex
              (Fin.last (HierarchyFullTailPrefix C i).length)))
          (MissingColors G Pnew.coloring y)
  swap
  · simp only [not_forall, _root_.not_imp] at hnoCommonPnew
    obtain ⟨i, hi, hd⟩ := hnoCommonPnew
    obtain ⟨beta, hb, hby⟩ := Finset.not_disjoint_iff.mp hd
    refine ⟨i, ?_⟩
    change i ∈ (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter _
    exact Finset.mem_filter.mpr ⟨hi, Pnew, beta, hb, hby⟩
  have hmeasureNew := P2752_T2_HierarchyMeasures H K same.1
  have hmeasurePnew := P2752_T2_HierarchyMeasures C.hierarchy
    Pnew.counterexample.hierarchy Pnew.sameGood.1
  have hmeasureOld := P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1
  have hnewSituation : HierarchyPathNumber K = 1 := by
    calc
      HierarchyPathNumber K = HierarchyPathNumber H := hmeasureNew.2.1.symm
      _ = 1 := hsituation
  have hnewSituationPnew :
      HierarchyPathNumber Pnew.counterexample.hierarchy = 1 := by
    calc
      HierarchyPathNumber Pnew.counterexample.hierarchy =
          HierarchyPathNumber C.hierarchy := hmeasurePnew.2.1.symm
      _ = HierarchyPathNumber H := hmeasureOld.2.1
      _ = 1 := hsituation
  have hstarNew : HierarchyStarredStage H q =
      HierarchyStarredStage K (Fin.last K.dividerCount) := hmeasureNew.1
  have hstarPnew : HierarchyStarredStage H q =
      HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount) :=
    hmeasureOld.1.symm.trans hmeasurePnew.1
  have hKstarLen : (HierarchyStarredStage K (Fin.last K.dividerCount)).length =
      A.length := by
    change (HierarchyStarredStage K (Fin.last K.dividerCount)).length =
      (HierarchyStarredStage H q).length
    rw [← hstarNew]
  have hgammaNewA : gamma ∈ TreeMissingColors sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) := by
    rw [← hstarNew]
    exact hgammaSigmaA
  have hgammaSigmaTn : gamma ∈ TreeMissingColors sigma Tn := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaTn
    have hvA := TreeSequenceInitialSegmentVertexSetSubset hTnA hv
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
    exact Finset.mem_biUnion.mpr ⟨v, hv, (hmissingBEquality v hvB).symm ▸ hmv⟩
  have hterminalTree : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive series above strict below generating =>
      cases rungAgreement
      have hseries : series = replacementSeries := eq_of_heq seriesPresentation
      cases hseries
      let i : Fin em.rounds := ⟨em.rounds - 1, by have hp := em.roundsPositive; omega⟩
      have hi : i.succ = Fin.last em.rounds := by
        apply Fin.ext
        change em.rounds - 1 + 1 = em.rounds
        exact Nat.sub_add_cancel em.roundsPositive
      simpa [Tn, n, hi] using ladderTreesAgree i
  have terminalTreeOf (coloring : PartialEdgeColoring E k)
      (c : CorrespondingExtendedTashkinovTree G k e0 ett coloring T) :
      c.replacementETT.series.data.tree
          (Fin.last c.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by as_aux_lemma =>
    rcases c with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive series above strict below generating =>
      cases rungAgreement
      have hseries : series = replacementSeries := eq_of_heq seriesPresentation
      cases hseries
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by
        have hp := ett.roundsPositive
        omega⟩
      have hi : i.succ = Fin.last ett.rounds := by
        apply Fin.ext
        change ett.rounds - 1 + 1 = ett.rounds
        exact Nat.sub_add_cancel ett.roundsPositive
      simpa [hi] using ladderTreesAgree i
  have hterminalOriginal := terminalTreeOf Pnew.coloring Pnew.corresponding
  have hterminalEm := terminalTreeOf P.coloring P.corresponding
  have hterminalPnewTn : Pnew.corresponding.replacementETT.series.data.tree
      (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc = Tn := by
    exact hterminalOriginal.trans (hterminalEm.symm.trans (by rfl))
  have treeMissingColorEq (c₁ c₂ : PartialEdgeColoring E k)
      (hc : c₁ = c₂) (U : TreeSequence G e0) :
      TreeMissingColors c₁ U = TreeMissingColors c₂ U := by
    cases hc
    rfl
  have missingColorEq (c₁ c₂ : PartialEdgeColoring E k)
      (hc : c₁ = c₂) (v : V) :
      MissingColors G c₁ v = MissingColors G c₂ v := by
    cases hc
    rfl
  have hPnewStarLen :
      (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length = A.length := by
    change (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length =
      (HierarchyStarredStage H q).length
    rw [hstarPnew]
  have hgammaNewTerminal : gamma ∈ TreeMissingColors Pnew.coloring
      (Pnew.corresponding.replacementETT.series.data.tree
        (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc) := by
    have h : gamma ∈ TreeMissingColors sigma
        (Pnew.corresponding.replacementETT.series.data.tree
          (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc) := by
      rw [hterminalPnewTn]
      exact hgammaSigmaTn
    rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
    exact h
  have hnormalizedNew :
      (0 < K.dividerCount ∧ gamma ∈ TreeMissingColors Pnew.coloring
        (K.stage ⟨K.dividerCount, by omega⟩)) ∨
      (K.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.corresponding.replacementETT.series.data.tree
            (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc)) := by
    rcases hcase with hp | hz
    · left
      have hcount : H.dividerCount = K.dividerCount := same.1.2.1
      refine ⟨?_, ?_⟩
      · simpa [hcount] using hp.1
      · have hgammaKstage : gamma ∈ TreeMissingColors sigma
            (K.stage ⟨K.dividerCount, by omega⟩) := by
          rw [← hmeasureNew.2.2, ← hAstage hp.1]
          exact hgammaSigmaA
        rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
        exact hgammaKstage
    · right
      have hcount : H.dividerCount = K.dividerCount := same.1.2.1
      refine ⟨?_, ?_⟩
      · simpa [hcount] using hz.1
      · exact hgammaNewTerminal
  have hstartNew :
      gamma ∈ TreeMissingColors Pnew.coloring
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        gamma ∈ MissingColors G Pnew.coloring y := by
    rw [hPnew]
    exact ⟨hgammaNewA, hgammaNewY⟩
  have hstartPnew :
      gamma ∈ TreeMissingColors Pnew.coloring
          (HierarchyStarredStage Pnew.counterexample.hierarchy
            (Fin.last Pnew.counterexample.hierarchy.dividerCount)) ∧
        gamma ∈ MissingColors G Pnew.coloring
      (T.vertex (Fin.last T.length)) := by
    constructor
    · have h : gamma ∈ TreeMissingColors sigma
          (HierarchyStarredStage Pnew.counterexample.hierarchy
            (Fin.last Pnew.counterexample.hierarchy.dividerCount)) := by
        rw [← hstarPnew]
        exact hgammaSigmaA
      rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
      exact h
    · rw [missingColorEq Pnew.coloring sigma hPnew _]
      exact hgammaNewY
  have hcountKP : K.dividerCount =
      Pnew.counterexample.hierarchy.dividerCount := by
    calc
      K.dividerCount = H.dividerCount := same.1.2.1.symm
      _ = C.hierarchy.dividerCount := P.sameGood.1.2.1.symm
      _ = Pnew.counterexample.hierarchy.dividerCount := Pnew.sameGood.1.2.1
  have hstageKP : K.stage ⟨K.dividerCount, by omega⟩ =
      Pnew.counterexample.hierarchy.stage
        ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩ := by
    calc
      K.stage ⟨K.dividerCount, by omega⟩ = H.stage ⟨H.dividerCount, by omega⟩ :=
        hmeasureNew.2.2.symm
      _ = C.hierarchy.stage ⟨C.hierarchy.dividerCount, by omega⟩ :=
        hmeasureOld.2.2.symm
      _ = Pnew.counterexample.hierarchy.stage
          ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩ :=
        hmeasurePnew.2.2
  have hnormalizedPnew :
      (0 < Pnew.counterexample.hierarchy.dividerCount ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.counterexample.hierarchy.stage
            ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩)) ∨
      (Pnew.counterexample.hierarchy.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.corresponding.replacementETT.series.data.tree
            (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc)) := by as_aux_lemma =>
    rcases hnormalizedNew with hp | hz
    · left
      refine ⟨?_, ?_⟩
      · rw [← hcountKP]
        exact hp.1
      · rw [← hstageKP]
        exact hp.2
    · right
      refine ⟨?_, hgammaNewTerminal⟩
      rw [← hcountKP]
      exact hz.1
  by_cases hunused : ∀ t : Fin T.length, A.length ≤ t.val →
      sigma (T.edge t) ≠ some gamma
  · have hunusedNew :
        ∀ t : Fin T.length,
          (HierarchyStarredStage Pnew.counterexample.hierarchy
            (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length ≤ t.val →
            Pnew.coloring (T.edge t) ≠ some gamma := by
      intro t ht hc
      have htA : A.length ≤ t.val := by rw [← hPnewStarLen]; exact ht
      have hc' : sigma (T.edge t) = some gamma := by rw [← hPnew]; exact hc
      exact hunused t htA hc'
    exact ⟨HierarchyFullTailLength C - 1,
      HierarchyClaimNineUnusedTailColor G k e0 input T phi ett base C ctx
      hvertexMissing Pnew hnewSituationPnew gamma hstartPnew
      hnormalizedPnew hnoCommonPnew hunusedNew⟩
  · let S : Finset (Fin T.length) :=
      Finset.univ.filter fun t => A.length ≤ t.val ∧ sigma (T.edge t) = some gamma
    have hS : S.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      apply hunused
      intro t ht
      by_contra hc
      have htmem : t ∈ S := by simp [S, ht, hc]
      rw [hempty] at htmem
      simp at htmem
    let ej : Fin T.length := S.min' hS
    have hejMem : ej ∈ S := Finset.min'_mem S hS
    have hejData := (Finset.mem_filter.mp hejMem).2
    have hejColor : sigma (T.edge ej) = some gamma := hejData.2
    have hseedIndex : e1.val = A.length := by exact he1
    have hseedNotGamma : sigma (T.edge e1) ≠ some gamma := by
      have hcolor : mu (T.edge e1) = some alpha := by simpa [mu] using hfirst
      rw [hfixedSeed, hcolor]
      exact fun h => hgammaNe (Option.some.inj h).symm
    have hAej : A.length < ej.val := by
      have hmin : ej.val ≤ e1.val ∨ e1.val ≤ ej.val := le_total ej.val e1.val
      by_contra hn
      have heq : ej.val = A.length := by omega
      have hteq : ej = e1 := Fin.ext (by rw [heq, hseedIndex])
      exact hseedNotGamma (hteq ▸ hejColor)
    let j : ℕ := ej.val - A.length + 1
    have hjLower : 2 ≤ j := by dsimp [j]; omega
    have hjUpper : j ≤ HierarchyFullTailLength C := by
      rw [hell]
      have hejl := ej.isLt
      dsimp [j]
      omega
    have hej : ej.val = A.length + (j - 1) := by
      dsimp only [j]
      clear * - hAej
      omega
    have hfirstNew : Pnew.coloring (T.edge ej) = some gamma ∧
        ∀ t : Fin T.length, A.length ≤ t.val → t.val < ej.val →
          Pnew.coloring (T.edge t) ≠ some gamma := by
      constructor
      · rw [hPnew]
        exact hejColor
      · intro t ht hlt hc
        have hc' : sigma (T.edge t) = some gamma := by rw [← hPnew]; exact hc
        have hmem : t ∈ S := by simp [S, ht, hc']
        have hmin : ej.val ≤ t.val := Finset.min'_le S t hmem
        omega
    have hejNew : ej.val =
        (HierarchyStarredStage Pnew.counterexample.hierarchy
          (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length + (j - 1) := by
      rw [hPnewStarLen]
      exact hej
    have hfirstNewK :
        Pnew.coloring (T.edge ej) = some gamma ∧
          ∀ t : Fin T.length,
            (HierarchyStarredStage Pnew.counterexample.hierarchy
              (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length ≤ t.val →
              t.val < ej.val → Pnew.coloring (T.edge t) ≠ some gamma := by
      refine ⟨hfirstNew.1, ?_⟩
      intro t ht hlt hc
      apply hfirstNew.2 t
      · rw [hPnewStarLen] at ht
        exact ht
      · exact hlt
      · exact hc
    have hjEligible := HierarchyClaimNineFirstUseAfterSeed G k e0 input T phi ett base C ctx
      hvertexMissing Pnew hnewSituationPnew gamma hstartPnew
      hnormalizedPnew hnoCommonPnew j hjLower hjUpper ej hejNew hfirstNewK
    exact ⟨j - 1, hjEligible⟩
