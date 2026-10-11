import Tablet.P2905_T2_EmptyCommonMissingLocation
import Tablet.P2905_T2_BaseExtraReplacement
import Tablet.P2905_T2_AbsentOwnerReplacement
import Tablet.P2905_T2_LateOwnerReplacement
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTerminalCommonMissing
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationThreeClaimJMinusOneNonempty
import Tablet.HierarchySituationThreeEligibleIndexBound
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.NineN
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.StableChangeCasesOneTwoStarredTail
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColoringInvariant
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.HierarchyWeaklyStable

set_option maxHeartbeats 600000

-- [TABLET NODE: HierarchySituationThreeClaimJMinusOneEmpty]
theorem HierarchySituationThreeClaimJMinusOneEmpty {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (hempty : ¬ (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      ∃ alpha : Fin k,
        let H := P.counterexample.hierarchy
        let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
        let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
          Fin.last P.corresponding.replacementETT.rounds
        let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
        let B := HierarchyFullTailPrefix C
          (HierarchyPathNumber C.hierarchy - 2)
        let D := HierarchyStoredColorsAt H q
        let Gamma := D.biUnion (P.counterexample.good.gamma q)
        let baseExtraMissing :=
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)
        alpha ∈ MissingColors G P.coloring
            (T.vertex (Fin.last T.length)) ∧
          alpha ∈ TreeMissingColors P.coloring B ∧
          (alpha ∉ Gamma ∪ baseExtraMissing ∨
            ∃ eta : Fin k, eta ∈ D ∧
              alpha ∈ P.counterexample.good.gamma q eta ∧
              (HierarchyFirstMissingPosition P.coloring T eta).val ≤
                B.length) := by
-- BODY
  classical
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by as_aux_lemma =>
    clear * - hXZ hYZ hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by as_aux_lemma =>
    intro j
    cases ett.series.certified j with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
      simpa [initialColoring] using triple.2.2.2.1
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact choice.selectedProper
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension => exact currentProper
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact previousProper
  have seriesOne : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by as_aux_lemma =>
    intro j
    cases ett.series.certified j with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
      simpa [initialColoring] using triple.2.2.2.2
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact choice.selectedOneUncolored
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension => exact currentOneUncolored
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact previousOneUncolored
  let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := seriesProper
    replacementOneUncolored := seriesOne
    replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := phi
    corresponding := selfCorr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    minimumContext := ctx }
  let j := HierarchyPathNumber C.hierarchy
  let ell := HierarchyFullTailLength C
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  let B := HierarchyFullTailPrefix C (ell - 1)
  let Y := HierarchyFullTailPrefix C (j - 2)
  let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
  have hAT : TreeSequenceInitialSegment A T := by
    have starNext (i : Fin (C.hierarchy.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy i)
          (C.hierarchy.stage i.succ) :=
      Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) i
    simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
      starNext (Fin.last C.hierarchy.dividerCount)
  have htail : 3 ≤ ell := by change j < ell at hpathUpper; change 2 ≤ j at hpathLower; omega
  have hell : ell = T.length - A.length := rfl
  have prefixLen (r : ℕ) (hr : r ≤ ell) :
      (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
    change min (A.length + r) T.length = A.length + r
    apply Nat.min_eq_left
    omega
  have prefixT (r : ℕ) :
      TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBLen : B.length = T.length - 1 := by
    have := prefixLen (ell - 1) (by omega)
    change B.length = A.length + (ell - 1) at this
    omega
  have hYLen : Y.length = A.length + (j - 2) := prefixLen _ (by
    change j < ell at hpathUpper; omega)
  have hAB : TreeSequenceInitialSegment A B := common hAT (prefixT _) (by omega)
  have hAY : TreeSequenceInitialSegment A Y := common hAT (prefixT _) (by omega)
  have hYB : TreeSequenceInitialSegment Y B := common (prefixT _) (prefixT _) (by
    change j < ell at hpathUpper; omega)
  have missingMono {X Z : TreeSequence G e0}
      (psi : PartialEdgeColoring E k) (hXZ : TreeSequenceInitialSegment X Z) :
      TreeMissingColors psi X ⊆ TreeMissingColors psi Z := by as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXZ hv, hm⟩
  have vertexMem (U : TreeSequence G e0) (i : Fin (U.length + 1)) :
      U.vertex i ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
      HierarchyFirstMissingPosition psi T c ≤ j := by as_aux_lemma =>
    clear * - G T psi c j hj
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hn : candidates.Nonempty := ⟨j, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hn]
    exact Finset.min'_le candidates j hm
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by as_aux_lemma =>
    clear * - G T psi c hlt
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
        unfold HierarchyFirstMissingPosition
        rw [dif_neg hn]
        rfl
      omega
  have eligible
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ ell - 1)
      (hc : c ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C i).vertex
          (Fin.last (HierarchyFullTailPrefix C i).length)))
      (hterm : c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
      I.Nonempty := by as_aux_lemma =>
    refine ⟨i, ?_⟩
    change i ∈ (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hi, P, c, hc, hterm⟩
  have emptyReduction := P2905_T2_EmptyCommonMissingLocation
    G k e0 input T phi ett base C ctx hpathLower hpathUpper hempty
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  obtain ⟨alpha, haPen, haTerminal⟩ :=
    HierarchyCounterexampleTerminalCommonMissing G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have haA : alpha ∈ TreeMissingColors phi A := emptyReduction P0 alpha haPen haTerminal
  have haY : alpha ∈ TreeMissingColors phi Y := missingMono phi hAY haA
  let q := Fin.last C.hierarchy.dividerCount
  let D := HierarchyStoredColorsAt C.hierarchy q
  let Gamma := D.biUnion (C.good.gamma q)
  let Extra := ((TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion
        fun v => MissingColors G phi v)
  by_cases hfree : alpha ∉ Gamma ∪ Extra
  · exact ⟨P0, alpha, haTerminal, haY, Or.inl hfree⟩
  by_cases hgamma : alpha ∈ Gamma
  · obtain ⟨eta, heta, haGamma⟩ := Finset.mem_biUnion.mp hgamma
    by_cases howner : eta ∈ TreeMissingColors phi B
    · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp howner
      obtain ⟨x, hx⟩ : ∃ x, B.vertex x = v := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
      have hmT : eta ∈ MissingColors G phi
          (T.vertex (Fin.castLE (Nat.succ_le_succ (prefixT (ell - 1)).1) x)) := by
        rw [(prefixT (ell - 1)).2.1, hx]; exact hm
      have hfLe := firstLe phi eta _ hmT
      have hfLt : (HierarchyFirstMissingPosition phi T eta).val < T.length := by
        change (HierarchyFirstMissingPosition phi T eta).val ≤ x.val at hfLe
        have := x.isLt
        omega
      have hmFirst := firstMem phi eta hfLt
      have hnotA : eta ∉ TreeMissingColors phi A := (Finset.mem_sdiff.mp heta).2
      have hfPos : A.length < (HierarchyFirstMissingPosition phi T eta).val := by
        by_contra hh
        have hle : (HierarchyFirstMissingPosition phi T eta).val ≤ A.length := by omega
        let a : Fin (A.length + 1) := ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
        have hidx : Fin.castLE (Nat.succ_le_succ hAT.1) a =
            HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
        apply hnotA
        refine Finset.mem_biUnion.mpr ⟨A.vertex a, vertexMem A a, ?_⟩
        rw [← hAT.2.1 a, hidx]
        exact hmFirst
      by_cases hsmall : (HierarchyFirstMissingPosition phi T eta).val ≤ Y.length
      · exact ⟨P0, alpha, haTerminal, haY, Or.inr ⟨eta, heta, haGamma, hsmall⟩⟩
      let t := (HierarchyFirstMissingPosition phi T eta).val - A.length
      have htpos : 1 ≤ t := by dsimp [t]; omega
      have htupper : t < ell := by dsimp [t]; omega
      have htlate : j - 1 ≤ t := by dsimp [t]; omega
      have hfirst : (HierarchyFirstMissingPosition phi T eta).val = A.length + t := by
        dsimp [t]; omega
      have hmTail : eta ∈ MissingColors G phi
          ((HierarchyFullTailPrefix C t).vertex
            (Fin.last (HierarchyFullTailPrefix C t).length)) := by
        rw [← (prefixT t).2.1]
        have hp := prefixLen t (by omega)
        have hidx : Fin.castLE (Nat.succ_le_succ (prefixT t).1)
            (Fin.last (HierarchyFullTailPrefix C t).length) =
            HierarchyFirstMissingPosition phi T eta := by
          apply Fin.ext
          simp only [Fin.val_castLE, Fin.val_last]
          omega
        rw [hidx]
        exact hmFirst
      obtain ⟨P, hterm, htailMissing⟩ := P2905_T2_LateOwnerReplacement
        G k e0 input T phi ett base C ctx hpathLower hpathUpper
        alpha haTerminal haA eta heta haGamma t htpos htupper htlate hfirst hmTail
      exact HierarchySituationThreeClaimJMinusOneNonempty G k e0 input T phi
        ett base C ctx hpathLower hpathUpper hvertexMissing
        (eligible P eta t ⟨htpos, by omega⟩ htailMissing hterm)
    · obtain ⟨P, beta, hterm, hbX, hbad⟩ := P2905_T2_AbsentOwnerReplacement
        G k e0 input T phi ett base C ctx hpathLower hpathUpper
        alpha haTerminal haA eta heta haGamma howner
      have hXB : TreeSequenceInitialSegment
          (HierarchyFullTailPrefix C (ell - 2)) B :=
        common (prefixT _) (prefixT _) (by
          rw [prefixLen _ (by omega), hBLen]; omega)
      have hbA := emptyReduction P beta (missingMono P.coloring hXB hbX) hterm
      exact ⟨P, beta, hterm, missingMono P.coloring hAY hbA, Or.inl hbad⟩
  · have hextra : alpha ∈ Extra := by
      have hmem : alpha ∈ Gamma ∪ Extra := by simpa only [not_not] using hfree
      exact (Finset.mem_union.mp hmem).resolve_left hgamma
    obtain ⟨P, beta, hterm, hbA, hbad⟩ := P2905_T2_BaseExtraReplacement
      G k e0 input T phi ett base C ctx hpathLower hpathUpper
      alpha haTerminal haA hextra hgamma
    exact ⟨P, beta, hterm, missingMono P.coloring hAY hbA, Or.inl hbad⟩
