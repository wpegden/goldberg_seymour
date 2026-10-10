import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyWeaklyStable
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.NineN
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TwoColorComponentSwapProper
import Tablet.IsOneEdgeUncolored
import Tablet.sc2
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.HierarchySituationTwoSubcaseOneOneNonexceptional
import Tablet.HkuTreeColorsControlled
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Mathlib.Data.Finset.Option

-- [TABLET NODE: HierarchySituationTwoSubcaseOneOneStoredException]
theorem HierarchySituationTwoSubcaseOneOneStoredException {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneData
      G k e0 input T phi ett base C ctx)
    (eta : Fin k)
    (hetaStored : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount))
    (hthetaPair :
      D.theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (hetaMissing :
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
    False := by
-- BODY
  classical
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have hierarchyGeometry
      {inp col : PartialEdgeColoring E k}
      {J : ExtendedTashkinovTree G k e0 inp T col}
      {b : HierarchyBase J col} (H : TashkinovHierarchy J b) :
      TreeSequenceInitialSegment
        (HierarchyStarredStage H (Fin.last H.dividerCount)) T ∧
      TreeSequenceInitialSegment
        (J.series.data.tree (Fin.last J.rounds).castSucc)
        (HierarchyStarredStage H (Fin.last H.dividerCount)) := by
    have forward : ∀ (a d : ℕ), (hbound : a + d ≤ H.dividerCount + 1) →
        TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
          (H.stage ⟨a + d, by omega⟩) := by
      intro a d
      induction d with
      | zero => intro h; exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
      | succ d ih =>
        intro h
        exact segmentTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let Tn := J.series.data.tree (Fin.last J.rounds).castSucc
    change TreeSequenceInitialSegment A T ∧ TreeSequenceInitialSegment Tn A
    have hTnCore : TreeSequenceInitialSegment Tn b.core := by
      by_cases hp : J.series.data.kind (Fin.last J.rounds) =
          some TashkinovExtensionKind.PE
      · exact (b.parallel hp).2.2.some.leftSegment
      · rw [b.nonparallel hp]
        exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    by_cases hq : H.dividerCount = 0
    · have hA : A = b.core := by
        simp [A, HierarchyStarredStage, Fin.last, hq]
      have hlast : H.stage ⟨1, by omega⟩ = T := by
        convert H.terminalStage using 1
        apply congrArg H.stage
        apply Fin.ext
        simp [hq]
      constructor
      · rw [hA]
        exact Eq.mp (congrArg (fun W : TreeSequence G e0 =>
          TreeSequenceInitialSegment b.core W) hlast) H.coreInsideFirst
      · rw [hA]
        exact hTnCore
    · have hpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hq
      have hindex : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
          (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp
        omega
      have hA : A = H.stage ⟨H.dividerCount, by omega⟩ := by
        dsimp [A, HierarchyStarredStage]
        rw [hindex]
        dsimp
        apply congrArg H.stage
        apply Fin.ext
        simp
        omega
      have hlast : H.stage ⟨H.dividerCount + 1, by omega⟩ = T := H.terminalStage
      have hTnStage : H.stage (0 : Fin (H.dividerCount + 2)) = Tn := H.baseStage
      refine ⟨?_, ?_⟩
      · simpa [hA, hlast] using forward H.dividerCount 1 (by omega)
      · simpa [hA, hTnStage] using forward 0 H.dividerCount (by omega)
  have missingMono {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (col : PartialEdgeColoring E k) :
      TreeMissingColors col X ⊆ TreeMissingColors col Y := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hcv⟩
  have firstMissing (col : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1)) (hc : c ∈ MissingColors G col (T.vertex i)) :
      c ∈ MissingColors G col
          (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
        (HierarchyFirstMissingPosition col T c).val ≤ i.val := by
    let S := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G col (T.vertex j)
    have hs : S.Nonempty := ⟨i, by simp [S, hc]⟩
    have heq : HierarchyFirstMissingPosition col T c = S.min' hs := by
      simp [HierarchyFirstMissingPosition, S, hs]
    rw [heq]
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem S hs)).2,
      Finset.min'_le S i (by simp [S, hc])⟩
  let H := C.hierarchy
  let q := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let X := HierarchyFullTailPrefix C (ell - 1)
  have hAT : TreeSequenceInitialSegment A T := (hierarchyGeometry H).1
  have hell : ell = T.length - A.length := rfl
  have htail : 2 ≤ ell := D.tailAtLeastTwo
  have hBlen : B.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    rw [hell]
    omega
  have hXlen : X.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    rw [hell]
    omega
  have hPenVal : D.penultimateVertexIndex.val = X.length := by
    rw [hXlen]
    have hp := D.penultimateVertexPosition
    omega
  have hLastVal : D.lastEdgeIndex.val = X.length := by
    rw [hXlen]
    have hp := D.lastEdgePosition
    omega
  have hTlen : X.length + 1 = T.length := by
    rw [hXlen]
    have hp := T.positive
    omega
  have hXexact : X.length = A.length + (ell - 1) := by
    rw [hXlen]
    omega
  have hEllone : 1 ≤ ell - 1 := by omega
  have hElllt : ell - 1 < ell := by omega
  have hXT : TreeSequenceInitialSegment X T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hAX : TreeSequenceInitialSegment A X :=
    commonPrefix hAT hXT (by rw [hXlen]; omega)
  have hAB : TreeSequenceInitialSegment A B :=
    commonPrefix hAT
      ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
      (by rw [hBlen]; omega)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet X) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hyp : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X := by
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    refine ⟨Fin.last X.length, Finset.mem_univ _, ?_⟩
    change T.vertex _ = T.vertex _
    apply congrArg T.vertex
    apply Fin.ext
    change X.length = D.penultimateVertexIndex.val
    rw [hXlen]
    have hp := D.penultimateVertexPosition
    omega
  have uniquePenultimate (c : Fin k)
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    have hm := firstMissing phi c D.penultimateVertexIndex hc
    have hv : T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet X := by
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨⟨(HierarchyFirstMissingPosition phi T c).val, by
        have hp := D.penultimateVertexPosition
        rw [hXlen]
        omega⟩, Finset.mem_univ _, ?_⟩
      rfl
    by_contra hi
    have hn : T.vertex (HierarchyFirstMissingPosition phi T c) ≠
        T.vertex D.penultimateVertexIndex := fun h => hi (T.vertex_injective h)
    exact Finset.disjoint_left.mp (helem hv hyp hn) hm.1 hc
  have hetaFirst := uniquePenultimate eta hetaMissing
  have alphaFirst := uniquePenultimate D.alpha D.alphaMissingPenultimate
  have hcard : (C.good.gamma q D.alpha).card = 2 :=
    C.good.twoColors q D.alpha D.alphaStored
  obtain ⟨gamma, hgamma, hthetaGamma⟩ :
      ∃ gamma, gamma ∈ C.good.gamma q D.alpha ∧ D.theta ≠ gamma := by
    by_contra hn
    push_neg at hn
    have hsubset : C.good.gamma q D.alpha ⊆ {D.theta} := by
      intro c hc
      simp only [Finset.mem_singleton]
      exact (hn c hc).symm
    have hle := Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hle
    omega
  have hgammaAvoid := Finset.mem_sdiff.mp
    (C.good.avoidance q D.alpha D.alphaStored hgamma)
  have hgammaA : gamma ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 D.alpha D.alphaStored hgamma
  obtain ⟨gammaVertex, gammaVertexA, gammaAtVertex⟩ :=
    (Finset.mem_biUnion (s := TreeSequenceVertexSet A)
      (t := fun v => MissingColors G phi v)).mp hgammaA
  have hgammaAlpha : gamma ≠ D.alpha := by
    intro he
    exact (Finset.mem_sdiff.mp D.alphaStored).2 (he ▸ hgammaA)
  have hgammaTail : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some gamma := by
    intro t ht hc
    by_cases hlast : t = D.lastEdgeIndex
    · have htg : D.theta = gamma :=
        Option.some.inj (D.thetaOnLastEdge.symm.trans (hlast ▸ hc))
      exact hthetaGamma htg
    · have hpos : t.val < D.penultimateVertexIndex.val := by
        have hp := D.penultimateVertexPosition
        have he := D.lastEdgePosition
        have htlt := t.isLt
        have hneq : t.val ≠ D.lastEdgeIndex.val := fun h => hlast (Fin.ext h)
        omega
      apply hgammaAvoid.2
      unfold HierarchySegmentColors
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hend : H.stage q.succ = T := H.terminalStage
      let r : Fin (H.stage q.succ).length :=
        Fin.cast (congrArg TreeSequence.length hend.symm) t
      refine ⟨r, ht, ?_, ?_⟩
      · simp only [alphaFirst]
        dsimp [r]
        rw [hend]
        omega
      · have edgeCast (U W : TreeSequence G e0) (h : U = W)
            (i : Fin W.length) :
            U.edge (Fin.cast (congrArg TreeSequence.length h.symm) i) = W.edge i := by
          cases h
          rfl
        change phi ((H.stage q.succ).edge r) = some gamma
        rw [edgeCast _ _ hend t]
        exact hc
  have starCongr (n m : ℕ) (coreLeft coreRight : TreeSequence G e0)
      (stageLeft : Fin (n + 2) → TreeSequence G e0)
      (stageRight : Fin (m + 2) → TreeSequence G e0)
      (hnm : n = m) (hcore : coreLeft = coreRight)
      (hstage : HEq stageLeft stageRight) :
      Fin.cases (motive := fun _ => TreeSequence G e0) coreLeft
          (fun i : Fin n => stageLeft i.succ.castSucc) (Fin.last n) =
        Fin.cases (motive := fun _ => TreeSequence G e0) coreRight
          (fun i : Fin m => stageRight i.succ.castSucc) (Fin.last m) := by
    subst m
    have hs := eq_of_heq hstage
    simp [hcore, hs]
  have presentationGeometry
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) = A ∧
        HierarchyFullTailLength P.counterexample = ell ∧
        HierarchyFullTailPrefix P.counterexample (ell - 1) = X ∧
        HierarchyPathNumber P.counterexample.hierarchy = HierarchyPathNumber H := by
    have hs := P.sameGood.1
    have hstar : HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A :=
      (starCongr _ _ base.core P.replacementBase.core H.stage
        P.counterexample.hierarchy.stage hs.2.1 hs.1 hs.2.2.1).symm
    refine ⟨hstar, ?_, ?_, ?_⟩
    · change T.length - _ = ell
      rw [hstar]
      rfl
    · simp only [HierarchyFullTailPrefix, hstar]
      rfl
    · simp only [HierarchyPathNumber, hstar]
      rfl
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
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
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
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
  have caseFor
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a : Fin k)
      (ha : a ∈ HierarchyStageMissingColors P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)) :
      (0 < P.counterexample.hierarchy.dividerCount ∧
        a ∈ TreeMissingColors P.coloring (P.counterexample.hierarchy.stage
          ⟨P.counterexample.hierarchy.dividerCount, by omega⟩)) ∨
      (P.counterexample.hierarchy.dividerCount = 0 ∧
        a ∈ TreeMissingColors P.coloring
          (P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc)) := by
    let K := P.counterexample.hierarchy
    let r := Fin.last K.dividerCount
    change a ∈ HierarchyStageMissingColors K r at ha
    by_cases hz : K.dividerCount = 0
    · right
      refine ⟨hz, ?_⟩
      have hi : r = 0 := by apply Fin.ext; simp [r, hz]
      simpa [HierarchyStageMissingColors, hi] using ha
    · left
      refine ⟨Nat.pos_of_ne_zero hz, ?_⟩
      have hi : r = (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ := by
        apply Fin.ext
        simp [r]
        omega
      change a ∈ HierarchyStageMissingColors K r at ha
      simp only [HierarchyStageMissingColors, hi, Fin.cases] at ha
      convert ha using 1
      apply congrArg (TreeMissingColors P.coloring)
      apply congrArg K.stage
      apply Fin.ext
      change K.dividerCount = K.dividerCount - 1 + 1
      omega
  have prefixNeTerminal (u : V) (hu : u ∈ TreeSequenceVertexSet X) :
      u ≠ T.vertex D.terminalVertexIndex := by
    obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hu
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    have hb := i.isLt
    have ht := D.terminalVertexPosition
    change i.val = D.terminalVertexIndex.val at hi
    have hb' : i.val < T.length := by simpa only [hTlen] using hb
    exact (Nat.ne_of_lt hb') (hi.trans ht)

  have prepareLater
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a b : Fin k) (hne : a ≠ b)
      (haA : a ∈ TreeMissingColors P.coloring A)
      (haStage : a ∈ HierarchyStageMissingColors P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount))
      (hbX : b ∈ TreeMissingColors P.coloring X)
      (haTail : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        P.coloring (T.edge t) ≠ some a)
      (hterminal : a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
        b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex)) :
      let mu := TwoColorComponentSwap G P.coloring a b
        (Sum.inl (T.vertex D.terminalVertexIndex))
      TwoColorPathComponent G P.coloring a b (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
        Disjoint
          (TwoColorComponent G P.coloring a b (Sum.inl (T.vertex D.terminalVertexIndex)))
          (TwoColorComponent G P.coloring a b
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T a)))) ∧
        (∀ v ∈ TreeSequenceVertexSet X,
          MissingColors G mu v = MissingColors G P.coloring v) ∧
        (∀ c ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount),
          HierarchyFirstMissingPosition mu T c =
            HierarchyFirstMissingPosition P.coloring T c) ∧
        ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet T) := by
    as_aux_lemma =>
      clear * - P a b hne haA haStage hbX haTail hterminal
        presentationGeometry firstMissing missingMono hierarchyGeometry
        commonPrefix hAT hXT hAX hXlen hBlen hPenVal hTlen hyp caseFor prefixNeTerminal
      let J := P.corresponding.replacementETT
      let C' := P.counterexample
      let col := P.coloring
      let H' := C'.hierarchy
      let q' := Fin.last H'.dividerCount
      let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
      let mu := TwoColorComponentSwap G col a b z
      have hg := presentationGeometry P
      have hstar : HierarchyStarredStage C'.hierarchy
          (Fin.last C'.hierarchy.dividerCount) = A := hg.1
      have hstar' : HierarchyStarredStage H' q' = A := hstar
      have hXeq : HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1) = X := by
        rw [hg.2.1]
        exact hg.2.2.1
      have hp : IsProperEdgeColoring G col := P.minimumContext.proper
      have hxElem : ColoredVertexSetElementary G col (TreeSequenceVertexSet X) := by
        have he : ColoredVertexSetElementary G col
            (TreeSequenceVertexSet (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1))) :=
          HierarchyCounterexamplePenultimateElementary G k e0
          P.corresponding.replacementInput T col J P.replacementBase C'
          P.minimumContext.proper P.minimumContext.oneEdgeUncolored
          P.minimumContext.lowerRung P.minimumContext.fewerDividers
          P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
        intro u hu v hv huv
        have hu' : u ∈ TreeSequenceVertexSet
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
          rw [hXeq]
          exact hu
        have hv' : v ∈ TreeSequenceVertexSet
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
          rw [hXeq]
          exact hv
        exact he hu' hv' huv
      obtain ⟨vb0, hvbX0, hb0⟩ := Finset.mem_biUnion.mp hbX
      obtain ⟨ib, _, hib⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hvbX0
      have hbi : b ∈ MissingColors G col
          (T.vertex (Fin.castLE (Nat.succ_le_succ hXT.1) ib)) := by
        rw [hXT.2.1 ib, hib]
        exact hb0
      have hbFirst := firstMissing col b _ hbi
      have hbBound : (HierarchyFirstMissingPosition col T b).val ≤ X.length :=
        hbFirst.2.trans (Nat.le_of_lt_succ ib.isLt)
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp haA
      obtain ⟨i, _, hiv⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      have hai : a ∈ MissingColors G col
          (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i)) := by
        rw [hAT.2.1 i, hiv]
        exact hav
      have haFirst := firstMissing col a _ hai
      have haBound : (HierarchyFirstMissingPosition col T a).val ≤ A.length :=
        le_trans haFirst.2 (Nat.le_of_lt_succ i.isLt)
      have haBoundX : (HierarchyFirstMissingPosition col T a).val ≤ X.length :=
        haBound.trans hAX.1
      let va := T.vertex (HierarchyFirstMissingPosition col T a)
      let vb := T.vertex (HierarchyFirstMissingPosition col T b)
      let vt := T.vertex D.terminalVertexIndex
      have hvaX : va ∈ TreeSequenceVertexSet X := by
        apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        refine ⟨⟨(HierarchyFirstMissingPosition col T a).val, by
          exact Nat.lt_succ_of_le (haBound.trans hAX.1)⟩, Finset.mem_univ _, ?_⟩
        rfl
      have hvbX : vb ∈ TreeSequenceVertexSet X := by
        apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        refine ⟨⟨(HierarchyFirstMissingPosition col T b).val, by
          exact Nat.lt_succ_of_le hbBound⟩, Finset.mem_univ _, ?_⟩
        rfl
      have horder (hbNotA : b ∉ TreeMissingColors col A) :
          (HierarchyFirstMissingPosition col T a).val <
            (HierarchyFirstMissingPosition col T b).val := by
        have hbLower : A.length < (HierarchyFirstMissingPosition col T b).val := by
          by_contra hn
          have hle : (HierarchyFirstMissingPosition col T b).val ≤ A.length := Nat.le_of_not_gt hn
          let j : Fin (A.length + 1) :=
            ⟨(HierarchyFirstMissingPosition col T b).val, Nat.lt_succ_of_le hle⟩
          apply hbNotA
          refine Finset.mem_biUnion.mpr ⟨A.vertex j,
            (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
          have hi : Fin.castLE (Nat.succ_le_succ hAT.1) j =
              HierarchyFirstMissingPosition col T b := Fin.ext rfl
          rw [← hAT.2.1 j, hi]
          exact hbFirst.1
        exact haBound.trans_lt hbLower
      have hnorm := caseFor P a haStage
      have hmissing : a ∈ TreeMissingColors col X ∧ b ∈ TreeMissingColors col X :=
        ⟨missingMono hAX col haA, hbX⟩
      have hmissingP : a ∈ TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) ∧
          b ∈ TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
        rw [hXeq]
        exact hmissing
      have helemP : ColoredVertexSetElementary G col
          (TreeSequenceVertexSet (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1))) := by
        rw [hXeq]
        exact hxElem
      have hchange := ChangeLemma G k e0 P.corresponding.replacementInput T col
        J P.replacementBase C' hp P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality
        helemP
        P.minimumContext.largeMissingSet a b hne
        hmissingP
        (by
          dsimp only
          intro hcond
          refine ⟨⟨HierarchyFirstMissingPosition col T a,
            HierarchyFirstMissingPosition col T b, rfl, rfl, ?_⟩, ?_⟩
          · apply horder
            rw [hstar] at hcond
            rcases hcond with hn | hn
            · exact (hn haA).elim
            · exact hn
          · intro hc
            obtain ⟨t, ht, hhi, hcol⟩ := (Finset.mem_filter.mp hc).2
            exact haTail t (by simpa only [hstar] using ht)
              (by clear * - hbBound hhi; omega) hcol)
      have hsame : TwoColorComponent G col a b (Sum.inl va) =
          TwoColorComponent G col a b (Sum.inl vb) := by
        rcases hnorm with ⟨hq, ha⟩ | ⟨hq, ha⟩
        · simpa [va, vb] using hchange.1 ⟨hq, Or.inl ha⟩
        · simpa [va, vb] using hchange.2.1 ⟨hq, Or.inl ha⟩
      have rootMem (w : Sum V E) : w ∈ TwoColorComponent G col a b w := by
        change (TwoColorIncidenceGraph G col a b).connectedComponentMk w = _
        rfl
      have leaf (w : V)
          (hm : a ∈ MissingColors G col w ∨ b ∈ MissingColors G col w) :
          ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)).Subsingleton := by
        have hd : @SimpleGraph.degree _ (TwoColorIncidenceGraph G col a b)
            (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
          rcases hm with hm | hm
          · exact MissingColorIncidenceEndpoint G col a b hne hp w hm
          · have hs : TwoColorIncidenceGraph G col b a =
                TwoColorIncidenceGraph G col a b := by
              ext x y
              cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
            rw [← hs]
            exact MissingColorIncidenceEndpoint G col b a hne.symm hp w hm
        letI : Fintype ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)) :=
          Fintype.ofFinite _
        have hc : Fintype.card
            ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact hd
        intro x hx y hy
        exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩)
      have hdis : Disjoint (TwoColorComponent G col a b z)
          (TwoColorComponent G col a b (Sum.inl va)) := by
        rcases TwoColorComponentsDisjoint G col a b z (Sum.inl va) with heq | hd
        · by_cases habVertex : va = vb
          · have hbAt : b ∈ MissingColors G col va := habVertex.symm ▸ hbFirst.1
            have emptyNeighbors :
                (TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl va) = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro w hw
              cases w with
              | inl w => simpa [TwoColorIncidenceGraph] using hw
              | inr e =>
                obtain ⟨hinc, hca | hcb⟩ := hw
                · have hn : a ∉ PresentColors G col va := by
                    simpa [MissingColors] using haFirst.1
                  exact hn (by simp [PresentColors]; exact ⟨e, hinc, hca⟩)
                · have hn : b ∉ PresentColors G col va := by
                    simpa [MissingColors] using hbAt
                  exact hn (by simp [PresentColors]; exact ⟨e, hinc, hcb⟩)
            have hat : (Sum.inl va : Sum V E) ≠ Sum.inl vt := by
              exact fun h => prefixNeTerminal va hvaX (Sum.inl.inj h)
            have hreach : (TwoColorIncidenceGraph G col a b).Reachable
                (Sum.inl va) (Sum.inl vt) := by
              apply SimpleGraph.ConnectedComponent.exact
              change Sum.inl va ∈ TwoColorComponent G col a b z
              rw [heq]
              exact rootMem _
            exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hat
              emptyNeighbors hreach).elim
          · obtain ⟨u, w, p, hpPath, hsupp⟩ :=
              TwoColorComponentSpanningPath G col a b hp z
            have endpoint (y : V)
                (hy : Sum.inl y ∈ TwoColorComponent G col a b z)
                (hm : a ∈ MissingColors G col y ∨ b ∈ MissingColors G col y) :
                Sum.inl y = u ∨ Sum.inl y = w := by
              have hySupp : Sum.inl y ∈ p.support := by
                change Sum.inl y ∈ {x | x ∈ p.support}
                rw [hsupp]
                exact hy
              by_contra hn
              push_neg at hn
              exact hpPath.isTrail.not_mem_support_of_subsingleton_neighborSet
                hn.1 hn.2 (leaf y hm) hySupp
            have haEnd := endpoint va (heq.symm ▸ rootMem (Sum.inl va)) (Or.inl haFirst.1)
            have hbEnd := endpoint vb
              (heq.symm ▸ hsame.symm ▸ rootMem (Sum.inl vb)) (Or.inr hbFirst.1)
            have htEnd := endpoint vt (rootMem z) hterminal
            have hab : (Sum.inl va : Sum V E) ≠ Sum.inl vb := by
              intro h
              exact habVertex (Sum.inl.inj h)
            have hat : (Sum.inl va : Sum V E) ≠ Sum.inl vt := by
              exact fun h => prefixNeTerminal va hvaX (Sum.inl.inj h)
            have hbt : (Sum.inl vb : Sum V E) ≠ Sum.inl vt := by
              exact fun h => prefixNeTerminal vb hvbX (Sum.inl.inj h)
            rcases haEnd with haEnd | haEnd <;>
              rcases hbEnd with hbEnd | hbEnd <;>
              rcases htEnd with htEnd | htEnd
            · exact (hab (haEnd.trans hbEnd.symm)).elim
            · exact (hab (haEnd.trans hbEnd.symm)).elim
            · exact (hat (haEnd.trans htEnd.symm)).elim
            · exact (hbt (hbEnd.trans htEnd.symm)).elim
            · exact (hbt (hbEnd.trans htEnd.symm)).elim
            · exact (hat (haEnd.trans htEnd.symm)).elim
            · exact (hab (haEnd.trans hbEnd.symm)).elim
            · exact (hab (haEnd.trans hbEnd.symm)).elim
        · exact hd
      have hpath : TwoColorPathComponent G col a b z :=
        ⟨hne, z, rootMem z, leaf vt hterminal⟩
      have hbehavior := TwoColorComponentSwapMissingBehavior G col a b hne hp z
      have edgeIn {u : V} {e : E}
          (hu : Sum.inl u ∈ TwoColorComponent G col a b z)
          (he : Incident G u e) (hc : col e = some a ∨ col e = some b) :
          Sum.inr e ∈ TwoColorComponent G col a b z := by
        have hadj : (TwoColorIncidenceGraph G col a b).Adj (Sum.inr e) (Sum.inl u) :=
          ⟨he, hc⟩
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hu
      have hprefix : ∀ u ∈ TreeSequenceVertexSet X,
          MissingColors G mu u = MissingColors G col u := by
        intro u hu
        by_cases huQ : Sum.inl u ∈ TwoColorComponent G col a b z
        · have haNot : a ∉ MissingColors G col u := by
            intro hau
            have huv : u = va := by
              by_contra hn
              exact Finset.disjoint_left.mp (hxElem hu hvaX hn) hau haFirst.1
            exact Set.disjoint_left.mp hdis huQ (huv.symm ▸ rootMem (Sum.inl va))
          have hbNot : b ∉ MissingColors G col u := by
            intro hbu
            have huv : u = vb := by
              by_contra hn
              exact Finset.disjoint_left.mp (hxElem hu hvbX hn) hbu hbFirst.1
            exact Set.disjoint_left.mp hdis huQ
              (huv.symm ▸ hsame.symm ▸ rootMem (Sum.inl vb))
          obtain ⟨ea, hea, hca⟩ : ∃ e, Incident G u e ∧ col e = some a := by
            simpa [MissingColors, PresentColors] using haNot
          obtain ⟨eb, heb, hcb⟩ : ∃ e, Incident G u e ∧ col e = some b := by
            simpa [MissingColors, PresentColors] using hbNot
          have hnewa : mu eb = some a := by
            simp [mu, TwoColorComponentSwap, edgeIn huQ heb (Or.inr hcb), hcb, hne.symm]
          have hnewb : mu ea = some b := by
            simp [mu, TwoColorComponentSwap, edgeIn huQ hea (Or.inl hca), hca]
          have haNewNot : a ∉ MissingColors G mu u := by
            simpa [MissingColors, PresentColors] using
              (show ∃ e, Incident G u e ∧ mu e = some a from ⟨eb, heb, hnewa⟩)
          have hbNewNot : b ∉ MissingColors G mu u := by
            simpa [MissingColors, PresentColors] using
              (show ∃ e, Incident G u e ∧ mu e = some b from ⟨ea, hea, hnewb⟩)
          apply Finset.ext
          intro c
          by_cases hca : c = a
          · simp [hca, haNot, haNewNot]
          · by_cases hcb : c = b
            · simp [hcb, hbNot, hbNewNot]
            · exact hbehavior.2.2.2 u c hca hcb
        · exact hbehavior.1 u huQ
      have hbNew : b ∈ MissingColors G mu vb := by
        rw [hprefix vb hvbX]
        exact hbFirst.1
      have hbNewFirst : HierarchyFirstMissingPosition mu T b =
          HierarchyFirstMissingPosition col T b := by
        have hm := firstMissing mu b (HierarchyFirstMissingPosition col T b) hbNew
        have hv : T.vertex (HierarchyFirstMissingPosition mu T b) ∈ TreeSequenceVertexSet X := by
          apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          refine ⟨⟨(HierarchyFirstMissingPosition mu T b).val, Nat.lt_succ_of_le (hm.2.trans hbBound)⟩, Finset.mem_univ _, ?_⟩
          rfl
        have hmOld : b ∈ MissingColors G col
            (T.vertex (HierarchyFirstMissingPosition mu T b)) := by
          rw [← hprefix _ hv]
          exact hm.1
        by_contra hn
        exact Finset.disjoint_left.mp
          (hxElem hv hvbX (fun he => hn (T.vertex_injective he))) hmOld hbFirst.1
      have hstoredFirst : ∀ c, c ∈ HierarchyStoredColorsAt H' q' →
          HierarchyFirstMissingPosition mu T c = HierarchyFirstMissingPosition col T c := by
        intro c hc
        have hca : c ≠ a := by
          intro he
          have hnot := (Finset.mem_sdiff.mp hc).2
          apply hnot
          change c ∈ TreeMissingColors col (HierarchyStarredStage H' q')
          rw [hstar', he]
          exact haA
        by_cases hcb : c = b
        · subst c
          exact hbNewFirst
        · have hcandidates :
              (Finset.univ.filter fun i : Fin (T.length + 1) =>
                c ∈ MissingColors G mu (T.vertex i)) =
              (Finset.univ.filter fun i : Fin (T.length + 1) =>
                c ∈ MissingColors G col (T.vertex i)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hbehavior.2.2.2 _ c hca hcb
          unfold HierarchyFirstMissingPosition
          simp only [hcandidates]
      have hnonElem : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet T) := by
        intro he
        have htMem : vt ∈ TreeSequenceVertexSet T :=
          (@Finset.mem_image _ _ (Classical.decEq V)).mpr
            ⟨D.terminalVertexIndex, Finset.mem_univ _, rfl⟩
        rcases hterminal with hta | htb
        · have hbTerminal : b ∈ MissingColors G mu vt := hbehavior.2.1 vt (rootMem z) hta
          have hpMem := TreeSequenceInitialSegmentVertexSetSubset hXT hvbX
          have hnept : vb ≠ vt := prefixNeTerminal vb hvbX
          exact Finset.disjoint_left.mp (he hpMem htMem hnept) hbNew hbTerminal
        · have haTerminal : a ∈ MissingColors G mu vt := hbehavior.2.2.1 vt (rootMem z) htb
          have hvaNot : Sum.inl va ∉ TwoColorComponent G col a b z := by
            intro hva
            exact Set.disjoint_left.mp hdis hva (rootMem (Sum.inl va))
          have haNew : a ∈ MissingColors G mu va := by
            rw [hbehavior.1 va hvaNot]
            exact haFirst.1
          have haMem := TreeSequenceInitialSegmentVertexSetSubset hXT hvaX
          have hneat : va ≠ vt := prefixNeTerminal va hvaX
          exact Finset.disjoint_left.mp (he haMem htMem hneat) haNew haTerminal
      exact ⟨hpath, hdis, hprefix, hstoredFirst, hnonElem⟩
  have rebuild
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (mu : PartialEdgeColoring E k)
      (hnon : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet T))
      (hsupply : ∃ corr : CorrespondingExtendedTashkinovTree
          G k e0 P.corresponding.replacementETT mu T,
        MaximumProperty corr.replacementETT ∧
          ∃ b : HierarchyBase corr.replacementETT mu,
            ∃ K : TashkinovHierarchy corr.replacementETT b,
              ∃ g : GoodHierarchy K,
                SameGoodHierarchy P.counterexample.good g) :
      ∃ P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        P'.coloring = mu := by
    obtain ⟨corr, hm, b, K, g, hg⟩ := hsupply
    let C' : HierarchyCounterexample b := {
      positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
      hierarchy := K
      good := g
      maximum := hm
      notElementary := hnon }
    exact HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
      P mu corr b C' hg
  have swapStep
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a b : Fin k) (hne : a ≠ b)
      (haA : a ∈ TreeMissingColors P.coloring A)
      (haStage : a ∈ HierarchyStageMissingColors P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount))
      (haTail : ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) ≠ some a)
      (hb : b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex))
      (hterminal : a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
        b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex))
      (lastColor : Fin k)
      (htheta : P.coloring (T.edge D.lastEdgeIndex) = some lastColor)
      (hthetaPresent : lastColor ∉ MissingColors G P.coloring
        (T.vertex D.penultimateVertexIndex)) :
      ∃ P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        P'.coloring = TwoColorComponentSwap G P.coloring a b
            (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
          (∀ v ∈ TreeSequenceVertexSet X,
            MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
          ∀ t : Fin T.length, A.length ≤ t.val →
            P'.coloring (T.edge t) = P.coloring (T.edge t) := by
    as_aux_lemma =>
      clear * - P a b hne haA haStage haTail hb hterminal lastColor htheta hthetaPresent
        prepareLater caseFor rebuild presentationGeometry firstMissing missingMono
        hAT hXT hAX hXlen hBlen hPenVal hLastVal hTlen hyp hell
        ell hEllone hElllt hXexact
      let J := P.corresponding.replacementETT
      let C' := P.counterexample
      let col := P.coloring
      let H' := C'.hierarchy
      let q' := Fin.last H'.dividerCount
      let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
      let mu := TwoColorComponentSwap G col a b z
      have hg := presentationGeometry P
      have hstar : HierarchyStarredStage C'.hierarchy
          (Fin.last C'.hierarchy.dividerCount) = A := hg.1
      have hstar' : HierarchyStarredStage H' q' = A := hstar
      have hXeq : HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1) = X := by
        rw [hg.2.1]
        exact hg.2.2.1
      have hp : IsProperEdgeColoring G col := P.minimumContext.proper
      have hbX : b ∈ TreeMissingColors col X := Finset.mem_biUnion.mpr ⟨_, hyp, hb⟩
      obtain ⟨hpath, hdis, hprefix, hstoredFirst, hnonElem⟩ :=
        prepareLater P a b hne haA haStage hbX (fun t ht _ => haTail t ht) hterminal
      have hcase := caseFor P a haStage
      have hmissingP : a ∈ TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) ∧
          b ∈ TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
        rw [hXeq]
        exact ⟨missingMono hAX col haA, hbX⟩
      have helemP : ColoredVertexSetElementary G col
          (TreeSequenceVertexSet (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1))) :=
        HierarchyCounterexamplePenultimateElementary G k e0
          P.corresponding.replacementInput T col J P.replacementBase C'
          P.minimumContext.proper P.minimumContext.oneEdgeUncolored
          P.minimumContext.lowerRung P.minimumContext.fewerDividers
          P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
      have hcase' :
          (0 < H'.dividerCount ∧
            a ∈ TreeMissingColors col (H'.stage ⟨H'.dividerCount, by omega⟩)) ∨
          (H'.dividerCount = 0 ∧
            (a ∈ TreeMissingColors col (J.series.data.tree (Fin.last J.rounds).castSucc) ∨
              (a ∈ TreeMissingColors col (HierarchyStarredStage H' q') ∧
                a ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds) ∧
                b ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds)))) := by
        rcases hcase with h | ⟨hz, hm⟩
        · exact Or.inl h
        · exact Or.inr ⟨hz, Or.inl hm⟩
      have hstable := StableChangeCasesOneTwo G k e0 P.corresponding.replacementInput
        T col J P.replacementBase C' hp P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality helemP
        P.minimumContext.largeMissingSet a b hne hmissingP
        z hpath mu rfl hcase' hdis
      let Tn := J.series.data.tree (Fin.last J.rounds).castSucc
      let Dn := TashkinovStoredColors J.series.data (Fin.last J.rounds)
      have stableTn : StableColoring Tn Dn col mu := by
        let baseStable := if J.series.data.kind (Fin.last J.rounds) =
            some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn P.replacementBase.closure Dn col mu
          else StableColoring Tn Dn col mu
        have extract : ∀ j : Fin (H'.dividerCount + 1),
            HierarchyWeaklyStable H' j mu → baseStable := by
          exact Fin.cases (motive := fun j => HierarchyWeaklyStable H' j mu → baseStable)
            (fun h => h) (fun i h => h.1)
        have hs := extract q' hstable.1
        by_cases hk : J.series.data.kind (Fin.last J.rounds) =
            some TashkinovExtensionKind.PE
        · have hs' : CombinedStableColoring Tn P.replacementBase.closure Dn col mu := by
            simpa [baseStable, hk] using hs
          exact hs'.1
        · simpa [baseStable, hk] using hs
      have lastX : X.vertex (Fin.last X.length) = T.vertex D.penultimateVertexIndex := by
        change T.vertex _ = T.vertex _
        apply congrArg T.vertex
        apply Fin.ext
        change X.length = D.penultimateVertexIndex.val
        exact hPenVal.symm
      have htailEdges : ∀ t : Fin T.length, A.length ≤ t.val →
          mu (T.edge t) = col (T.edge t) := by
        intro t ht
        have hna : col (T.edge t) ≠ some a := haTail t ht
        by_cases hcb : col (T.edge t) = some b
        · by_cases hlast : t = D.lastEdgeIndex
          · have htb : lastColor = b :=
              Option.some.inj (htheta.symm.trans (hlast ▸ hcb))
            exact (hthetaPresent (htb.symm ▸ hb)).elim
          · have htX : t.val < X.length := by
              have hle : t.val ≤ X.length := Nat.le_of_lt_succ
                (by change t.val < X.length + 1; rw [hTlen]; exact t.isLt)
              have hne : t.val ≠ X.length := by
                intro he
                exact hlast (Fin.ext (he.trans hLastVal.symm))
              exact lt_of_le_of_ne hle hne
            let r : Fin X.length := ⟨t.val, htX⟩
            have hbLast : b ∈ MissingColors G col (X.vertex (Fin.last X.length)) := by
              rw [lastX]
              exact hb
            let Y := HierarchyFullTailPrefix C' (ell - 1)
            have hYX : Y = X := hg.2.2.1
            let rY : Fin Y.length := Fin.cast (congrArg TreeSequence.length hYX.symm) r
            have hrY : rY.val = t.val := rfl
            have hedgeY : Y.edge rY = T.edge t := by
              have edgeCast (U W : TreeSequence G e0) (h : U = W)
                  (i : Fin W.length) :
                  U.edge (Fin.cast (congrArg TreeSequence.length h.symm) i) = W.edge i := by
                cases h
                rfl
              exact (edgeCast Y X hYX r).trans (hXT.2.2 r).symm
            have hbY : b ∈ MissingColors G col (Y.vertex (Fin.last Y.length)) := by
              rw [hYX]
              exact hbLast
            have hexc := HierarchyTailMissingColorExclusion G k e0
              P.corresponding.replacementInput T col J P.replacementBase H'
              helemP
              (ell - 1) hEllone
              (by
                change ell - 1 < T.length - (HierarchyStarredStage H' q').length
                rw [hstar', ← hell]
                exact hElllt)
              b hbY rY
              (by
                change (HierarchyStarredStage H' q').length ≤ rY.val
                rw [hstar', hrY]
                exact ht)
              (by
                change rY.val < (HierarchyStarredStage H' q').length + (ell - 1)
                rw [hstar', hrY]
                rw [← hXexact]
                exact htX)
              ((congrArg col hedgeY).trans hcb)
            obtain ⟨hqzero, hcore, hrpos, f, hstep, hkind, hsingleton,
              hrf, hfb, hstored⟩ := hexc
            have hAcore : A = P.replacementBase.core := by
              have hi : q' = 0 := by apply Fin.ext; simp [q', hqzero]
              have hcore' : HierarchyStarredStage H' q' = P.replacementBase.core := by
                rw [hi]
                rfl
              exact hstar'.symm.trans hcore'
            have hATn : A = Tn := hAcore.trans hcore
            have htpos : t.val = A.length := by
              change rY.val = (HierarchyStarredStage H' q').length at hrpos
              simpa only [hrY, hstar'] using hrpos
            obtain ⟨j, hj⟩ := T.attaches t
            let ia : Fin (A.length + 1) := ⟨j.val, by rw [← htpos]; exact j.isLt⟩
            have hvertex : A.vertex ia =
                T.vertex (Fin.castLT j (Nat.lt_trans j.isLt (Nat.succ_lt_succ t.isLt))) := by
              rw [← hAT.2.1 ia]
              apply congrArg T.vertex
              apply Fin.ext
              rfl
            have hincident : TreeIncidentEdge Tn (T.edge t) := by
              rw [← hATn]
              refine ⟨A.vertex ia, ?_, ?_⟩
              · exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
                  ⟨ia, Finset.mem_univ _, rfl⟩
              · rw [hvertex]
                simp [Incident, hj]
            exact stableTn.1 (T.edge t) hincident
              ⟨b, Finset.mem_union_right _ hstored, hcb⟩
        · dsimp only [mu]
          unfold TwoColorComponentSwap
          simp only [if_neg hna, if_neg hcb, ite_self]
      have hfull := StableChangeCasesOneTwoFullTail G k e0
        P.corresponding.replacementInput T col J P.replacementBase C' P.minimumContext
        a b hne hmissingP z hpath mu rfl hcase' hdis
        (by dsimp only; intro t ht
            exact htailEdges t (by simpa only [hstar] using ht))
        (by intro v hv; rw [hXeq] at hv; exact hprefix v hv) hstoredFirst
      obtain ⟨Pnew, hcolor⟩ := rebuild P mu hnonElem hfull.2.2.2.2
      refine ⟨Pnew, hcolor, ?_, ?_⟩
      · simpa [hcolor] using hprefix
      · simpa [hcolor] using htailEdges
  obtain ⟨P1, hmu1, hprefix1, hedges1⟩ := swapStep P0 gamma D.alpha hgammaAlpha
    hgammaA hgammaAvoid.1 hgammaTail D.alphaMissingPenultimate
    (Or.inr D.alphaMissingTerminal) D.theta D.thetaOnLastEdge D.thetaPresentPenultimate
  let rho := P1.coloring
  let J1 := P1.corresponding.replacementETT
  let H1 := P1.counterexample.hierarchy
  let q1 := Fin.last H1.dividerCount
  have geometry1 := presentationGeometry P1
  have elementary1 : ColoredVertexSetElementary G rho (TreeSequenceVertexSet X) := by
    intro u hu v hv hn
    rw [hprefix1 u hu, hprefix1 v hv]
    exact helem hu hv hn
  let n1 := Fin.last J1.rounds
  let Tn1 := J1.series.data.tree n1.castSucc
  let extra := (TreeSequenceVertexSet P1.replacementBase.core \
    TreeSequenceVertexSet Tn1).biUnion fun v => MissingColors G rho v
  let used := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < A.length + (ell - 2) ∧
      rho (T.edge t) = some c
  let available := (TreeMissingColors rho B \ extra) \ used
  let Gamma := (HierarchyStoredColorsAt H1 q1).biUnion (P1.counterexample.good.gamma q1)
  let beforeLast : Fin T.length := ⟨B.length, by
    rw [hBlen]
    have hp := T.positive
    clear * - hp
    omega⟩
  let finalColors := (rho (T.edge beforeLast)).toFinset ∪
    (rho (T.edge D.lastEdgeIndex)).toFinset
  have hsize : 2 * J1.rounds + 11 ≤ available.card := by
    have hn := NineN G k e0 P1.corresponding.replacementInput T rho J1
      P1.counterexample.positive P1.replacementBase H1 P1.counterexample.good
      (by
        change ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet (HierarchyFullTailPrefix P1.counterexample
            (HierarchyFullTailLength P1.counterexample - 1)))
        rw [geometry1.2.1, geometry1.2.2.1]
        exact elementary1)
      P1.minimumContext.largeMissingSet (ell - 2)
      (by change ell - 2 < T.length - (HierarchyStarredStage H1 q1).length
          rw [geometry1.1, ← hell]
          clear * - htail
          omega)
    have hs := hn.1
    change 2 * J1.rounds + 11 ≤
      (((TreeMissingColors rho
        (HierarchyFullTailPrefix P1.counterexample (ell - 2)) \ extra) \
          ((Finset.univ : Finset (Fin k)).filter fun c =>
            ∃ t : Fin T.length,
              (HierarchyStarredStage H1 q1).length ≤ t.val ∧
                t.val < (HierarchyStarredStage H1 q1).length + (ell - 2) ∧
                rho (T.edge t) = some c))).card at hs
    have star1 : HierarchyStarredStage H1 q1 = A := geometry1.1
    change HierarchyStarredStage P1.counterexample.hierarchy
      (Fin.last P1.counterexample.hierarchy.dividerCount) = A at star1
    have prefixB : HierarchyFullTailPrefix P1.counterexample (ell - 2) = B := by
      simp only [HierarchyFullTailPrefix, star1]
      rfl
    rw [prefixB, star1] at hs
    exact hs
  have hGammaSize : Gamma.card ≤ 2 * J1.rounds := by
    have hc : Gamma.card ≤
        ∑ c ∈ HierarchyStoredColorsAt H1 q1, (P1.counterexample.good.gamma q1 c).card :=
      Finset.card_biUnion_le
    have he := Finset.sum_const_nat
      (s := HierarchyStoredColorsAt H1 q1) (m := 2)
      (fun c hc => P1.counterexample.good.twoColors q1 c hc)
    have hb := HierarchyStoredColorsCardinality H1 q1
    change (HierarchyStoredColorsAt H1 q1).card ≤ J1.rounds at hb
    rw [he] at hc
    exact hc.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 hb)
  have hFinalSize : finalColors.card ≤ 2 := by
    have hc := Finset.card_union_le
      (rho (T.edge beforeLast)).toFinset (rho (T.edge D.lastEdgeIndex)).toFinset
    have ho (o : Option (Fin k)) : o.toFinset.card ≤ 1 := by
      cases o <;> simp
    have h1 := ho (rho (T.edge beforeLast))
    have h2 := ho (rho (T.edge D.lastEdgeIndex))
    change finalColors.card ≤
      (rho (T.edge beforeLast)).toFinset.card +
        (rho (T.edge D.lastEdgeIndex)).toFinset.card at hc
    clear * - hc h1 h2
    omega
  have hchoice : (available \ (Gamma ∪ finalColors)).Nonempty := by
    apply Finset.card_pos.mp
    have hremoved := Finset.card_union_le Gamma finalColors
    have hremain := Finset.card_le_card_sdiff_add_card (s := available)
      (t := Gamma ∪ finalColors)
    clear * - hsize hGammaSize hFinalSize hremoved hremain
    omega
  obtain ⟨beta, hbeta⟩ := hchoice
  have betaParts : ((beta ∈ TreeMissingColors rho B ∧ beta ∉ extra) ∧ beta ∉ used) ∧
      (beta ∉ Gamma ∧ beta ∉ finalColors) := by
    simpa only [available, Finset.mem_sdiff, Finset.mem_union, not_or] using hbeta
  have betaB : beta ∈ TreeMissingColors rho B := betaParts.1.1.1
  have betaOutside : beta ∉ Gamma := betaParts.2.1
  obtain ⟨betaVertex, betaVertexB, betaAtVertex1⟩ :=
    (Finset.mem_biUnion (s := TreeSequenceVertexSet B)
      (t := fun v => MissingColors G rho v)).mp betaB
  have betaTail : ∀ t : Fin T.length, A.length ≤ t.val →
      rho (T.edge t) ≠ some beta := by
    intro t ht hc
    by_cases hb : t.val < B.length
    · apply betaParts.1.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, t, ht, ?_, hc⟩
      have hBexact : B.length = A.length + (ell - 2) := by
        rw [hBlen]
        clear * - hell htail
        omega
      simpa only [hBexact] using hb
    · apply betaParts.2.2
      by_cases hp : t = beforeLast
      · exact Finset.mem_union_left _
          (by simp only [← hp, Option.mem_toFinset]; rw [hc]; exact Option.mem_some_self beta)
      · have hl : t = D.lastEdgeIndex := by
          apply Fin.ext
          have htlt := t.isLt
          have hnp : t.val ≠ beforeLast.val := fun h => hp (Fin.ext h)
          have hpos := D.lastEdgePosition
          change t.val ≠ B.length at hnp
          rw [hBlen] at hb hnp
          clear * - htlt hnp hb hpos
          omega
        exact Finset.mem_union_right _
          (by simp only [← hl, Option.mem_toFinset]; rw [hc]; exact Option.mem_some_self beta)
  have gammaA1 : gamma ∈ TreeMissingColors rho A := by
    refine (Finset.mem_biUnion (s := TreeSequenceVertexSet A)
      (t := fun v => MissingColors G rho v)).mpr ⟨gammaVertex, gammaVertexA, ?_⟩
    rw [hprefix1 gammaVertex (TreeSequenceInitialSegmentVertexSetSubset hAX gammaVertexA)]
    exact gammaAtVertex
  have gammaTerminal1 : gamma ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
    rw [show rho = P1.coloring from rfl, hmu1]
    apply (TwoColorComponentSwapMissingBehavior G phi gamma D.alpha hgammaAlpha
      ctx.proper (Sum.inl (T.vertex D.terminalVertexIndex))).2.2.1
    · change (TwoColorIncidenceGraph G phi gamma D.alpha).connectedComponentMk _ = _
      rfl
    · exact D.alphaMissingTerminal
  have slotData (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      ∀ c, c ∈ HierarchyStoredColorsAt H q →
        c ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) c =
            C.good.gamma q c := by
    intro c hc
    obtain ⟨hn, hs⟩ := P.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hn) q =
        Fin.last P.counterexample.hierarchy.dividerCount := by
      apply Fin.ext
      exact hn
    have hh := hs q
    rw [hi] at hh
    exact ⟨hh.1 ▸ hc, (hh.2 c hc).symm⟩
  have reservedEq
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      (HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
            (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)) =
        (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
    obtain ⟨hn, hs⟩ := P.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hn) q =
        Fin.last P.counterexample.hierarchy.dividerCount := by
      apply Fin.ext
      exact hn
    have hh := hs q
    rw [hi] at hh
    ext c
    constructor
    · intro hc
      obtain ⟨d, hd, hc⟩ := Finset.mem_biUnion.mp hc
      have hd' : d ∈ HierarchyStoredColorsAt H q := hh.1.symm ▸ hd
      exact Finset.mem_biUnion.mpr ⟨d, hd', by rw [hh.2 d hd']; exact hc⟩
    · intro hc
      obtain ⟨d, hd, hc⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨d, hh.1 ▸ hd, by rw [← hh.2 d hd]; exact hc⟩
  have gammaStage1 : gamma ∈ HierarchyStageMissingColors H1 q1 := by
    have hd := slotData P1 D.alpha D.alphaStored
    have hm : gamma ∈ P1.counterexample.good.gamma q1 D.alpha := by rw [hd.2]; exact hgamma
    exact (Finset.mem_sdiff.mp (P1.counterexample.good.avoidance q1 D.alpha hd.1 hm)).1
  have gammaOriginal : Gamma =
      (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := reservedEq P1
  have gammaBeta : gamma ≠ beta := by
    intro he
    apply betaOutside
    exact Finset.mem_biUnion.mpr ⟨D.alpha, (slotData P1 D.alpha D.alphaStored).1,
      by rw [(slotData P1 D.alpha D.alphaStored).2, ← he]; exact hgamma⟩
  have gammaTail1 : ∀ t : Fin T.length, A.length ≤ t.val →
      rho (T.edge t) ≠ some gamma := by
    intro t ht
    change P1.coloring (T.edge t) ≠ some gamma
    rw [hedges1 t ht]
    exact hgammaTail t ht
  let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
  let mu2 := TwoColorComponentSwap G rho gamma beta z
  have hBX : TreeSequenceInitialSegment B X :=
    commonPrefix ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
      hXT (by rw [hBlen, hXlen]; clear * - T; omega)
  have betaX1 : beta ∈ TreeMissingColors rho X :=
    (Finset.mem_biUnion (s := TreeSequenceVertexSet X)
      (t := fun v => MissingColors G rho v)).mpr
        ⟨betaVertex, TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB, betaAtVertex1⟩
  obtain ⟨path2, dis2, prefix2, stored2, non2⟩ :=
    prepareLater P1 gamma beta gammaBeta gammaA1 gammaStage1 betaX1
      (fun t ht _ => gammaTail1 t ht) (Or.inl gammaTerminal1)
  have pairMissing2 : gamma ∈ TreeMissingColors rho X ∧ beta ∈ TreeMissingColors rho X := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨⟨gammaVertex, TreeSequenceInitialSegmentVertexSetSubset hAX gammaVertexA, ?_⟩,
      betaVertex, TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB, betaAtVertex1⟩
    rw [hprefix1 _ (TreeSequenceInitialSegmentVertexSetSubset hAX gammaVertexA)]
    exact gammaAtVertex
  have case2 := caseFor P1 gamma gammaStage1
  have fixed2 : ∀ t : Fin T.length, A.length ≤ t.val →
      mu2 (T.edge t) = rho (T.edge t) := by
    intro t ht
    dsimp only [mu2]
    unfold TwoColorComponentSwap
    simp only [if_neg (gammaTail1 t ht), if_neg (betaTail t ht), ite_self]
  obtain ⟨P2, color2⟩ := rebuild P1 mu2 non2
    (StableChangeCasesOneTwoFullTail G k e0 P1.corresponding.replacementInput T rho
      J1 P1.replacementBase P1.counterexample P1.minimumContext gamma beta gammaBeta
      (by rw [geometry1.2.1, geometry1.2.2.1]; exact pairMissing2)
      z path2 mu2 rfl
      (by dsimp only; rcases case2 with h | ⟨hz, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨hz, Or.inl hm⟩)
      dis2
      (by dsimp only; intro t ht; rw [geometry1.1] at ht; exact fixed2 t ht)
      (by intro v hv; rw [geometry1.2.1, geometry1.2.2.1] at hv; exact prefix2 v hv)
      stored2).2.2.2.2
  let tau := P2.coloring
  let J2 := P2.corresponding.replacementETT
  let H2 := P2.counterexample.hierarchy
  let q2 := Fin.last H2.dividerCount
  have geometry2 := presentationGeometry P2
  have prefix2' : ∀ v ∈ TreeSequenceVertexSet X,
      MissingColors G tau v = MissingColors G phi v := by
    intro v hv
    rw [show tau = P2.coloring from rfl, color2]
    exact (prefix2 v hv).trans (hprefix1 v hv)
  have edges2 : ∀ t : Fin T.length, A.length ≤ t.val →
      tau (T.edge t) = phi (T.edge t) := by
    intro t ht
    rw [show tau = P2.coloring from rfl, color2]
    exact (fixed2 t ht).trans (hedges1 t ht)
  have betaB2 : beta ∈ TreeMissingColors tau B := by
    refine (Finset.mem_biUnion (s := TreeSequenceVertexSet B)
      (t := fun v => MissingColors G tau v)).mpr ⟨betaVertex, betaVertexB, ?_⟩
    rw [show tau = P2.coloring from rfl, color2,
      prefix2 betaVertex (TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB)]
    exact betaAtVertex1
  have betaTerminal2 : beta ∈ MissingColors G tau (T.vertex D.terminalVertexIndex) := by
    rw [show tau = P2.coloring from rfl, color2]
    apply (TwoColorComponentSwapMissingBehavior G rho gamma beta gammaBeta
      P1.minimumContext.proper z).2.1
    · change (TwoColorIncidenceGraph G rho gamma beta).connectedComponentMk _ = _
      rfl
    · exact gammaTerminal1
  have betaTail2 : ∀ t : Fin T.length, A.length ≤ t.val →
      tau (T.edge t) ≠ some beta := by
    intro t ht
    rw [show tau = P2.coloring from rfl, color2, fixed2 t ht]
    exact betaTail t ht
  have thetaA2 : D.theta ∈ TreeMissingColors tau A := by
    have hm := (GoodHierarchyReservedDisjoint C.good q).1 eta hetaStored hthetaPair
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hm
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [prefix2' v (TreeSequenceInitialSegmentVertexSetSubset hAX hv)]
    exact hc
  have thetaStage2 : D.theta ∈ HierarchyStageMissingColors H2 q2 := by
    have hd := slotData P2 eta hetaStored
    have hm : D.theta ∈ P2.counterexample.good.gamma q2 eta := by
      rw [hd.2]
      exact hthetaPair
    exact (Finset.mem_sdiff.mp (P2.counterexample.good.avoidance q2 eta hd.1 hm)).1
  have thetaBeta : D.theta ≠ beta := by
    intro he
    apply betaOutside
    rw [gammaOriginal]
    exact Finset.mem_biUnion.mpr ⟨eta, hetaStored, he ▸ hthetaPair⟩
  have thetaTail2 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      tau (T.edge t) ≠ some D.theta := by
    intro t ht htx hc
    have hd := slotData P2 eta hetaStored
    have hm : D.theta ∈ P2.counterexample.good.gamma q2 eta := by rw [hd.2]; exact hthetaPair
    have hav := (Finset.mem_sdiff.mp
      (P2.counterexample.good.avoidance q2 eta hd.1 hm)).2
    have heta : eta ∈ MissingColors G tau (T.vertex D.penultimateVertexIndex) := by
      rw [prefix2' _ hyp]
      exact hetaMissing
    have hetaFirst2 : HierarchyFirstMissingPosition tau T eta = D.penultimateVertexIndex := by
      have he2 : ColoredVertexSetElementary G tau (TreeSequenceVertexSet X) := by
        intro u hu v hv hn
        rw [prefix2' u hu, prefix2' v hv]
        exact helem hu hv hn
      have hf := firstMissing tau eta D.penultimateVertexIndex heta
      have hv : T.vertex (HierarchyFirstMissingPosition tau T eta) ∈ TreeSequenceVertexSet X := by
        apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        refine ⟨⟨(HierarchyFirstMissingPosition tau T eta).val,
          Nat.lt_succ_of_le (hf.2.trans (le_of_eq hPenVal))⟩, Finset.mem_univ _, ?_⟩
        rfl
      by_contra hn
      exact Finset.disjoint_left.mp (he2 hv hyp (fun he => hn (T.vertex_injective he))) hf.1 heta
    apply hav
    unfold HierarchySegmentColors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hend : H2.stage q2.succ = T := H2.terminalStage
    let r : Fin (H2.stage q2.succ).length :=
      Fin.cast (congrArg TreeSequence.length hend.symm) t
    refine ⟨r, by rw [geometry2.1]; exact ht, ?_, ?_⟩
    · rw [hetaFirst2]
      dsimp [r]
      rw [hend]
      simpa only [hPenVal, Nat.min_eq_left hXT.1] using htx
    · have edgeCast (U W : TreeSequence G e0) (h : U = W)
          (i : Fin W.length) :
          U.edge (Fin.cast (congrArg TreeSequence.length h.symm) i) = W.edge i := by
        cases h
        rfl
      change tau ((H2.stage q2.succ).edge r) = some D.theta
      rw [edgeCast _ _ hend t]
      exact hc
  have edgeCast (X Y : TreeSequence G e0) (h : X = Y) (i : Fin X.length) :
      X.edge i = Y.edge (Fin.cast (congrArg TreeSequence.length h) i) := by
    cases h
    rfl
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hST : TreeSequenceInitialSegment (HierarchyStarredStage K (Fin.last K.dividerCount)) T)
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (hp : IsProperEdgeColoring G old) (ho : IsOneEdgeUncolored old e0)
      (hnp : IsProperEdgeColoring G new) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin T.length, t.val < (HierarchyStarredStage K (Fin.last K.dividerCount)).length →
        new (T.edge t) = old (T.edge t) := by
    as_aux_lemma =>
      clear * - G T e0 old new ett' base' K hST hw hp ho hnp hno edgeCast
      let S := HierarchyStarredStage K (Fin.last K.dividerCount)
      intro t ht
      let tS : Fin S.length := ⟨t.val, ht⟩
      have hcast : Fin.castLE hST.1 tS = t := Fin.ext rfl
      rw [← hcast, hST.2.2 tS]
      by_cases hzero : K.dividerCount = 0
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := by
          apply Fin.ext
          simp [hzero]
        have hS : S = base'.core := by change HierarchyStarredStage K _ = _; rw [hi]; rfl
        rw [hi] at hw
        change (if ett'.series.data.kind (Fin.last ett'.rounds) =
          some TashkinovExtensionKind.PE then _ else _) at hw
        by_cases hpe : ett'.series.data.kind (Fin.last ett'.rounds) = some TashkinovExtensionKind.PE
        · rw [if_pos hpe] at hw
          have hc := CombinedStableClosurePreserved G k e0 input' T old old new ett'
            (by have h := ett'.roundsPositive; omega) base' ett'.generatingColoring hpe hp ho hnp hno hw
          obtain ⟨_, _, ⟨hunion⟩⟩ := base'.parallel hpe
          let tc : Fin base'.core.length := Fin.cast (congrArg TreeSequence.length hS) tS
          have he : S.edge tS = base'.core.edge tc := edgeCast S base'.core hS tS
          rw [he]
          by_cases hbelow : tc.val < (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length
          · let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length := ⟨tc.val, hbelow⟩
            have heq : Fin.castLE hunion.leftSegment.1 tn = tc := Fin.ext rfl
            rw [← heq, hunion.leftSegment.2.2 tn]
            exact hc.1 tn
          · obtain ⟨j, heq, _⟩ := hunion.newEntryFromRight tc (by omega)
            rw [heq]
            exact hc.2.1 j
        · rw [if_neg hpe] at hw
          have hcore := base'.nonparallel hpe
          have hS' := hS.trans hcore
          let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length :=
            Fin.cast (congrArg TreeSequence.length hS') tS
          have he : S.edge tS = (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).edge tn := by
            exact edgeCast S _ hS' tS
          rw [he]
          let r : Fin ett'.rounds := ⟨ett'.rounds - 1, by have h := ett'.roundsPositive; omega⟩
          have hr : r.succ = Fin.last ett'.rounds := by
            have hn := ett'.roundsPositive
            apply Fin.ext
            simp [r]
            omega
          have hfix := (HkuTreeColorsControlled G k ett'.rounds e0 input' ett'.series r).2.2 new
            hnp hno (by rw [hr, ← ett'.generatingColoring]; exact hw)
          rw [hr, ← ett'.generatingColoring] at hfix
          exact hfix tn
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
            (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ := by
          apply Fin.ext
          simp
          omega
        have hS : S = K.stage (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ.castSucc := by
          change HierarchyStarredStage K _ = _
          rw [hi]
          simp [HierarchyStarredStage]
        rw [hi] at hw
        simp [HierarchyWeaklyStable] at hw
        have hinv : TreeColoringInvariant S old new := hS.symm ▸ hw.2
        by_cases hpos : 1 ≤ tS.val
        · exact hinv.1 tS hpos
        · have hi : tS = ⟨0, S.positive⟩ := by
            apply Fin.ext
            change tS.val = 0
            omega
          rw [hi, S.first_edge, hno.1, ho.1]
  let mu3 := TwoColorComponentSwap G tau D.theta beta z
  have betaX2 : beta ∈ TreeMissingColors tau X :=
    (Finset.mem_biUnion (s := TreeSequenceVertexSet X)
      (t := fun v => MissingColors G tau v)).mpr
        ⟨betaVertex, TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB, by
          rw [show tau = P2.coloring from rfl, color2,
            prefix2 betaVertex (TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB)]
          exact betaAtVertex1⟩
  obtain ⟨path3, dis3, prefix3, stored3, non3⟩ :=
    prepareLater P2 D.theta beta thetaBeta thetaA2 thetaStage2 betaX2
      thetaTail2 (Or.inr betaTerminal2)
  have pairMissing3 : D.theta ∈ TreeMissingColors tau X ∧ beta ∈ TreeMissingColors tau X := by
    obtain ⟨v, hv, hc⟩ := (Finset.mem_biUnion (s := TreeSequenceVertexSet A)
      (t := fun v => MissingColors G tau v)).mp thetaA2
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨⟨v, TreeSequenceInitialSegmentVertexSetSubset hAX hv, hc⟩,
      betaVertex, TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB, ?_⟩
    rw [show tau = P2.coloring from rfl, color2,
      prefix2 betaVertex (TreeSequenceInitialSegmentVertexSetSubset hBX betaVertexB)]
    exact betaAtVertex1
  have case3 := caseFor P2 D.theta thetaStage2
  have elementary2 : ColoredVertexSetElementary G tau (TreeSequenceVertexSet X) := by
    intro u hu v hv hn
    rw [prefix2' u hu, prefix2' v hv]
    exact helem hu hv hn
  have stable3 := StableChangeCasesOneTwo G k e0 P2.corresponding.replacementInput
    T tau J2 P2.replacementBase P2.counterexample P2.minimumContext.proper
    P2.minimumContext.oneEdgeUncolored P2.minimumContext.lowerRung
    P2.minimumContext.fewerDividers P2.minimumContext.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G tau (TreeSequenceVertexSet
        (HierarchyFullTailPrefix P2.counterexample (HierarchyFullTailLength P2.counterexample - 1)))
      rw [geometry2.2.1, geometry2.2.2.1]
      exact elementary2)
    P2.minimumContext.largeMissingSet D.theta beta thetaBeta
    (by
      change D.theta ∈ TreeMissingColors tau (HierarchyFullTailPrefix P2.counterexample
        (HierarchyFullTailLength P2.counterexample - 1)) ∧
        beta ∈ TreeMissingColors tau (HierarchyFullTailPrefix P2.counterexample
          (HierarchyFullTailLength P2.counterexample - 1))
      rw [geometry2.2.1, geometry2.2.2.1]
      exact pairMissing3)
    z path3 mu3 rfl
    (by dsimp only; rcases case3 with h | ⟨hz, hm⟩
        · exact Or.inl h
        · exact Or.inr ⟨hz, Or.inl hm⟩)
    dis3
  have fixedTail3 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      mu3 (T.edge t) = tau (T.edge t) := by
    intro t ht hx
    dsimp only [mu3]
    unfold TwoColorComponentSwap
    simp only [if_neg (thetaTail2 t ht hx), if_neg (betaTail2 t ht), ite_self]
  have fixedCore3 : ∀ t : Fin T.length, t.val < A.length →
      mu3 (T.edge t) = tau (T.edge t) := by
    have hh := weakEdges tau mu3 J2 P2.replacementBase H2
      (by rw [geometry2.1]; exact hAT) stable3.1
      P2.minimumContext.proper P2.minimumContext.oneEdgeUncolored
      stable3.2.1.1 stable3.2.1.2.1
    rw [geometry2.1] at hh
    exact hh
  have fixedPrefix3 : ∀ t : Fin T.length, t.val < X.length →
      mu3 (T.edge t) = tau (T.edge t) := by
    intro t ht
    by_cases ha : t.val < A.length
    · exact fixedCore3 t ha
    · exact fixedTail3 t (Nat.le_of_not_gt ha) ht
  have transportRoute (S : TreeSequence G e0)
      (hs : TashkinovAugmentationSequence tau S X) :
      TashkinovAugmentationSequence mu3 S X := by
    apply TashkinovAugmentationSequenceColoringTransport tau mu3 S B X hs hBX
      (by rw [hXlen, hBlen]; clear * - hell htail; omega)
    · intro t _
      have hh := fixedPrefix3 (Fin.castLE hXT.1 t) (by exact t.isLt)
      rw [hXT.2.2 t] at hh
      exact hh
    · intro v hv
      exact prefix3 v (TreeSequenceInitialSegmentVertexSetSubset hBX hv)
  have route3 :
      (J2.series.data.kind (Fin.last J2.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence mu3
          (J2.series.data.tree (Fin.last J2.rounds).castSucc) X) ∨
      ((J2.series.data.kind (Fin.last J2.rounds) = some TashkinovExtensionKind.SE ∨
          J2.series.data.kind (Fin.last J2.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, J2.series.data.connectingEdges (Fin.last J2.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (J2.series.data.tree (Fin.last J2.rounds).castSucc) f seed ∧
          TashkinovAugmentationSequence mu3 seed X) := by
    clear * - J2 H2 tau mu3 X A hXT hAX hXlen hell htail
      transportRoute segmentTrans hierarchyGeometry geometry2 commonPrefix
    let n := Fin.last J2.rounds
    let Tn := J2.series.data.tree n.castSucc
    let F := J2.series.data.tree (Fin.last (J2.rounds + 1))
    have hXF : TreeSequenceInitialSegment X F := segmentTrans hXT J2.belowFinal
    have hn : n.succ = Fin.last (J2.rounds + 1) := Fin.ext rfl
    have hTnA : TreeSequenceInitialSegment Tn A := by
      have hh := (hierarchyGeometry H2).2
      rw [geometry2.1] at hh
      exact hh
    have hTnX : TreeSequenceInitialSegment Tn X := segmentTrans hTnA hAX
    have nonparallel
        (hkind : J2.series.data.kind n = some TashkinovExtensionKind.SE ∨
          J2.series.data.kind n = some TashkinovExtensionKind.RE)
        (f : E) (seed : TreeSequence G e0)
        (hedges : J2.series.data.connectingEdges n = {f})
        (hadjoin : TreeSequenceAdjoinEdge Tn f seed)
        (hclosure : TashkinovClosure tau seed F) :
        ∃ f seed, J2.series.data.connectingEdges (Fin.last J2.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (J2.series.data.tree (Fin.last J2.rounds).castSucc) f seed ∧
          TashkinovAugmentationSequence mu3 seed X := by
      have hseedF := TashkinovAugmentationSequenceInitialSegment tau seed F hclosure.1
      have hsBound : seed.length ≤ X.length := by
        have hlen := hTnA.1
        have hseed := hadjoin.1
        rw [hXlen]
        clear * - hlen hseed hell htail
        omega
      have hseedX := commonPrefix hseedF hXF hsBound
      exact ⟨f, seed, hedges, hadjoin, transportRoute seed
        (TashkinovAugmentationSequenceRestrict tau seed X F hclosure.1 hseedX hXF)⟩
    have cert := J2.series.certified n
    generalize hindex : n = j at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        have hnzero : n = 0 := by simpa using hindex
        have hv := congrArg Fin.val hnzero
        have hp := J2.roundsPositive
        simp [n] at hv
        clear * - hv hp
        omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hk : J2.series.data.kind n = some TashkinovExtensionKind.SE := by rw [hindex]; exact currentKind
        refine Or.inr ⟨Or.inl hk, ?_⟩
        apply nonparallel (Or.inl hk) choice.edge adjoined
        · rw [hindex]; exact currentEdges
        · simpa [Tn, hindex] using adjoinedExactly
        · rw [← hindex, hn, ← J2.generatingColoring] at closedExtension
          exact closedExtension
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        have hk : J2.series.data.kind n = some TashkinovExtensionKind.PE := by rw [hindex]; exact currentKind
        refine Or.inl ⟨hk, transportRoute Tn ?_⟩
        rw [← hindex, hn, ← J2.generatingColoring] at closedExtension
        exact TashkinovAugmentationSequenceRestrict tau Tn X F closedExtension.1 hTnX hXF
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        have hk : J2.series.data.kind n = some TashkinovExtensionKind.RE := by rw [hindex]; exact currentKind
        refine Or.inr ⟨Or.inr hk, ?_⟩
        apply nonparallel (Or.inr hk) available.edge adjoined
        · rw [hindex]; exact currentEdges
        · simpa [Tn, hindex] using adjoinedExactly
        · rw [← hindex, hn, ← J2.generatingColoring] at closedExtension
          exact closedExtension
  have lastTheta2 : tau (T.edge D.lastEdgeIndex) = some D.theta := by
    rw [edges2 _ (by
      have hp := D.lastEdgePosition
      clear * - hp hell htail
      omega)]
    exact D.thetaOnLastEdge
  have suffix3 : TashkinovAugmentationSequence tau X T := by
    apply Relation.ReflTransGen.single
    refine ⟨hTlen.symm, hXT, D.theta, ?_, pairMissing3.1⟩
    have hi : Fin.cast hTlen (Fin.last X.length) = D.lastEdgeIndex := by
      apply Fin.ext
      exact hLastVal.symm
    rw [hi]
    exact lastTheta2
  have cutoff3 : ∀ c ∈ HierarchyStoredColorsAt H2 q2,
      (D.theta ∈ P2.counterexample.good.gamma q2 c ∨
        beta ∈ P2.counterexample.good.gamma q2 c) →
      (HierarchyFirstMissingPosition tau T c).val ≤ X.length := by
    intro c hc hp
    rcases hp with ht | hb
    · have he : c = eta := by
        by_contra hn
        have hs := slotData P2 eta hetaStored
        have hm : D.theta ∈ P2.counterexample.good.gamma q2 eta := by rw [hs.2]; exact hthetaPair
        exact Finset.disjoint_left.mp
          (P2.counterexample.good.disjointPairs q2 c eta hc hs.1 hn) ht hm
      subst c
      have hm : eta ∈ MissingColors G tau (T.vertex D.penultimateVertexIndex) := by
        rw [prefix2' _ hyp]
        exact hetaMissing
      exact (firstMissing tau eta D.penultimateVertexIndex hm).2.trans (le_of_eq hPenVal)
    · apply (betaOutside ?_).elim
      rw [gammaOriginal, ← reservedEq P2]
      exact (Finset.mem_biUnion (s := HierarchyStoredColorsAt H2 q2)
        (t := P2.counterexample.good.gamma q2)).mpr ⟨c, hc, hb⟩
  obtain ⟨P3, color3⟩ := rebuild P2 mu3 non3
    (StableChangeCasesOneTwoSplitTail G k e0 P2.corresponding.replacementInput T tau J2
      P2.replacementBase P2.counterexample P2.minimumContext D.theta beta thetaBeta
      (by rw [geometry2.2.1, geometry2.2.2.1]; exact pairMissing3)
      z path3 mu3 rfl
      (by dsimp only; rcases case3 with h | ⟨hz, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨hz, Or.inl hm⟩)
      dis3 X
      (by dsimp only; rw [geometry2.1]; exact hAX)
      (by dsimp only; rw [geometry2.1]; rw [hXlen]
          clear * - hell htail; omega)
      (by rw [geometry2.2.1, geometry2.2.2.1]; exact
        ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩)
      (by dsimp only; intro t ht hx; rw [geometry2.1] at ht; exact fixedTail3 t ht hx)
      route3 suffix3
      (by
        constructor
        · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp pairMissing3.1
          exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [prefix3 v hv]; exact hc⟩
        · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp pairMissing3.2
          exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [prefix3 v hv]; exact hc⟩)
      (by intro v hv; rw [geometry2.2.1, geometry2.2.2.1] at hv; exact prefix3 v hv)
      stored3 cutoff3).2.2
  have terminalIncident : Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
    obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
    have hind : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
      apply Fin.ext
      have he := D.lastEdgePosition
      have hv := D.terminalVertexPosition
      simp only [Fin.val_succ]
      clear * - he hv
      omega
    rw [← hind]
    simp [Incident, hi]
  have lastComponent3 : Sum.inr (T.edge D.lastEdgeIndex) ∈
      TwoColorComponent G tau D.theta beta z := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (TwoColorIncidenceGraph G tau D.theta beta).Adj
        (Sum.inr (T.edge D.lastEdgeIndex)) z from ⟨terminalIncident, Or.inl lastTheta2⟩)
  have lastBeta3 : P3.coloring (T.edge D.lastEdgeIndex) = some beta := by
    rw [color3]
    simp [mu3, TwoColorComponentSwap, lastComponent3, lastTheta2]
  have thetaTerminal3 : D.theta ∈ MissingColors G P3.coloring (T.vertex D.terminalVertexIndex) := by
    rw [color3]
    apply (TwoColorComponentSwapMissingBehavior G tau D.theta beta thetaBeta
      P2.minimumContext.proper z).2.2.1
    · change (TwoColorIncidenceGraph G tau D.theta beta).connectedComponentMk _ = _
      rfl
    · exact betaTerminal2
  have prefix3' : ∀ v ∈ TreeSequenceVertexSet X,
      MissingColors G P3.coloring v = MissingColors G phi v := by
    intro v hv
    rw [color3]
    exact (prefix3 v hv).trans (prefix2' v hv)
  have thetaA3 : D.theta ∈ TreeMissingColors P3.coloring A := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp thetaA2
    exact Finset.mem_biUnion.mpr ⟨v, hv, by
      rw [color3, prefix3 v (TreeSequenceInitialSegmentVertexSetSubset hAX hv)]
      exact hc⟩
  have thetaStage3 : D.theta ∈ HierarchyStageMissingColors P3.counterexample.hierarchy
      (Fin.last P3.counterexample.hierarchy.dividerCount) := by
    have hs := slotData P3 eta hetaStored
    have hm : D.theta ∈ P3.counterexample.good.gamma
        (Fin.last P3.counterexample.hierarchy.dividerCount) eta := by rw [hs.2]; exact hthetaPair
    exact (Finset.mem_sdiff.mp (P3.counterexample.good.avoidance _ eta hs.1 hm)).1
  have thetaTail3 : ∀ t : Fin T.length, A.length ≤ t.val →
      P3.coloring (T.edge t) ≠ some D.theta := by
    intro t ht hc
    by_cases hx : t.val < X.length
    · rw [color3, fixedTail3 t ht hx] at hc
      exact thetaTail2 t ht hx hc
    · have hi : t = D.lastEdgeIndex := by
        apply Fin.ext
        have htlt := t.isLt
        clear * - htlt hx hLastVal hXlen
        omega
      rw [hi, lastBeta3] at hc
      exact thetaBeta (Option.some.inj hc).symm
  have betaPresent3 : beta ∉ MissingColors G P3.coloring (T.vertex D.penultimateVertexIndex) := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp betaB2
    have hvX := TreeSequenceInitialSegmentVertexSetSubset hBX hv
    have hcv : beta ∈ MissingColors G P3.coloring v := by rw [color3, prefix3 v hvX]; exact hc
    have hn : v ≠ T.vertex D.penultimateVertexIndex := by
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      intro he
      have hi := congrArg Fin.val (T.vertex_injective he)
      change i.val = D.penultimateVertexIndex.val at hi
      have hb : B.length + 1 ≤ D.penultimateVertexIndex.val := by
        rw [hPenVal, hXlen, hBlen]
        clear * - hell htail
        omega
      exact (Nat.ne_of_lt (i.isLt.trans_le hb)) hi
    intro hp
    have he3 : ColoredVertexSetElementary G P3.coloring (TreeSequenceVertexSet X) := by
      intro u hu w hw hn
      rw [prefix3' u hu, prefix3' w hw]
      exact helem hu hw hn
    exact Finset.disjoint_left.mp (he3 hvX hyp hn) hcv hp
  -- Restore the stored Case 1 witness after making the last edge nonreserved.
  have thetaAlpha : D.theta ≠ D.alpha := by
    intro he
    exact D.thetaPresentPenultimate (he.symm ▸ D.alphaMissingPenultimate)
  obtain ⟨P4, color4, prefix4, edges4⟩ := swapStep P3 D.theta D.alpha thetaAlpha
    thetaA3 thetaStage3 thetaTail3
    (by rw [prefix3' _ hyp]; exact D.alphaMissingPenultimate)
    (Or.inl thetaTerminal3) beta lastBeta3 betaPresent3
  have geometry4 := presentationGeometry P4
  have alphaTerminal4 : D.alpha ∈ MissingColors G P4.coloring (T.vertex D.terminalVertexIndex) := by
    rw [color4]
    apply (TwoColorComponentSwapMissingBehavior G P3.coloring D.theta D.alpha thetaAlpha
      P3.minimumContext.proper z).2.1
    · change (TwoColorIncidenceGraph G P3.coloring D.theta D.alpha).connectedComponentMk _ = _
      rfl
    · exact thetaTerminal3
  have hlastTail : A.length ≤ D.lastEdgeIndex.val := by
    have hp := D.lastEdgePosition
    clear * - hp hell htail
    omega
  have hd4 := slotData P4 D.alpha D.alphaStored
  let D4 : HierarchySituationTwoCaseOneData G k e0 P4.corresponding.replacementInput
      T P4.coloring P4.corresponding.replacementETT P4.replacementBase P4.counterexample
      P4.minimumContext := {
    tailAtLeastTwo := by rw [geometry4.2.1]; exact htail
    pathNumberFull := geometry4.2.2.2.trans (D.pathNumberFull.trans geometry4.2.1.symm)
    lastEdgeIndex := D.lastEdgeIndex
    penultimateVertexIndex := D.penultimateVertexIndex
    terminalVertexIndex := D.terminalVertexIndex
    lastEdgePosition := D.lastEdgePosition
    penultimateVertexPosition := D.penultimateVertexPosition
    terminalVertexPosition := D.terminalVertexPosition
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
    theta := beta
    thetaOnLastEdge := (edges4 _ hlastTail).trans lastBeta3
    thetaPresentPenultimate := by rw [prefix4 _ hyp]; exact betaPresent3
    alpha := D.alpha
    gammaOne := D.gammaOne
    gammaTwo := D.gammaTwo
    alphaMissingPenultimate := by rw [prefix4 _ hyp, prefix3' _ hyp]; exact D.alphaMissingPenultimate
    alphaMissingTerminal := alphaTerminal4
    alphaStored := hd4.1
    gammaPair := hd4.2.trans D.gammaPair
    gammaDistinct := D.gammaDistinct }
  apply HierarchySituationTwoSubcaseOneOneNonexceptional G k e0 P4.corresponding.replacementInput
    T P4.coloring P4.corresponding.replacementETT P4.replacementBase P4.counterexample
    P4.minimumContext D4
  left
  intro hm
  apply betaOutside
  rw [reservedEq P4] at hm
  change beta ∈ Gamma
  rw [gammaOriginal]
  exact hm
