import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoCaseTwoExclusions
import Tablet.HierarchySituationTwoSubcaseOneOne
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.MissingColors
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TashkinovHierarchy
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.sc2
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: HierarchySituationTwoSubcaseTwoOneStoredException]
theorem HierarchySituationTwoSubcaseTwoOneStoredException {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx)
    (eta : Fin k)
    (hetaStored : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount))
    (hetaMissing :
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex))
    (hthetaPair :
      D.theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta) :
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
  have hcard : (C.good.gamma q eta).card = 2 :=
    C.good.twoColors q eta hetaStored
  obtain ⟨gamma, hgamma, hthetaGamma⟩ :
      ∃ gamma, gamma ∈ C.good.gamma q eta ∧ D.theta ≠ gamma := by
    by_contra hn
    push_neg at hn
    have hsubset : C.good.gamma q eta ⊆ {D.theta} := by
      intro c hc
      simp only [Finset.mem_singleton]
      exact (hn c hc).symm
    have hle := Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hle
    omega
  have hpair : C.good.gamma q eta = {D.theta, gamma} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hthetaPair
      · exact hgamma
    · simp [hthetaGamma, hcard]
  have hgammaAvoid := Finset.mem_sdiff.mp
    (C.good.avoidance q eta hetaStored hgamma)
  have hgammaA : gamma ∈ TreeMissingColors phi A := by
    by_cases hq : H.dividerCount = 0
    · have hz : q = 0 := by apply Fin.ext; simp [q, hq]
      have hm : gamma ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [HierarchyStageMissingColors, hz] using hgammaAvoid.1
      exact missingMono (hierarchyGeometry H).2 phi hm
    · have hpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hq
      have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp [q]
        omega
      simpa [A, HierarchyStarredStage, HierarchyStageMissingColors, hi]
        using hgammaAvoid.1
  have halpha := HierarchySituationTwoCaseTwoExclusions
    G k e0 input T phi ett base C ctx D
  have hgammaAlpha : gamma ≠ D.alpha := by
    intro heq
    exact halpha.1 (heq ▸ missingMono hAB phi hgammaA)
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
      · simp only [hetaFirst]
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
      (htheta : P.coloring (T.edge D.lastEdgeIndex) = some D.theta)
      (hthetaPresent : D.theta ∉ MissingColors G P.coloring
        (T.vertex D.penultimateVertexIndex)) :
      ∃ P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        P'.coloring = TwoColorComponentSwap G P.coloring a b
            (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
          (∀ v ∈ TreeSequenceVertexSet X,
            MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
          ∀ t : Fin T.length, A.length ≤ t.val →
            P'.coloring (T.edge t) = P.coloring (T.edge t) := by
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
    have hbFirst : HierarchyFirstMissingPosition col T b =
        D.penultimateVertexIndex := by
      have hm := firstMissing col b D.penultimateVertexIndex hb
      have hv : T.vertex (HierarchyFirstMissingPosition col T b) ∈
          TreeSequenceVertexSet X := by
        apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        refine ⟨⟨(HierarchyFirstMissingPosition col T b).val, by
          rw [hXlen]
          have hpos := D.penultimateVertexPosition
          omega⟩, Finset.mem_univ _, ?_⟩
        rfl
      by_contra hi
      exact Finset.disjoint_left.mp
        (hxElem hv hyp (fun h => hi (T.vertex_injective h))) hm.1 hb
    obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp haA
    obtain ⟨i, _, hiv⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    have hai : a ∈ MissingColors G col
        (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i)) := by
      rw [hAT.2.1 i, hiv]
      exact hav
    have haFirst := firstMissing col a _ hai
    have haBound : (HierarchyFirstMissingPosition col T a).val ≤ A.length :=
      le_trans haFirst.2 (Nat.le_of_lt_succ i.isLt)
    let va := T.vertex (HierarchyFirstMissingPosition col T a)
    let vb := T.vertex D.penultimateVertexIndex
    let vt := T.vertex D.terminalVertexIndex
    have hvaX : va ∈ TreeSequenceVertexSet X := by
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨⟨(HierarchyFirstMissingPosition col T a).val, by
        rw [hXlen]
        omega⟩, Finset.mem_univ _, ?_⟩
      rfl
    have horder : (HierarchyFirstMissingPosition col T a).val <
        D.penultimateVertexIndex.val := by
      have hp := D.penultimateVertexPosition
      omega
    have hnorm :
        (0 < H'.dividerCount ∧
          a ∈ TreeMissingColors col (H'.stage ⟨H'.dividerCount, by omega⟩)) ∨
        (H'.dividerCount = 0 ∧ a ∈ TreeMissingColors col
          (J.series.data.tree (Fin.last J.rounds).castSucc)) := by
      change a ∈ HierarchyStageMissingColors H' q' at haStage
      by_cases hq : H'.dividerCount = 0
      · right
        refine ⟨hq, ?_⟩
        have hi : q' = 0 := by apply Fin.ext; simp [q', hq]
        simpa [HierarchyStageMissingColors, hi] using haStage
      · left
        refine ⟨Nat.pos_of_ne_zero hq, ?_⟩
        have hi : q' =
            (⟨H'.dividerCount - 1, by omega⟩ : Fin H'.dividerCount).succ := by
          apply Fin.ext
          simp [q']
          omega
        have ha := haStage
        simp only [HierarchyStageMissingColors, hi, Fin.cases] at ha
        convert ha using 1
        apply congrArg (TreeMissingColors col)
        apply congrArg H'.stage
        apply Fin.ext
        simp
        omega
    have hmissing : a ∈ TreeMissingColors col X ∧ b ∈ TreeMissingColors col X :=
      ⟨missingMono hAX col haA, Finset.mem_biUnion.mpr ⟨vb, hyp, hb⟩⟩
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
        · simpa [hbFirst] using horder
        · intro hc
          obtain ⟨t, ht, _, hcol⟩ := (Finset.mem_filter.mp hc).2
          exact haTail t (by simpa only [hstar] using ht) hcol)
    have hsame : TwoColorComponent G col a b (Sum.inl va) =
        TwoColorComponent G col a b (Sum.inl vb) := by
      rcases hnorm with ⟨hq, ha⟩ | ⟨hq, ha⟩
      · simpa [va, vb, hbFirst] using hchange.1 ⟨hq, Or.inl ha⟩
      · simpa [va, vb, hbFirst] using hchange.2.1 ⟨hq, Or.inl ha⟩
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
          (heq.symm ▸ hsame.symm ▸ rootMem (Sum.inl vb)) (Or.inr hb)
        have htEnd := endpoint vt (rootMem z) hterminal
        have hab : (Sum.inl va : Sum V E) ≠ Sum.inl vb := by
          intro h
          have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
          omega
        have hat : (Sum.inl va : Sum V E) ≠ Sum.inl vt := by
          intro h
          have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
          have ht := D.terminalVertexPosition
          omega
        have hbt : (Sum.inl vb : Sum V E) ≠ Sum.inl vt := by
          intro h
          have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
          have hbp := D.penultimateVertexPosition
          have htp := D.terminalVertexPosition
          omega
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
    have hcase :
        (0 < H'.dividerCount ∧
          a ∈ TreeMissingColors col (H'.stage ⟨H'.dividerCount, by omega⟩)) ∨
        (H'.dividerCount = 0 ∧
          (a ∈ TreeMissingColors col (J.series.data.tree (Fin.last J.rounds).castSucc) ∨
            (a ∈ TreeMissingColors col
                (HierarchyStarredStage H' q') ∧
              a ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds) ∧
              b ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds)))) := by
      rcases hnorm with h | ⟨hq, ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨hq, Or.inl ha⟩
    -- Obtain weak stability before protecting the possible SE/RE seed.
    have hstable := StableChangeCasesOneTwo G k e0 P.corresponding.replacementInput
      T col J P.replacementBase C' hp P.minimumContext.oneEdgeUncolored
      P.minimumContext.lowerRung P.minimumContext.fewerDividers
      P.minimumContext.lexicographicMinimality
      helemP
      P.minimumContext.largeMissingSet a b hne
      hmissingP
      z hpath mu rfl hcase hdis
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
            exact Finset.disjoint_left.mp (hxElem hu hyp hn) hbu hb
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
        · have htb : D.theta = b :=
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
    have hbNew : b ∈ MissingColors G mu (T.vertex D.penultimateVertexIndex) := by
      rw [hprefix _ hyp]
      exact hb
    have hbNewFirst : HierarchyFirstMissingPosition mu T b =
        D.penultimateVertexIndex := by
      have hm := firstMissing mu b D.penultimateVertexIndex hbNew
      let i : Fin (X.length + 1) := ⟨(HierarchyFirstMissingPosition mu T b).val, by
        exact Nat.lt_succ_of_le (hm.2.trans (Nat.le_of_eq hPenVal))⟩
      have hv : T.vertex (HierarchyFirstMissingPosition mu T b) ∈
          TreeSequenceVertexSet X :=
        (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hmOld : b ∈ MissingColors G col
          (T.vertex (HierarchyFirstMissingPosition mu T b)) := by
        rw [← hprefix _ hv]
        exact hm.1
      by_contra hn
      exact Finset.disjoint_left.mp
        (hxElem hv hyp (fun he => hn (T.vertex_injective he))) hmOld hb
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
        exact hbNewFirst.trans hbFirst.symm
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
    have hfull := StableChangeCasesOneTwoFullTail G k e0
      P.corresponding.replacementInput T col J P.replacementBase C' P.minimumContext
      a b hne hmissingP
      z hpath mu rfl hcase hdis
      (by dsimp only; intro t ht
          exact htailEdges t (by simpa only [hstar] using ht))
      (by intro v hv; rw [hXeq] at hv; exact hprefix v hv) hstoredFirst
    obtain ⟨corr, hmax, baseNew, Hnew, goodNew, hsameGood⟩ := hfull.2.2.2.2
    have hnonElem : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet T) := by
      intro he
      have htMem : vt ∈ TreeSequenceVertexSet T :=
        (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨D.terminalVertexIndex, Finset.mem_univ _, rfl⟩
      rcases hterminal with hta | htb
      · have hbTerminal : b ∈ MissingColors G mu vt := hbehavior.2.1 vt (rootMem z) hta
        have hpMem := TreeSequenceInitialSegmentVertexSetSubset hXT hyp
        have hnept : vb ≠ vt := by
          intro heq
          have hi := congrArg Fin.val (T.vertex_injective heq)
          have hpp := D.penultimateVertexPosition
          have htp := D.terminalVertexPosition
          omega
        exact Finset.disjoint_left.mp (he hpMem htMem hnept) hbNew hbTerminal
      · have haTerminal : a ∈ MissingColors G mu vt := hbehavior.2.2.1 vt (rootMem z) htb
        have hvaNot : Sum.inl va ∉ TwoColorComponent G col a b z := by
          intro hva
          exact Set.disjoint_left.mp hdis hva (rootMem (Sum.inl va))
        have haNew : a ∈ MissingColors G mu va := by
          rw [hbehavior.1 va hvaNot]
          exact haFirst.1
        have haMem := TreeSequenceInitialSegmentVertexSetSubset hXT hvaX
        have hneat : va ≠ vt := by
          intro heq
          have hi := congrArg Fin.val (T.vertex_injective heq)
          have htp := D.terminalVertexPosition
          omega
        exact Finset.disjoint_left.mp (he haMem htMem hneat) haNew haTerminal
    let Cnew : HierarchyCounterexample baseNew := {
      positive := by rw [corr.rungAgreement]; exact C'.positive
      hierarchy := Hnew
      good := goodNew
      maximum := hmax
      notElementary := hnonElem }
    obtain ⟨Pnew, hcolor⟩ := HierarchyReplacementPresentationTrans
      G k e0 input T phi ett base C ctx P mu corr baseNew Cnew hsameGood
    refine ⟨Pnew, hcolor, ?_, ?_⟩
    · simpa [hcolor] using hprefix
    · simpa [hcolor] using htailEdges
  have hlastTail : A.length ≤ D.lastEdgeIndex.val := by
    have hp := D.lastEdgePosition
    omega
  have storedPair (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
        P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta =
          {D.theta, gamma} := by
    obtain ⟨hcount, hslots⟩ := P.sameGood.2
    have hs := hslots q
    have hi : Fin.cast (congrArg (fun n => n + 1) hcount) q =
        Fin.last P.counterexample.hierarchy.dividerCount := by
      apply Fin.ext
      exact hcount
    rw [hi] at hs
    exact ⟨hs.1 ▸ hetaStored, (hs.2 eta hetaStored).symm.trans hpair⟩
  have reduceCaseOne
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hprefix : ∀ v ∈ TreeSequenceVertexSet X,
        MissingColors G P.coloring v = MissingColors G phi v)
      (hedges : ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) = phi (T.edge t))
      (hterminal : eta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex)) :
      False := by
    have hg := presentationGeometry P
    have hsp := storedPair P
    let D1 : HierarchySituationTwoCaseOneData G k e0 P.corresponding.replacementInput
        T P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext := {
      tailAtLeastTwo := by simpa [hg.2.1] using htail
      pathNumberFull := hg.2.2.2.trans (D.pathNumberFull.trans hg.2.1.symm)
      lastEdgeIndex := D.lastEdgeIndex
      penultimateVertexIndex := D.penultimateVertexIndex
      terminalVertexIndex := D.terminalVertexIndex
      lastEdgePosition := D.lastEdgePosition
      penultimateVertexPosition := D.penultimateVertexPosition
      terminalVertexPosition := D.terminalVertexPosition
      lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
      theta := D.theta
      thetaOnLastEdge := (hedges _ hlastTail).trans D.thetaOnLastEdge
      thetaPresentPenultimate := by rw [hprefix _ hyp]; exact D.thetaPresentPenultimate
      alpha := eta
      gammaOne := D.theta
      gammaTwo := gamma
      alphaMissingPenultimate := by rw [hprefix _ hyp]; exact hetaMissing
      alphaMissingTerminal := hterminal
      alphaStored := hsp.1
      gammaPair := hsp.2
      gammaDistinct := hthetaGamma }
    exact HierarchySituationTwoSubcaseOneOne G k e0 P.corresponding.replacementInput
      T P.coloring P.corresponding.replacementETT P.replacementBase
      P.counterexample P.minimumContext D1
  obtain ⟨P1, hmu1, hprefix1, hedges1⟩ := swapStep P0 gamma D.alpha hgammaAlpha
    hgammaA hgammaAvoid.1 hgammaTail D.alphaMissingPenultimate
    (Or.inr D.alphaMissingTerminal) D.thetaOnLastEdge D.thetaPresentPenultimate
  have hgammaTerminal : gamma ∈ MissingColors G P1.coloring
      (T.vertex D.terminalVertexIndex) := by
    rw [hmu1]
    apply (TwoColorComponentSwapMissingBehavior G phi gamma D.alpha
      hgammaAlpha ctx.proper (Sum.inl (T.vertex D.terminalVertexIndex))).2.2.1
    · change (TwoColorIncidenceGraph G phi gamma D.alpha).connectedComponentMk _ = _
      rfl
    · exact D.alphaMissingTerminal
  by_cases hetaTerminal : eta ∈ MissingColors G P1.coloring (T.vertex D.terminalVertexIndex)
  · exact reduceCaseOne P1 hprefix1 hedges1 hetaTerminal
  · have hetaPenultimate : eta ∈ MissingColors G P1.coloring
        (T.vertex D.penultimateVertexIndex) := by
      rw [hprefix1 _ hyp]
      exact hetaMissing
    have hgammaA1 : gamma ∈ TreeMissingColors P1.coloring A := by
      obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hgammaA
      exact Finset.mem_biUnion.mpr ⟨v, hv, by
        rw [hprefix1 v (TreeSequenceInitialSegmentVertexSetSubset hAX hv)]
        exact hc⟩
    have hgammaEta : gamma ≠ eta := by
      intro he
      exact (Finset.mem_sdiff.mp hetaStored).2 (he ▸ hgammaA)
    have hpair1 := storedPair P1
    have hgammaMem1 : gamma ∈ P1.counterexample.good.gamma
        (Fin.last P1.counterexample.hierarchy.dividerCount) eta := by
      rw [hpair1.2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self gamma)
    have hstage1 := (Finset.mem_sdiff.mp
      (P1.counterexample.good.avoidance _ eta hpair1.1 hgammaMem1)).1
    have hgammaTail1 : ∀ t : Fin T.length, A.length ≤ t.val →
        P1.coloring (T.edge t) ≠ some gamma := by
      intro t ht
      rw [hedges1 t ht]
      exact hgammaTail t ht
    have htheta1 := (hedges1 _ hlastTail).trans D.thetaOnLastEdge
    have hthetaPresent1 : D.theta ∉ MissingColors G P1.coloring
        (T.vertex D.penultimateVertexIndex) := by
      rw [hprefix1 _ hyp]
      exact D.thetaPresentPenultimate
    obtain ⟨P2, hmu2, hprefix2, hedges2⟩ := swapStep P1 gamma eta hgammaEta
      hgammaA1 hstage1 hgammaTail1 hetaPenultimate (Or.inl hgammaTerminal)
      htheta1 hthetaPresent1
    have hetaTerminal2 : eta ∈ MissingColors G P2.coloring
        (T.vertex D.terminalVertexIndex) := by
      rw [hmu2]
      apply (TwoColorComponentSwapMissingBehavior G P1.coloring gamma eta
        hgammaEta P1.minimumContext.proper
        (Sum.inl (T.vertex D.terminalVertexIndex))).2.1
      · change (TwoColorIncidenceGraph G P1.coloring gamma eta).connectedComponentMk _ = _
        rfl
      · exact hgammaTerminal
    exact reduceCaseOne P2 (fun v hv => (hprefix2 v hv).trans (hprefix1 v hv))
      (fun t ht => (hedges2 t ht).trans (hedges1 t ht)) hetaTerminal2
