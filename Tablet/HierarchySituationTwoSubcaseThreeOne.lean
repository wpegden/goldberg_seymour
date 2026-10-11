import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseThreeNormalization
import Tablet.HierarchySituationTwoCaseThreeOneData
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchySituationTwoSubcaseOneOne
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.MissingColors
import Tablet.ModColoring
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
import Tablet.TashkinovStoredColors
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.P2752_T2_MinimumContextTransport
import Tablet.P2752_T2_HierarchyMeasures
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.MissingColorIncidenceEndpoint
import Tablet.P2752_T2_TerminalStoredColors
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute
import Tablet.TashkinovAugmentationSequenceSuffix

-- [TABLET NODE: HierarchySituationTwoSubcaseThreeOne]
theorem HierarchySituationTwoSubcaseThreeOne {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeOneData
      G k e0 input T phi ett base C ctx) :
    False := by
-- BODY
  classical
  let alpha : Fin k := D.alpha
  let theta : Fin k := D.theta
  let lastIndex : Fin T.length := D.lastEdgeIndex
  let penIndex : Fin (T.length + 1) := D.penultimateVertexIndex
  let endIndex : Fin (T.length + 1) := D.terminalVertexIndex
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let Bplus := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have lastColor : phi (T.edge lastIndex) = some theta := D.thetaOnLastEdge
  have alphaTerminal : alpha ∈ MissingColors G phi (T.vertex endIndex) := D.alphaMissingTerminal
  have alphaBefore : alpha ∈ TreeMissingColors phi B := D.alphaMissingTwoBefore
  have alphaUnused : ∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some alpha :=
    D.alphaUnusedOnFullTail
  have lastPosition : lastIndex.val + 1 = T.length := D.lastEdgePosition
  have penPosition : penIndex.val + 1 = T.length := D.penultimateVertexPosition
  have endPosition : endIndex.val = T.length := D.terminalVertexPosition
  have thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex) := D.thetaPresentPenultimate
  have oldRoute := P2813_T1_TerminalRoute G k e0 input T phi ett
  have h_exception : ∃ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt H q ∧
      eta ∈ MissingColors G phi (T.vertex penIndex) ∧
      theta ∈ C.good.gamma q eta := by
    as_aux_lemma =>
      let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
        { tailAtLeastTwo := D.tailAtLeastTwo
          pathNumberFull := D.pathNumberFull
          lastEdgeIndex := lastIndex
          penultimateVertexIndex := penIndex
          terminalVertexIndex := endIndex
          lastEdgePosition := lastPosition
          penultimateVertexPosition := penPosition
          terminalVertexPosition := endPosition
          lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
          theta := theta
          thetaOnLastEdge := lastColor
          thetaPresentPenultimate := thetaPresent }
      obtain ⟨R, hboundaryPE, hrouteMinus, hrouteStar, corrMinus, maxMinus,
          baseMinus, hcoreMinus, hclosureMinus, hsupportMinus, HMinus, hcountMinus,
          hstageMinus, hpositionMinus, corrStar, maxStar, baseStar, hcoreStar,
          hclosureStar, hsupportStar, HStar, hcountStar, hstageStar, hpositionStar⟩ :=
        HierarchySituationTwoReorderedTreesCertified G k e0 input T phi ett base C ctx tail
      by_contra hnone
      have hnone' : ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
          eta ∈ MissingColors G phi (T.vertex penIndex) →
          theta ∉ C.good.gamma q eta := by
        intro eta hs hm hgamma
        exact hnone ⟨eta, hs, hm, hgamma⟩
      have transSegment {X Y Z : TreeSequence G e0}
          (hXY : TreeSequenceInitialSegment X Y)
          (hYZ : TreeSequenceInitialSegment Y Z) :
          TreeSequenceInitialSegment X Z := by
        as_aux_lemma =>
          refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
          · intro i
            exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
          · intro i
            exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
      have restrictSegment {X Y Z : TreeSequence G e0}
          (hXZ : TreeSequenceInitialSegment X Z)
          (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
          TreeSequenceInitialSegment X Y := by
        as_aux_lemma =>
          refine ⟨hXY, ?_, ?_⟩
          · intro i
            exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
          · intro i
            exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
      have starredAt (j : Fin (H.dividerCount + 1)) (hj : j.val ≠ 0) :
          HierarchyStarredStage H j = H.stage j.castSucc := by
        as_aux_lemma =>
          obtain hz | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
          · exact False.elim (hj (congrArg Fin.val hz))
          · rfl
      have hAT : TreeSequenceInitialSegment A T := by
        by_cases hz : H.dividerCount = 0
        · have hq : q = 0 := Fin.ext (by simp [q, hz])
          have hs : (⟨1, Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le _))⟩ : Fin (H.dividerCount + 2)) =
              Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
          simpa [A, hq, HierarchyStarredStage, hs, H.terminalStage] using H.coreInsideFirst
        · have ha : A = H.stage q.castSucc := starredAt q (by simpa [q] using hz)
          rw [ha]
          have hs : H.stage q.succ = T := by convert H.terminalStage using 1; congr 1
          simpa only [hs] using H.nested q
      have htail : 2 ≤ ell := D.tailAtLeastTwo
      have hell : ell = T.length - A.length := rfl
      have hBL : B.length + 2 = T.length := by
        simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength, TreeSequencePrefix]
        change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
        omega
      have hPL : Bplus.length + 1 = T.length := by
        simp only [Bplus, HierarchyFullTailPrefix, HierarchyFullTailLength, TreeSequencePrefix]
        change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
        omega
      have hBT : TreeSequenceInitialSegment B T :=
        ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
      have hBplusT : TreeSequenceInitialSegment Bplus T :=
        ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
      have hAB : TreeSequenceInitialSegment A B := restrictSegment hAT hBT (by omega)
      have hBBplus : TreeSequenceInitialSegment B Bplus :=
        restrictSegment hBT hBplusT (by omega)
      have hBM := R.minusFinal.2.1
      have hMinusLen := R.minusFinal.1
      have hBMlen : R.minus.length = B.length + 1 := by omega
      have hBM' : TreeSequenceInitialSegment B R.minus := hBM
      have hBS := transSegment hBM' R.starFinal.2.1
      have hminusLen : R.minus.length + 1 = T.length := by omega
      have hPE : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
        HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
          ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
          ctx.lexicographicMinimality ctx.largeMissingSet
      have vertexMem (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
          X.vertex i ∈ TreeSequenceVertexSet X := by
        exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
      have firstLe (X : TreeSequence G e0) (c : Fin k)
          (i : Fin (X.length + 1)) (hi : c ∈ MissingColors G phi (X.vertex i)) :
          (HierarchyFirstMissingPosition phi X c).val ≤ i.val := by
        as_aux_lemma =>
          unfold HierarchyFirstMissingPosition
          dsimp only
          have hm : i ∈ Finset.univ.filter
              (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          rw [dif_pos ⟨i, hm⟩]
          exact Finset.min'_le _ _ hm
      have firstMissing (X : TreeSequence G e0) (c : Fin k)
          (hc : c ∈ TreeMissingColors phi X) :
          c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
        as_aux_lemma =>
          obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
          obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
          unfold HierarchyFirstMissingPosition
          dsimp only
          have hm : i ∈ Finset.univ.filter
              (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩
          rw [dif_pos ⟨i, hm⟩]
          exact (Finset.mem_filter.mp (Finset.min'_mem _ ⟨i, hm⟩)).2
      have firstBefore (X : TreeSequence G e0) (c : Fin k)
          (i : Fin (X.length + 1))
          (hi : i.val < (HierarchyFirstMissingPosition phi X c).val) :
          c ∉ MissingColors G phi (X.vertex i) := by
        as_aux_lemma =>
          intro hm
          have := firstLe X c i hm
          omega
      have firstLower (X : TreeSequence G e0) (c : Fin k) (t : ℕ)
          (ht : t ≤ X.length)
          (hn : ∀ i : Fin (X.length + 1), i.val < t →
            c ∉ MissingColors G phi (X.vertex i)) :
          t ≤ (HierarchyFirstMissingPosition phi X c).val := by
        as_aux_lemma =>
          by_contra hlt
          have hp : (HierarchyFirstMissingPosition phi X c).val < t := by omega
          have hm : c ∈ TreeMissingColors phi X := by
            by_contra hm
            have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
              unfold HierarchyFirstMissingPosition
              dsimp only
              rw [dif_neg]
              rintro ⟨i, hi⟩
              exact hm (Finset.mem_biUnion.mpr ⟨X.vertex i, vertexMem X i,
                (Finset.mem_filter.mp hi).2⟩)
            have := congrArg Fin.val he
            simp only [Fin.val_last] at this
            omega
          exact hn _ hp (firstMissing X c hm)
      have oldAvoid (eta c : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
          (hc : c ∈ C.good.gamma q eta) :
          c ∉ Finset.univ.filter (fun c => ∃ r : Fin T.length,
            A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
            phi (T.edge r) = some c) := by
        as_aux_lemma =>
          have hh := (Finset.mem_sdiff.mp (C.good.avoidance q eta hs hc)).2
          change c ∉ HierarchySegmentColors H q eta at hh
          unfold HierarchySegmentColors at hh
          dsimp only at hh
          have hend : H.stage q.succ = T := by convert H.terminalStage using 1; congr 1
          rw [hend] at hh
          exact hh
      have thetaCutoff (eta : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
          (hc : theta ∈ C.good.gamma q eta) :
          (HierarchyFirstMissingPosition phi T eta).val ≤ B.length := by
        as_aux_lemma =>
          clear * - G T phi A B D hs hc firstMissing oldAvoid hnone' vertexMem lastIndex lastColor lastPosition penPosition theta penIndex
            hBL htail hell
          have hlast : lastIndex.val = B.length + 1 := by
            have := lastPosition
            omega
          have hpen : penIndex.val = B.length + 1 := by
            have := penPosition
            omega
          by_contra hcut
          have hgt : B.length < (HierarchyFirstMissingPosition phi T eta).val := by omega
          by_cases hafter : B.length + 1 < (HierarchyFirstMissingPosition phi T eta).val
          · apply oldAvoid eta theta hs hc
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lastIndex,
              by have := lastPosition; omega,
              by have := lastIndex.isLt; omega, lastColor⟩
          · have heq : HierarchyFirstMissingPosition phi T eta = penIndex := by
              apply Fin.ext
              have hpos := penPosition
              omega
            have hm := firstMissing T eta (by
              by_contra h
              have he : HierarchyFirstMissingPosition phi T eta = Fin.last T.length := by
                unfold HierarchyFirstMissingPosition
                dsimp only
                rw [dif_neg]
                intro hne
                obtain ⟨i, hi⟩ := hne
                exact h (Finset.mem_biUnion.mpr ⟨T.vertex i, vertexMem T i,
                  (Finset.mem_filter.mp hi).2⟩)
              have hv := congrArg Fin.val he
              simp only [Fin.val_last] at hv
              omega)
            rw [heq] at hm
            exact hnone' eta hs hm hc
      have terminalData :
          corrMinus.replacementETT.series.data.tree
              (Fin.last corrMinus.replacementETT.rounds).castSucc = Tn ∧
          corrMinus.replacementETT.series.data.kind
              (Fin.last corrMinus.replacementETT.rounds) =
            ett.series.data.kind n ∧
          TashkinovStoredColors corrMinus.replacementETT.series.data
              (Fin.last corrMinus.replacementETT.rounds) =
            TashkinovStoredColors ett.series.data n := by
        as_aux_lemma =>
          rcases corrMinus with ⟨newInput, newSeries, newETT, hr, hs, hf,
            ht, hd, he, hk, hp, ho, hstable⟩
          cases newETT with
          | mk rounds positive data above strict below generating =>
            cases hr
            have hseries : data = newSeries := eq_of_heq hs
            cases hseries
            let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
            have hi : i.succ = Fin.last ett.rounds := Fin.ext (by
              simp [i]; have := ett.roundsPositive; omega)
            have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
              simpa [Tn, n, hi] using ht i
            refine ⟨htree, hk _, ?_⟩
            have hstored :
                TashkinovStoredColors newSeries.data (Fin.last ett.rounds) =
                  TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
              unfold TashkinovStoredColors
              simp only [Fin.val_last]
              simp_rw [hd]
              rw [← hf, ← ett.generatingColoring, htree]
            simpa [n] using hstored
      have hierarchyInfo : ∀ j : Fin (HMinus.dividerCount + 1),
          let jo := Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
          HierarchyStarredStage HMinus j = HierarchyStarredStage H jo ∧
          HierarchyStoredColorsAt HMinus j = HierarchyStoredColorsAt H jo ∧
          HierarchyStageMissingColors HMinus j = HierarchyStageMissingColors H jo := by
        intro j
        let index := fun j : Fin (HMinus.dividerCount + 1) =>
          Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
        have hz : index 0 = 0 := Fin.ext rfl
        have hstar : HierarchyStarredStage HMinus j = HierarchyStarredStage H (index j) := by
          obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
          · subst j
            simpa [hz, HierarchyStarredStage] using hcoreMinus
          · have hi : (index i.succ).val ≠ 0 := by simp [index]
            rw [starredAt (index i.succ) hi]
            exact hstageMinus i.succ
        refine ⟨hstar, ?_, ?_⟩
        · unfold HierarchyStoredColorsAt
          dsimp only
          rw [terminalData.2.2, hstar]
        · obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
          · subst j
            simp [HierarchyStageMissingColors, hz, Tn, n, terminalData.1]
          · have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
            let io : Fin H.dividerCount := ⟨i.val, by rw [← hcount]; exact i.isLt⟩
            have hi : index i.succ = io.succ := Fin.ext rfl
            simp only [HierarchyStageMissingColors, hi, Fin.cases_succ]
            exact congrArg (TreeMissingColors phi) (hstageMinus i.succ)
      have stageEq (j : Fin (HMinus.dividerCount + 1)) :
          HMinus.stage j.castSucc = H.stage
            (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j).castSucc := hstageMinus j
      have starredEq (j : Fin (HMinus.dividerCount + 1)) :
          HierarchyStarredStage HMinus j = HierarchyStarredStage H
            (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
        (hierarchyInfo j).1
      have storedEq (j : Fin (HMinus.dividerCount + 1)) :
          HierarchyStoredColorsAt HMinus j = HierarchyStoredColorsAt H
            (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
        (hierarchyInfo j).2.1
      have missingEq (j : Fin (HMinus.dividerCount + 1)) :
          HierarchyStageMissingColors HMinus j = HierarchyStageMissingColors H
            (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
        (hierarchyInfo j).2.2
      have stageSegment : ∀ a d : ℕ,
          ∀ hb : a + d ≤ H.dividerCount + 1,
          TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
          (H.stage ⟨a + d, by omega⟩) := by
        as_aux_lemma =>
          clear * - H transSegment
          intro a d
          induction d with
          | zero => intro hb; exact ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
          | succ d ih =>
              intro hb
              have hp := ih (by omega)
              have hn := H.nested ⟨a + d, by omega⟩
              exact transSegment hp (by simpa [Nat.add_assoc] using hn)
      have nextBound (i : Fin H.dividerCount) :
          (H.stage i.succ.castSucc).length ≤ B.length := by
        as_aux_lemma =>
          have hqpos : 0 < H.dividerCount := by have := i.isLt; omega
          have hqval : 0 < q.val := by simpa [q] using hqpos
          have hA : A = H.stage q.castSucc := starredAt q (by
            intro hz
            exact (Nat.ne_of_gt hqval) hz)
          have hs := stageSegment (i.val + 1) (H.dividerCount - (i.val + 1)) (by
            have := i.isLt
            omega)
          have hlo : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc :=
            Fin.ext rfl
          have hhi : (⟨i.val + 1 + (H.dividerCount - (i.val + 1)), by omega⟩ :
              Fin (H.dividerCount + 2)) = q.castSucc := by
            apply Fin.ext
            simp [q]
          rw [hlo, hhi, ← hA] at hs
          exact le_trans hs.1 hAB.1
      have edgesMinus (r : Fin R.minus.length) :
          (∃ t : Fin T.length, t.val = r.val ∧ r.val < B.length ∧
            R.minus.edge r = T.edge t) ∨
          (r.val = B.length ∧ R.minus.edge r = T.edge lastIndex) := by
        as_aux_lemma =>
          by_cases hr : r.val < B.length
          · let i : Fin B.length := ⟨r.val, hr⟩
            have he : Fin.castLE hBM.1 i = r := Fin.ext rfl
            have hprefix : TreeSequenceInitialSegment B R.minus := hBM
            refine Or.inl ⟨Fin.castLE hBT.1 i, rfl, hr, ?_⟩
            rw [← he, hprefix.2.2 i, hBT.2.2 i]
          · have he : r = Fin.cast hBMlen.symm (Fin.last B.length) := by
              apply Fin.ext
              simp
              omega
            exact Or.inr ⟨by have := r.isLt; omega, by rw [he]; exact R.minusFinal.2.2⟩
      have firstWitness (X : TreeSequence G e0) (c : Fin k)
          (hc : (HierarchyFirstMissingPosition phi X c).val < X.length) :
          c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
        let W := Finset.univ.filter fun i : Fin (X.length + 1) =>
          c ∈ MissingColors G phi (X.vertex i)
        by_cases hw : W.Nonempty
        · have he : HierarchyFirstMissingPosition phi X c = W.min' hw := by
            simp only [HierarchyFirstMissingPosition, W, dif_pos hw]
          rw [he]
          exact (Finset.mem_filter.mp (Finset.min'_mem W hw)).2
        · have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
            simp only [HierarchyFirstMissingPosition, W, dif_neg hw]
          rw [he] at hc
          simp only [Fin.val_last] at hc
          omega
      have terminalAvoid (eta c : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
          (hc : c ∈ C.good.gamma q eta)
          (hm : c ∈ Finset.univ.filter (fun c => ∃ r : Fin R.minus.length,
            A.length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition phi R.minus eta).val R.minus.length ∧
            phi (R.minus.edge r) = some c)) : False := by
        as_aux_lemma =>
          clear * - G T phi A B R D hs hc hm hBM hBT edgesMinus firstBefore lastColor theta
            firstLower oldAvoid thetaCutoff firstWitness firstLe hBL hBMlen hMinusLen hminusLen
          obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hm
          have hbeforeU : r.val < (HierarchyFirstMissingPosition phi R.minus eta).val :=
            lt_of_lt_of_le hhi (Nat.min_le_left _ _)
          have hcommonAbsent : ∀ i : Fin (T.length + 1), i.val ≤ B.length →
              i.val ≤ r.val → eta ∉ MissingColors G phi (T.vertex i) := by
            intro i hi hir
            let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
            have hindex : i.val < (HierarchyFirstMissingPosition phi R.minus eta).val := by
              change i.val < (HierarchyFirstMissingPosition phi R.minus eta).val
              omega
            have hj := firstBefore R.minus eta
              (Fin.castLE (Nat.succ_le_succ hBM.1) j) hindex
            have hvertex : R.minus.vertex (Fin.castLE (Nat.succ_le_succ hBM.1) j) =
                T.vertex i := by
              calc
                _ = B.vertex j := hBM.2.1 j
                _ = T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j) := hBT.2.1 j
                _ = T.vertex i := by congr 1
            rw [hvertex] at hj
            exact hj
          rcases edgesMinus r with ⟨t, htr, htb, hedge⟩ | ⟨hr, hedge⟩
          · have hcut : t.val + 1 ≤ (HierarchyFirstMissingPosition phi T eta).val :=
              firstLower T eta (t.val + 1) (by have := t.isLt; omega) (by
                intro i hi
                exact hcommonAbsent i (by omega) (by omega))
            have hmem : c ∈ Finset.univ.filter (fun c => ∃ r : Fin T.length,
                A.length ≤ r.val ∧
                r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
                phi (T.edge r) = some c) := by
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, t, ?_, ?_, ?_⟩
              · have := t.isLt
                omega
              · have := t.isLt
                omega
              · rw [← hedge]
                exact hcol
            exact oldAvoid eta c hs hc hmem
          · have hcTheta : c = theta := by
              rw [hedge, lastColor] at hcol
              exact (Option.some.inj hcol).symm
            subst c
            have hcut := thetaCutoff eta hs hc
            have hposLT : (HierarchyFirstMissingPosition phi T eta).val < T.length := by
              omega
            have hmissingT := firstWitness T eta hposLT
            let j : Fin (B.length + 1) :=
              ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
            have hjT : Fin.castLE (Nat.succ_le_succ hBT.1) j =
                HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
            have hmissingU : eta ∈ MissingColors G phi
                (R.minus.vertex (Fin.castLE (Nat.succ_le_succ hBM.1) j)) := by
              rw [hBM.2.1 j, ← hBT.2.1 j, hjT]
              exact hmissingT
            have hfirstU := firstLe R.minus eta _ hmissingU
            have hindex := r.isLt
            have : (HierarchyFirstMissingPosition phi R.minus eta).val ≤ B.length := by
              change (HierarchyFirstMissingPosition phi R.minus eta).val ≤ j.val at hfirstU
              have hjval : j.val = (HierarchyFirstMissingPosition phi T eta).val := rfl
              omega
            omega
      let index (j : Fin (HMinus.dividerCount + 1)) : Fin (H.dividerCount + 1) :=
        Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
      have indexZero : index 0 = 0 := Fin.ext rfl
      have indexLast : index (Fin.last HMinus.dividerCount) = q := by
        apply Fin.ext
        simp [index, q, hcountMinus]
      have segmentEq (i : Fin HMinus.dividerCount) (eta : Fin k) :
          HierarchySegmentColors HMinus i.castSucc eta =
            HierarchySegmentColors H (index i.castSucc) eta := by
        as_aux_lemma =>
          let io : Fin H.dividerCount := ⟨i.val, by
            have hi := i.isLt
            change HMinus.dividerCount = H.dividerCount at hcountMinus
            omega⟩
          have hnext : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
            Fin.ext rfl
          have hprev : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.castSucc = io.castSucc :=
            Fin.ext rfl
          have hnextIdx : index i.succ = io.succ := by simpa [index] using hnext
          have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprev
          have hcutOld := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta
            (H.stage io.succ.castSucc).length (nextBound io)
          have hcutNew := HierarchyFirstMissingPositionPrefixCutoff phi B R.minus hBM eta
            (H.stage io.succ.castSucc).length (nextBound io)
          have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
          have hio : io.castSucc.succ = io.succ.castSucc := Fin.ext rfl
          unfold HierarchySegmentColors
          dsimp only
          rw [hi, stageEq i.succ, starredEq i.castSucc, hnext, hprev, hprevIdx, hio,
            ← hcutNew, hcutOld]
      let goodMinus : GoodHierarchy HMinus := {
        gamma := fun j eta => C.good.gamma (index j) eta
        twoColors := by
          intro j eta hmem
          apply C.good.twoColors (index j) eta
          rw [← storedEq j]
          exact hmem
        avoidance := by
          intro j eta hmem c hc
          have holdMem : eta ∈ HierarchyStoredColorsAt H (index j) := by
            rw [← storedEq j]
            exact hmem
          have hold := Finset.mem_sdiff.mp (C.good.avoidance (index j) eta holdMem hc)
          refine Finset.mem_sdiff.mpr ⟨(missingEq j).symm ▸ hold.1, ?_⟩
          intro hseg
          by_cases hj : j.val < HMinus.dividerCount
          · let i : Fin HMinus.dividerCount := ⟨j.val, hj⟩
            have hij : i.castSucc = j := Fin.ext rfl
            have hOldSeg : c ∈ HierarchySegmentColors H (index j) eta := by
              have hnew : c ∈ HierarchySegmentColors HMinus i.castSucc eta := by
                simpa [hij] using hseg
              have hEq := segmentEq i eta
              have hindex : index j = index i.castSucc := by
                apply Fin.ext
                simp [hij]
              have hmem : c ∈ HierarchySegmentColors H (index i.castSucc) eta := by
                rw [← hEq]
                exact hnew
              simpa [hindex] using hmem
            exact hold.2 hOldSeg
          · have hjlast : j = Fin.last HMinus.dividerCount := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            subst j
            have havo := terminalAvoid eta c
              (by simpa [index, indexLast] using holdMem)
              (by simpa [index, indexLast] using hc)
              (by
                unfold HierarchySegmentColors at hseg
                dsimp only at hseg
                have hend : HMinus.stage (Fin.last HMinus.dividerCount).succ = R.minus := by
                  convert HMinus.terminalStage using 1
                  congr 1
                have hlastIndex :
                    Fin.cast (congrArg (fun d => d + 1) hcountMinus)
                      (Fin.last HMinus.dividerCount) = q := by
                  change index (Fin.last HMinus.dividerCount) = q
                  exact indexLast
                rw [hend, starredEq (Fin.last HMinus.dividerCount)] at hseg
                simpa [index, indexLast] using hseg)
            exact havo.elim
        disjointPairs := by
          intro j eta theta h₁ h₂ hne
          apply C.good.disjointPairs (index j) eta theta
          · rw [← storedEq j]; exact h₁
          · rw [← storedEq j]; exact h₂
          · exact hne
        uniqueRefresh := by
          intro i
          have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
          let io : Fin H.dividerCount := ⟨i.val, by simpa [hcount] using i.isLt⟩
          have hnext : io.succ = index i.succ := Fin.ext rfl
          have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
          have hnextFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
            Fin.ext rfl
          have hprevFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.castSucc = io.castSucc :=
            Fin.ext rfl
          have hnextIdx : index i.succ = io.succ := by simpa [index] using hnextFin
          have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprevFin
          obtain ⟨chosen, hchosen, hunique⟩ := C.good.uniqueRefresh io
          refine ⟨chosen, ?_, ?_⟩
          · rcases hchosen with ⟨hs, hlocal, hstable⟩
            refine ⟨?_, ?_, ?_⟩
            · rw [storedEq i.succ, hnextFin]
              exact hs
            · rw [stageEq i.succ, starredEq i.castSucc, hnextFin, hprevFin]
              exact hlocal
            · intro theta htheta hne
              have hthetaOld := htheta
              rw [storedEq i.succ] at hthetaOld
              rw [hnextFin] at hthetaOld
              exact hstable theta hthetaOld hne
          · intro eta heta
            have hetaOld : eta ∈ HierarchyStoredColorsAt H io.succ := by
              have hh := heta.1
              rw [storedEq i.succ] at hh
              rw [hnextFin] at hh
              exact hh
            have hlocalOld : C.good.gamma io.succ eta ⊆
                (TreeSequenceVertexSet (H.stage io.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage H io.castSucc)).biUnion
                  fun v => MissingColors G phi v := by
              have hh := heta.2.1
              rw [stageEq i.succ, starredEq i.castSucc, hnextFin, hprevFin] at hh
              exact hh
            have hstableOld : ∀ theta ∈ HierarchyStoredColorsAt H io.succ,
                theta ≠ eta → C.good.gamma io.succ theta = C.good.gamma io.castSucc theta := by
              intro theta htheta hne
              have hthetaNew : theta ∈ HierarchyStoredColorsAt HMinus i.succ := by
                have hh : theta ∈ HierarchyStoredColorsAt H (index i.succ) := by
                  rw [hnextIdx]
                  exact htheta
                rw [storedEq i.succ]
                exact hh
              have hh := heta.2.2 theta hthetaNew hne
              simpa [hnextIdx, hprevIdx] using hh
            apply hunique eta ⟨hetaOld, hlocalOld, hstableOld⟩
        parallelBase := by
          dsimp only
          intro hpe
          have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
            terminalData.2.1.symm.trans hpe
          have hold := C.good.parallelBase hpeOld
          rw [hcoreMinus, hclosureMinus, terminalData.1, storedEq 0]
          simpa [indexZero] using hold
        minusClosed := by
          intro i
          have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
          let io : Fin H.dividerCount := ⟨i.val, by simpa [hcount] using i.isLt⟩
          have hnext : io.succ = index i.succ := Fin.ext rfl
          have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
          have hnextFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
            Fin.ext rfl
          have hprevFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.castSucc = io.castSucc :=
            Fin.ext rfl
          have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprevFin
          have hold := C.good.minusClosed io
          rw [stageEq i.succ, storedEq i.succ]
          rw [hnextFin, hprevIdx]
          exact hold }
      have lastMinus :
          HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) = A := by
        calc
          HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) =
              HierarchyStarredStage H (index (Fin.last HMinus.dividerCount)) :=
            starredEq _
          _ = A := by simpa [A] using congrArg (HierarchyStarredStage H) indexLast
      have pathBound : HierarchyPathNumber HMinus ≤
          R.minus.length - (HierarchyStarredStage HMinus
            (Fin.last HMinus.dividerCount)).length := by
        unfold HierarchyPathNumber
        dsimp only
        split
        · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ _)).1).2
        · exact le_rfl
      obtain ⟨vAlpha, hvAlphaB, hmissAlpha⟩ :=
        Finset.mem_biUnion.mp alphaBefore
      have hvAlphaMinus : vAlpha ∈ TreeSequenceVertexSet R.minus :=
        TreeSequenceInitialSegmentVertexSetSubset hBM hvAlphaB
      have hterminalMinus : T.vertex endIndex ∈
          TreeSequenceVertexSet R.minus := by
        rw [← R.minusTerminalVertex]
        exact vertexMem R.minus (Fin.last R.minus.length)
      have hverticesNe : vAlpha ≠ T.vertex endIndex := by
        intro he
        obtain ⟨i, hi, rfl⟩ :=
          (@Finset.mem_image _ _ (Classical.decEq V)).mp hvAlphaB
        have heIndex : Fin.castLE (Nat.succ_le_succ hBT.1) i =
            endIndex := by
          apply T.vertex_injective
          exact (hBT.2.1 i).trans he
        have hv := congrArg Fin.val heIndex
        simp only [Fin.val_castLE] at hv
        have hiB : i.val ≤ B.length := Nat.lt_succ_iff.mp i.isLt
        have ht := endPosition
        omega
      have hnotElementary :
          ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet R.minus) := by
        intro helem
        have hdis := helem hvAlphaMinus hterminalMinus hverticesNe
        exact Finset.disjoint_left.mp hdis hmissAlpha alphaTerminal
      let CMinus : HierarchyCounterexample baseMinus := {
        positive := by rw [corrMinus.rungAgreement]; exact C.positive
        hierarchy := HMinus
        good := goodMinus
        maximum := maxMinus
        notElementary := hnotElementary }
      have hpathLess : HierarchyPathNumber HMinus < HierarchyPathNumber H := by
        rw [D.pathNumberFull]
        rw [lastMinus] at pathBound
        change HierarchyPathNumber HMinus < T.length - A.length
        have hlen : R.minus.length + 1 = T.length := by omega
        have hAlen : A.length ≤ R.minus.length := le_trans hAB.1 hBM.1
        omega
      have hmeasureLess : HierarchyCounterexampleLess
          (HierarchyCounterexampleMeasure CMinus)
          (HierarchyCounterexampleMeasure C) := Or.inl hpathLess
      exact (ctx.lexicographicMinimality CMinus corrMinus.rungAgreement hcountMinus)
        hmeasureLess
  rcases h_exception with ⟨eta, hetaStored, hetaMissing, hthetaGamma⟩
  have hTailAtLeast : 2 ≤ ell := D.tailAtLeastTwo
  have hellOuter : ell = T.length - A.length := rfl
  have hBLouter : B.length + 2 = T.length := by
    simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength, TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
    rw [← hellOuter]
    omega
  have hPLouter : Bplus.length + 1 = T.length := by
    simp only [Bplus, HierarchyFullTailPrefix, HierarchyFullTailLength, TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    rw [← hellOuter]
    omega
  have hBTouter : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBplusTouter : TreeSequenceInitialSegment Bplus T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBBplusOuter : TreeSequenceInitialSegment B Bplus := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hATouter : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hs : (⟨1, Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le _))⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
      simpa [A, hq, HierarchyStarredStage, hs, H.terminalStage] using H.coreInsideFirst
    · have hq : q ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        simp [q] at hv
        omega
      have ha : A = H.stage q.castSucc := by
        dsimp [A]
        rw [← Fin.succ_pred q hq]
        rfl
      rw [ha]
      have hs : H.stage q.succ = T := by
        convert H.terminalStage using 1
        congr 1
      simpa only [hs] using H.nested q
  have hABouter : TreeSequenceInitialSegment A B := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      exact hATouter.2.1 i
    · intro i
      exact hATouter.2.2 i
  have hABplusouter : TreeSequenceInitialSegment A Bplus := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      exact hATouter.2.1 i
    · intro i
      exact hATouter.2.2 i
  have hElemOuter : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have missingMonoOuter {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors phi X ⊆ TreeMissingColors phi Y :=
    Finset.biUnion_subset_biUnion_of_subset_left (MissingColors G phi)
      (TreeSequenceInitialSegmentVertexSetSubset hXY)
  have hAlphaWitness : ∃ v ∈ TreeSequenceVertexSet B,
      alpha ∈ MissingColors G phi v := by
    exact Finset.mem_biUnion.mp alphaBefore
  obtain ⟨vAlpha, hvAlpha, hAlphaAt⟩ := hAlphaWitness
  have vertexMemOuter (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
      X.vertex i ∈ TreeSequenceVertexSet X :=
    (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
  have firstMissingOuter (X : TreeSequence G e0) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi X) :
      c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
    as_aux_lemma =>
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      unfold HierarchyFirstMissingPosition
      dsimp only
      have hm : i ∈ Finset.univ.filter
          (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩
      rw [dif_pos ⟨i, hm⟩]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ ⟨i, hm⟩)).2
  have firstLeOuter (X : TreeSequence G e0) (c : Fin k)
      (i : Fin (X.length + 1)) (hi : c ∈ MissingColors G phi (X.vertex i)) :
      (HierarchyFirstMissingPosition phi X c).val ≤ i.val := by
    as_aux_lemma =>
      unfold HierarchyFirstMissingPosition
      dsimp only
      have hm : i ∈ Finset.univ.filter
          (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [dif_pos ⟨i, hm⟩]
      exact Finset.min'_le _ _ hm
  have firstBoundByPrefix (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi X) :
      (HierarchyFirstMissingPosition phi T c).val ≤ X.length := by
    as_aux_lemma =>
      obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      let j : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hXT.1) i
      have hj : c ∈ MissingColors G phi (T.vertex j) := by
        rw [hXT.2.1 i]
        exact hvc
      have hfirst := firstLeOuter T c j hj
      change (HierarchyFirstMissingPosition phi T c).val ≤ j.val at hfirst
      dsimp [j] at hfirst
      have hi := i.isLt
      omega
  have hPenultimateInBplus :
      T.vertex penIndex ∈ TreeSequenceVertexSet Bplus := by
    let i : Fin (Bplus.length + 1) := ⟨Bplus.length, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i =
        penIndex := by
      apply Fin.ext
      have hp := penPosition
      have hpos : penIndex.val = Bplus.length := by
        have h1 : penIndex.val + 1 = Bplus.length + 1 :=
          hp.trans hPLouter.symm
        omega
      simp only [Fin.val_castLE, Fin.val_mk]
      simpa [i] using hpos.symm
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨i, Finset.mem_univ _, by
        apply congrArg T.vertex
        exact hi⟩
  have hBdef : B = HierarchyFullTailPrefix C (ell - 2) := rfl
  have hBplusDef : Bplus = HierarchyFullTailPrefix C (ell - 1) := rfl
  clear_value B Bplus
  have canonicalElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1))) :=
    hBplusDef ▸ hElemOuter
  have hAlphaEtaNe : alpha ≠ eta := by
    intro he
    have hvNe : vAlpha ≠ T.vertex penIndex := by
      intro hv
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hvAlpha
      have hi : Fin.castLE (Nat.succ_le_succ hBTouter.1) i =
          penIndex := by
        apply T.vertex_injective
        exact (hBTouter.2.1 i).trans hv
      have hval := congrArg Fin.val hi
      simp only [Fin.val_castLE] at hval
      have hiB : i.val ≤ B.length := Nat.lt_succ_iff.mp i.isLt
      have hp := penPosition
      omega
    have hvAlphaBplus := TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hvAlpha
    have hdis := hElemOuter hvAlphaBplus hPenultimateInBplus hvNe
    exact Finset.disjoint_left.mp hdis hAlphaAt (he ▸ hetaMissing)
  have hthetaInA : theta ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 eta hetaStored hthetaGamma
  have hetaNotA : eta ∉ TreeMissingColors phi A :=
    (Finset.mem_sdiff.mp hetaStored).2
  have hAlphaMissingBplus : alpha ∈ TreeMissingColors phi Bplus :=
    missingMonoOuter (X := B) (Y := Bplus) hBBplusOuter alphaBefore
  have hthetaMissingBplus : theta ∈ TreeMissingColors phi Bplus :=
    missingMonoOuter (X := A) (Y := Bplus) hABplusouter hthetaInA
  have canonicalMissing :
      theta ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (ell - 1)) ∧
        alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (ell - 1)) :=
    hBplusDef ▸ ⟨hthetaMissingBplus, hAlphaMissingBplus⟩
  have hetaFirst : HierarchyFirstMissingPosition phi T eta =
      penIndex := by
    apply Fin.ext
    have htreeMiss : eta ∈ TreeMissingColors phi T :=
      Finset.mem_biUnion.mpr ⟨T.vertex penIndex,
        vertexMemOuter T penIndex, hetaMissing⟩
    have hfirstAt := firstMissingOuter T eta htreeMiss
    have hle := firstLeOuter T eta penIndex hetaMissing
    by_contra hne
    have hlt : (HierarchyFirstMissingPosition phi T eta).val <
        penIndex.val := by omega
    let i : Fin (Bplus.length + 1) :=
      ⟨(HierarchyFirstMissingPosition phi T eta).val, by
        have hp := penPosition
        have hpos := hPLouter
        omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i =
        HierarchyFirstMissingPosition phi T eta := by
      apply Fin.ext
      rfl
    have hvFirst : T.vertex (HierarchyFirstMissingPosition phi T eta) ∈
        TreeSequenceVertexSet Bplus := by
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨i, Finset.mem_univ _, by
          rw [← hBplusTouter.2.1 i]
          apply congrArg T.vertex
          exact hi⟩
    have hverticesNe : T.vertex (HierarchyFirstMissingPosition phi T eta) ≠
        T.vertex penIndex := by
      intro he
      have hv := congrArg Fin.val (T.vertex_injective he)
      omega
    have hdis := hElemOuter hvFirst hPenultimateInBplus hverticesNe
    exact Finset.disjoint_left.mp hdis hfirstAt hetaMissing
  have thetaOldAvoid : theta ∉ Finset.univ.filter (fun c =>
      ∃ r : Fin T.length, A.length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
        phi (T.edge r) = some c) := by
    have hh := (Finset.mem_sdiff.mp
      (C.good.avoidance q eta hetaStored hthetaGamma)).2
    change theta ∉ HierarchySegmentColors H q eta at hh
    unfold HierarchySegmentColors at hh
    dsimp only at hh
    have hend : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    rw [hend] at hh
    exact hh
  have hthetaFirstBound :
      (HierarchyFirstMissingPosition phi T theta).val ≤ A.length :=
    firstBoundByPrefix A hATouter theta hthetaInA
  have hAlphaFirstBound :
      (HierarchyFirstMissingPosition phi T alpha).val ≤ B.length :=
    firstBoundByPrefix B hBTouter alpha alphaBefore
  have hvAlphaBplus : vAlpha ∈ TreeSequenceVertexSet Bplus :=
    TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hvAlpha
  have horderedUnused :
      (theta ∉ TreeMissingColors phi A ∨ alpha ∉ TreeMissingColors phi A) →
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T theta))
          (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        theta ∉ Finset.univ.filter (fun c =>
          ∃ t : Fin T.length, A.length ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition phi T alpha).val ∧
            phi (T.edge t) = some c) := by
    clear * - G T phi A B D hthetaInA hthetaFirstBound hAlphaFirstBound alphaBefore penPosition alpha theta
      firstMissingOuter hATouter hBTouter missingMonoOuter vertexMemOuter thetaOldAvoid
      hetaFirst hBLouter hPLouter
    intro hnot
    rcases hnot with hnotTheta | hnotAlpha
    · exact False.elim (hnotTheta hthetaInA)
    · have hAlphaAfter : A.length <
          (HierarchyFirstMissingPosition phi T alpha).val := by
        by_contra h
        have hle : (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length :=
          Nat.le_of_not_gt h
        have hAlphaMissingT : alpha ∈ TreeMissingColors phi T :=
          missingMonoOuter hBTouter alphaBefore
        have hmiss := firstMissingOuter T alpha hAlphaMissingT
        let i : Fin (A.length + 1) :=
          ⟨(HierarchyFirstMissingPosition phi T alpha).val, by omega⟩
        have hi : Fin.castLE (Nat.succ_le_succ hATouter.1) i =
            HierarchyFirstMissingPosition phi T alpha := Fin.ext rfl
        have hvA : A.vertex i ∈ TreeSequenceVertexSet A := vertexMemOuter A i
        have hsameVertex : A.vertex i = T.vertex
            (HierarchyFirstMissingPosition phi T alpha) := by
          rw [← hATouter.2.1 i, hi]
        have hv : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
            TreeSequenceVertexSet A := hsameVertex ▸ hvA
        exact hnotAlpha (Finset.mem_biUnion.mpr ⟨_, hv, hmiss⟩)
      refine ⟨?_, ?_⟩
      · exact ⟨HierarchyFirstMissingPosition phi T theta,
          HierarchyFirstMissingPosition phi T alpha, rfl, rfl,
          lt_of_le_of_lt hthetaFirstBound hAlphaAfter⟩
      · intro hc
        obtain ⟨_, t, htA, htB, he⟩ := Finset.mem_filter.mp hc
        apply thetaOldAvoid
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA, ?_, he⟩
        rw [hetaFirst]
        have hp := penPosition
        have hlen := hBLouter
        have hfirstAlpha := hAlphaFirstBound
        omega
  have thetaAvoidsSplit : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < Bplus.length → phi (T.edge t) ≠ some theta := by
    intro t ht htb he
    apply thetaOldAvoid
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, ?_, he⟩
    rw [hetaFirst]
    have hp := penPosition
    have hpos := hPLouter
    have hbt := t.isLt
    omega
  have hthetaAlphaNe : theta ≠ alpha := by
    intro he
    have hInc : Incident G (T.vertex endIndex) (T.edge lastIndex) := by
      obtain ⟨i, hi⟩ := T.attaches lastIndex
      have hj : lastIndex.succ = endIndex := by
        apply Fin.ext
        have hl := lastPosition
        have ht := endPosition
        simp only [Fin.val_succ]
        omega
      change _ ∈ G.ends (T.edge lastIndex)
      rw [hi, hj]
      exact Sym2.mem_mk_left _ _
    apply (Finset.mem_sdiff.mp alphaTerminal).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge lastIndex, hInc,
      he ▸ lastColor⟩
  have hstageTheta : theta ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta hetaStored hthetaGamma)).1
  have hThetaTn : H.dividerCount = 0 → theta ∈ TreeMissingColors phi Tn := by
    intro hz
    have hq0 : q = 0 := Fin.ext (by simp [q, hz])
    rw [hq0] at hstageTheta
    simpa [HierarchyStageMissingColors, Tn] using hstageTheta
  have hThetaTnq (hz : 0 < H.dividerCount) :
      theta ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩) := by
    have hq0 : q ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp [q] at hv
      omega
    rcases Fin.eq_zero_or_eq_succ q with hqzero | ⟨i, hqi⟩
    · exact False.elim (hq0 hqzero)
    · rw [hqi] at hstageTheta
      change theta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) at hstageTheta
      have hidx : i.succ.castSucc =
          (⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ : Fin (H.dividerCount + 2)) := by
        apply Fin.ext
        have hqval := congrArg Fin.val hqi
        simp only [q, Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hqval ⊢
        omega
      rw [hidx] at hstageTheta
      exact hstageTheta
  have hChange :
      (0 < H.dividerCount ∧ theta ∈ TreeMissingColors phi
        (H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩)) ∨
      (H.dividerCount = 0 ∧
        (theta ∈ TreeMissingColors phi Tn ∨
          (theta ∈ TreeMissingColors phi A ∧
            theta ∉ TashkinovStoredColors ett.series.data n ∧
            alpha ∉ TashkinovStoredColors ett.series.data n))) := by
    by_cases hz : H.dividerCount = 0
    · right
      exact ⟨hz, Or.inl (hThetaTn hz)⟩
    · left
      exact ⟨Nat.pos_of_ne_zero hz, hThetaTnq (Nat.pos_of_ne_zero hz)⟩
  have hchange := ChangeLemma G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality canonicalElem ctx.largeMissingSet
      theta alpha hthetaAlphaNe canonicalMissing horderedUnused
  have hcomponentEq :
      TwoColorComponent G phi theta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
        TwoColorComponent G phi theta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) := by
    by_cases hz : H.dividerCount = 0
    · exact hchange.2.1 ⟨hz, Or.inl (hThetaTn hz)⟩
    · exact hchange.1 ⟨Nat.pos_of_ne_zero hz,
        Or.inl (hThetaTnq (Nat.pos_of_ne_zero hz))⟩
  have selfComponent (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have leafComponent (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (v : V)
      (hm : a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v) :
      Set.Subsingleton ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)) := by
    as_aux_lemma =>
      clear * - G rho a b hne hp v hm
      have hd : @SimpleGraph.degree _ (TwoColorIncidenceGraph G rho a b)
          (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
        rcases hm with ha | hb
        · exact MissingColorIncidenceEndpoint G rho a b hne hp v ha
        · have he : TwoColorIncidenceGraph G rho a b = TwoColorIncidenceGraph G rho b a := by
            ext x y
            cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
          rw [he]
          exact MissingColorIncidenceEndpoint G rho b a hne.symm hp v hb
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
      intro x hx y hy
      exact Finset.card_le_one_iff.mp hd
        (by simpa [SimpleGraph.mem_neighborFinset] using hx)
        (by simpa [SimpleGraph.mem_neighborFinset] using hy)
  have separateVertices (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    as_aux_lemma =>
      clear * - G rho a b hne hp u v w huv huw hvw hu hv hw hsame
        leafComponent selfComponent
      rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
      · exfalso
        obtain ⟨s, t, p, hpPath, hsupport⟩ :=
          TwoColorComponentSpanningPath G rho a b hp (Sum.inl w)
        have endpoint (x : V) (hx : Sum.inl x ∈ TwoColorComponent G rho a b (Sum.inl w))
            (hm : a ∈ MissingColors G rho x ∨ b ∈ MissingColors G rho x) :
            Sum.inl x = s ∨ Sum.inl x = t := by
          by_contra hn
          push_neg at hn
          have hs : Sum.inl x ∈ p.support := by
            change Sum.inl x ∈ {z | z ∈ p.support}
            rw [hsupport]
            exact hx
          exact hpPath.isTrail.not_mem_support_of_subsingleton_neighborSet
            hn.1 hn.2 (leafComponent rho a b hne hp x hm) hs
        have hue := endpoint u (he ▸ selfComponent rho a b u) (Or.inl hu)
        have hve := endpoint v (by rw [he, hsame]; exact selfComponent rho a b v) (Or.inr hv)
        have hwe := endpoint w (selfComponent rho a b w) hw
        rcases hue with hue | hue <;> rcases hve with hve | hve <;>
          rcases hwe with hwe | hwe
        all_goals first
          | exact huv (Sum.inl.inj (hue.trans hve.symm))
          | exact huw (Sum.inl.inj (hue.trans hwe.symm))
          | exact hvw (Sum.inl.inj (hve.trans hwe.symm))
      · exact hd
  have separateMaybeCoincident (rho : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    as_aux_lemma =>
      clear * - G rho a b hne hp u v w huw hvw hu hv hw hsame
        separateVertices selfComponent
      by_cases huv : u = v
      · subst v
        rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
        · have noColor (c : Fin k) (hc : c ∈ MissingColors G rho u)
              (f : E) (hf : Incident G u f) : rho f ≠ some c := by
            intro hcol
            exact (Finset.mem_sdiff.mp hc).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hcol⟩)
          have hn : (TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl u) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            cases x with
            | inl x => exact hx
            | inr f =>
              rcases hx with ⟨hi, hc⟩
              exact hc.elim (noColor a hu f hi) (noColor b hv f hi)
          have hwIn : Sum.inl w ∈ TwoColorComponent G rho a b (Sum.inl u) :=
            he ▸ selfComponent rho a b w
          change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) =
            (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl u) at hwIn
          exact False.elim (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (fun h => huw (Sum.inl.inj h)) hn
            (SimpleGraph.ConnectedComponent.exact hwIn).symm)
        · exact hd
      · exact separateVertices rho a b hne hp u v w huv huw hvw hu hv hw hsame
  have hAlphaMissingT : alpha ∈ TreeMissingColors phi T :=
    missingMonoOuter (X := B) (Y := T) hBTouter alphaBefore
  have hthetaMissingT : theta ∈ TreeMissingColors phi T :=
    missingMonoOuter (X := A) (Y := T) hATouter hthetaInA
  have hthetaAtFirst : theta ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) :=
    firstMissingOuter T theta hthetaMissingT
  have hAlphaAtFirst : alpha ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T alpha)) :=
    firstMissingOuter T alpha hAlphaMissingT
  have hthetaTerminalNe : T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
      T.vertex endIndex := by
    intro he
    have hv := congrArg Fin.val (T.vertex_injective he)
    have ht := endPosition
    have hlen := hellOuter
    have htail := hTailAtLeast
    have hbound := hthetaFirstBound
    clear * - hv ht hlen htail hbound
    omega
  have hAlphaTerminalNe : T.vertex (HierarchyFirstMissingPosition phi T alpha) ≠
      T.vertex endIndex := by
    intro he
    have hv := congrArg Fin.val (T.vertex_injective he)
    have ht := endPosition
    have hlen := hBLouter
    have hbound := hAlphaFirstBound
    clear * - hv ht hlen hbound
    omega
  have hdisjointComponent := separateMaybeCoincident phi theta alpha
      hthetaAlphaNe ctx.proper
      (T.vertex (HierarchyFirstMissingPosition phi T theta))
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex endIndex)
      hthetaTerminalNe hAlphaTerminalNe hthetaAtFirst hAlphaAtFirst
      (Or.inr alphaTerminal) hcomponentEq
  let z : Sum V E := Sum.inl (T.vertex endIndex)
  have hpath : TwoColorPathComponent G phi theta alpha z :=
    ⟨hthetaAlphaNe, _, selfComponent phi theta alpha _,
      leafComponent phi theta alpha hthetaAlphaNe ctx.proper _
        (Or.inr alphaTerminal)⟩
  let muOne := TwoColorComponentSwap G phi theta alpha z
  have behaviorOne :
      (∀ v : V, Sum.inl v ∉ TwoColorComponent G phi theta alpha z →
        MissingColors G muOne v = MissingColors G phi v) ∧
      (∀ v : V, Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
        theta ∈ MissingColors G phi v → alpha ∈ MissingColors G muOne v) ∧
      (∀ v : V, Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
        alpha ∈ MissingColors G phi v → theta ∈ MissingColors G muOne v) ∧
      (∀ v : V, ∀ c : Fin k, c ≠ theta → c ≠ alpha →
        (c ∈ MissingColors G muOne v ↔ c ∈ MissingColors G phi v)) := by
    exact TwoColorComponentSwapMissingBehavior G phi theta alpha
      hthetaAlphaNe ctx.proper z
  have prefixMissing (z : Sum V E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet Bplus) (hvB : v ∈ TreeSequenceVertexSet Bplus)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet Bplus,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    as_aux_lemma =>
      clear * - G rho a b hne hp helem u v huB hvB hu hv hdu hdv Bplus z
      have behavior := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
      intro w hwB
      by_cases hw : Sum.inl w ∈ TwoColorComponent G rho a b z
      · have hwa : a ∉ MissingColors G rho w := by
          intro hm
          have hwu : w ≠ u := fun he => hdu (he ▸ hw)
          exact Finset.disjoint_left.mp (helem hwB huB hwu) hm hu
        have hwb : b ∉ MissingColors G rho w := by
          intro hm
          have hwv : w ≠ v := fun he => hdv (he ▸ hw)
          exact Finset.disjoint_left.mp (helem hwB hvB hwv) hm hv
        have presentSwapped (c d : Fin k)
            (hd : d ∉ MissingColors G rho w)
            (hdab : (d = a ∧ c = b) ∨ (d = b ∧ c = a)) :
            c ∉ MissingColors G (TwoColorComponentSwap G rho a b z) w := by
          have hpres : d ∈ PresentColors G rho w := by simpa [MissingColors] using hd
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpres
          rcases hpres with ⟨e, hwe, he⟩
          have hadj : (TwoColorIncidenceGraph G rho a b).Adj (Sum.inr e) (Sum.inl w) := by
            simp only [TwoColorIncidenceGraph]
            exact ⟨hwe, hdab.elim (fun h => Or.inl (he.trans (congrArg some h.1)))
              (fun h => Or.inr (he.trans (congrArg some h.1)))⟩
          have heC : Sum.inr e ∈ TwoColorComponent G rho a b z := by
            change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) = _ at hw
            change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inr e) = _
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hw
          have heSwap : TwoColorComponentSwap G rho a b z e = some c := by
            rcases hdab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp [TwoColorComponentSwap, heC, he]
            · simp [TwoColorComponentSwap, heC, he, hne]
          have hpresent : c ∈ PresentColors G (TwoColorComponentSwap G rho a b z) w := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hwe, heSwap⟩
          simpa [MissingColors] using hpresent
        have hnewa := presentSwapped a b hwb (Or.inr ⟨rfl, rfl⟩)
        have hnewb := presentSwapped b a hwa (Or.inl ⟨rfl, rfl⟩)
        apply Finset.ext
        intro c
        by_cases hca : c = a
        · subst c
          simp only [Finset.mem_coe, hnewa, hwa]
        · by_cases hcb : c = b
          · subst c
            simp only [Finset.mem_coe, hnewb, hwb]
          · exact behavior.2.2.2 w c hca hcb
      · exact behavior.1 w hw
  have hThetaFirstBplus :
      T.vertex (HierarchyFirstMissingPosition phi T theta) ∈
        TreeSequenceVertexSet Bplus := by
    let i : Fin (T.length + 1) := HierarchyFirstMissingPosition phi T theta
    have hi : i.val ≤ Bplus.length := le_trans hthetaFirstBound hABplusouter.1
    let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
    have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩
  have hAlphaFirstBplus :
      T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
        TreeSequenceVertexSet Bplus := by
    let i : Fin (T.length + 1) := HierarchyFirstMissingPosition phi T alpha
    have hi : i.val ≤ Bplus.length := le_trans hAlphaFirstBound
      (by omega)
    let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
    have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩
  have huOutsideOne : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta)) ∉
      TwoColorComponent G phi theta alpha z := by
    intro hh
    exact Set.disjoint_left.mp hdisjointComponent hh
      (selfComponent phi theta alpha
        (T.vertex (HierarchyFirstMissingPosition phi T theta)))
  have hvOutsideOne : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∉
      TwoColorComponent G phi theta alpha z := by
    intro hh
    have hhTheta : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∈
        TwoColorComponent G phi theta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) := by
      rw [hcomponentEq]
      exact selfComponent phi theta alpha
        (T.vertex (HierarchyFirstMissingPosition phi T alpha))
    exact Set.disjoint_left.mp hdisjointComponent hh hhTheta
  have hmissingOne : ∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G muOne v = MissingColors G phi v :=
    prefixMissing z phi theta alpha hthetaAlphaNe ctx.proper hElemOuter
      (T.vertex (HierarchyFirstMissingPosition phi T theta))
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      hThetaFirstBplus hAlphaFirstBplus hthetaAtFirst hAlphaAtFirst
      huOutsideOne hvOutsideOne
  have hmissingPointwise (v : V) (hv : v ∈ TreeSequenceVertexSet Bplus) :
      MissingColors G muOne v = MissingColors G phi v := by
    as_aux_lemma =>
      clear_value muOne
      clear * - hmissingOne hv
      exact hmissingOne v hv
  have htreeMissingEq : TreeMissingColors muOne Bplus = TreeMissingColors phi Bplus := by
    as_aux_lemma =>
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl hmissingPointwise
  have hstableOne := StableChangeCasesOneTwo G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality canonicalElem ctx.largeMissingSet
      theta alpha hthetaAlphaNe canonicalMissing
      z hpath muOne rfl hChange hdisjointComponent
  have hfixedCoreOne : ∀ t : Fin A.length,
      muOne (A.edge t) = phi (A.edge t) := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hw := hstableOne.1
      have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) = 0 := Fin.ext hz
      rw [hi] at hw
      change (if ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi muOne
        else StableColoring Tn
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi muOne) at hw
      have hcore := P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base muOne
        ctx.oneEdgeUncolored hstableOne.2.1.2.1 hw
      have hAzero : A = base.core := by
        change HierarchyStarredStage H q = base.core
        rw [hq]
        rfl
      rw [hAzero]
      exact hcore
    · have hq : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp only [q, Fin.val_last, Fin.val_succ, Fin.val_mk]
        omega
      have hw := hstableOne.1
      have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
          (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := hq
      rw [hi] at hw
      intro t
      have hAstage : A = H.stage
          (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ.castSucc := by
        change HierarchyStarredStage H _ = _
        rw [hq]
        rfl
      by_cases ht : 1 ≤ t.val
      · have hinv := (hAstage ▸ hw.2.1) t ht
        exact hinv
      · have ht0 : t.val = 0 := by omega
        have he : A.edge t = e0 := by
          rw [show t = ⟨0, A.positive⟩ from Fin.ext ht0]
          exact A.first_edge
        rw [he, hstableOne.2.1.2.1.1, ctx.oneEdgeUncolored.1]
  have hfixedSplit : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < Bplus.length → muOne (T.edge t) = phi (T.edge t) := by
    intro t ht htb
    simp [muOne, TwoColorComponentSwap, alphaUnused t ht,
      thetaAvoidsSplit t ht htb]
  have hlastIncident : Incident G (T.vertex endIndex)
      (T.edge lastIndex) := by
    obtain ⟨i, hi⟩ := T.attaches lastIndex
    have hj : lastIndex.succ = endIndex := by
      apply Fin.ext
      have hl := lastPosition
      have ht := endPosition
      simp only [Fin.val_succ]
      omega
    change _ ∈ G.ends (T.edge lastIndex)
    rw [hi, hj]
    exact Sym2.mem_mk_left _ _
  have hlastEdgeInOne : Sum.inr (T.edge lastIndex) ∈
      TwoColorComponent G phi theta alpha z := by
    have hadj : (TwoColorIncidenceGraph G phi theta alpha).Adj
        (Sum.inr (T.edge lastIndex)) z := by
      exact ⟨hlastIncident, Or.inl lastColor⟩
    change (TwoColorIncidenceGraph G phi theta alpha).connectedComponentMk
      (Sum.inr (T.edge lastIndex)) = _
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hlastOne : muOne (T.edge lastIndex) = some alpha := by
    simp [muOne, TwoColorComponentSwap, hlastEdgeInOne, lastColor,
      hthetaAlphaNe.symm]
  have hthetaTerminalOne : theta ∈ MissingColors G muOne
      (T.vertex endIndex) := by
    exact behaviorOne.2.2.1 _ (selfComponent phi theta alpha
      (T.vertex endIndex)) alphaTerminal
  have hetaPenultimateOne : eta ∈ MissingColors G muOne
      (T.vertex penIndex) := by
    rw [hmissingOne _ hPenultimateInBplus]
    exact hetaMissing
  have segTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) : TreeSequenceInitialSegment X Z := by
    refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have stageSegment (a d : ℕ) (hb : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    as_aux_lemma =>
      clear * - H a d hb segTrans
      induction d with
      | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      | succ d ih =>
          exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ := by
    have hq : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp only [q, Fin.val_last, Fin.val_succ, Fin.val_mk]
      omega
    change HierarchyStarredStage H q = H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩
    rw [hq]
    change H.stage
      ((⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ.castSucc) = _
    apply congrArg H.stage
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]
    omega
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have hTnBplus : TreeSequenceInitialSegment Tn Bplus := by
    have hsourceT : TreeSequenceInitialSegment Tn T := ett.abovePenultimate
    have hlen : Tn.length ≤ Bplus.length := by
      have hs : Tn.length < T.length := by
        have hi : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
          Fin.ext rfl
        simpa [Tn, n, hi] using ett.strictAbovePenultimate
      have hp := hPLouter
      clear * - hs hp
      omega
    exact ⟨hlen,
      fun i => (hBplusTouter.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
        (hsourceT.2.1 i),
      fun i => (hBplusTouter.2.2 (Fin.castLE hlen i)).symm.trans (hsourceT.2.2 i)⟩
  have hfixedBplusAux (aLen : Nat) (haLen : aLen = A.length)
      (hcut : ∀ t : Fin Bplus.length, t.val < aLen ∨ aLen ≤ t.val) :
      ∀ t : Fin Bplus.length, muOne (Bplus.edge t) = phi (Bplus.edge t) := by
    as_aux_lemma =>
      intro t
      have left (ha : t.val < aLen) :
          muOne (Bplus.edge t) = phi (Bplus.edge t) := by
        let ta0 : Fin aLen := ⟨t.val, ha⟩
        let ta : Fin A.length := Fin.cast haLen ta0
        have he : Fin.castLE hABplusouter.1 ta = t := Fin.ext (by simp [ta, ta0])
        have heEdge : Bplus.edge t = A.edge ta := by
          calc
            Bplus.edge t = Bplus.edge (Fin.castLE hABplusouter.1 ta) := by rw [he]
            _ = A.edge ta := hABplusouter.2.2 ta
        rw [heEdge]
        exact hfixedCoreOne ta
      have right (ha : aLen ≤ t.val) :
          muOne (Bplus.edge t) = phi (Bplus.edge t) := by
        let tt : Fin T.length := Fin.castLE hBplusTouter.1 t
        have he : Bplus.edge t = T.edge tt := (hBplusTouter.2.2 t).symm
        rw [he]
        apply hfixedSplit tt
        · have hh : A.length ≤ t.val := by rw [← haLen]; exact ha
          exact hh
        · have hval : tt.val = t.val := by simp [tt]
          rw [hval]
          exact t.isLt
      exact (hcut t).elim left right
  have hfixedBplus := hfixedBplusAux A.length rfl
    (fun t => Nat.lt_or_ge t.val A.length)
  have hBplusLength : Bplus.length = B.length + 1 := by
    have hp := hPLouter
    have hb := hBLouter
    apply Nat.succ.inj
    change Bplus.length + 1 = (B.length + 1) + 1
    calc
      Bplus.length + 1 = T.length := hp
      _ = B.length + 2 := hb.symm
      _ = (B.length + 1) + 1 := by rfl
  have transportOne (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S Bplus) :
      TashkinovAugmentationSequence muOne S Bplus := by
    refine TashkinovAugmentationSequenceColoringTransport phi muOne S B Bplus hseq
      hBBplusOuter hBplusLength ?_ ?_
    · intro t _
      exact hfixedBplus t
    · intro v hv
      exact hmissingOne v (TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hv)
  have hrouteOne :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muOne Tn Bplus) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence muOne seed Bplus) := by
    rcases oldRoute with ⟨hp, hseq⟩ |
      ⟨hnp', f, seed, hconnecting, hadjoin, _, _, hseq⟩
    · have hsourceB := hTnBplus
      exact Or.inl ⟨hp, transportOne Tn
        (TashkinovAugmentationSequenceRestrict phi Tn Bplus T hseq hsourceB hBplusTouter)⟩
    · have hseedT : TreeSequenceInitialSegment seed T :=
        TashkinovAugmentationSequenceInitialSegment phi seed T hseq
      have hnp : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
        intro hpe
        rcases hnp' with hse | hre
        · rw [hpe] at hse
          cases hse
        · rw [hpe] at hre
          cases hre
      have hTnA : TreeSequenceInitialSegment Tn A := by
        have hcoreTn : base.core = Tn := by
          simpa [Tn, n] using base.nonparallel hnp
        have hTnCore : TreeSequenceInitialSegment Tn base.core := by
          rw [hcoreTn]
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        exact segTrans hTnCore coreToA
      have hseedLen : seed.length ≤ Bplus.length := by
        have hadjLen := hadjoin.1
        change seed.length = Tn.length + 1 at hadjLen
        have ha := hTnA.1
        have htail := hTailAtLeast
        have hp := hPLouter
        have hell := hellOuter
        have hAlen := hABplusouter.1
        clear * - hadjLen ha htail hp hell hAlen
        omega
      have hseedB : TreeSequenceInitialSegment seed Bplus := by
        refine ⟨hseedLen, ?_, ?_⟩
        · intro i
          exact (hBplusTouter.2.1 (Fin.castLE (Nat.succ_le_succ hseedLen) i)).symm.trans
            (hseedT.2.1 i)
        · intro i
          exact (hBplusTouter.2.2 (Fin.castLE hseedLen i)).symm.trans (hseedT.2.2 i)
      exact Or.inr ⟨hnp', f, seed, hconnecting, hadjoin,
        transportOne seed
          (TashkinovAugmentationSequenceRestrict phi seed Bplus T hseq hseedB hBplusTouter)⟩
  have firstWitness (rho : PartialEdgeColoring E k) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho Bplus) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        (HierarchyFirstMissingPosition rho T c).val ≤ Bplus.length := by
    as_aux_lemma =>
      clear * - G T rho Bplus hBplusTouter c hc
      obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨i, rfl⟩ := hv
      let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
        c ∈ MissingColors G rho (T.vertex j)
      have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hBplusTouter.2.1 i]
        exact hvc
      have hn : candidates.Nonempty := ⟨_, hi⟩
      have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      have hle := Finset.min'_le candidates _ hi
      unfold HierarchyFirstMissingPosition
      change (c ∈ MissingColors G rho (T.vertex (if h : candidates.Nonempty then
        candidates.min' h else Fin.last T.length))) ∧ _
      rw [dif_pos hn]
      refine ⟨hm, ?_⟩
      change (candidates.min' hn).val ≤ Bplus.length
      change (candidates.min' hn).val ≤ i.val at hle
      have hib := i.isLt
      omega
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho Bplus) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    as_aux_lemma =>
      clear * - G T Bplus rho sigma c helem hmiss hc firstWitness hBplusTouter
      have hr := firstWitness rho c hc
      have hc' : c ∈ TreeMissingColors sigma Bplus := by
        obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
        exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
      have hs := firstWitness sigma c hc'
      have pref (i : Fin (T.length + 1)) (hi : i.val ≤ Bplus.length) :
          T.vertex i ∈ TreeSequenceVertexSet Bplus := by
        let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
        have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
        exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩
      by_contra hne
      have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
          T.vertex (HierarchyFirstMissingPosition rho T c) :=
        fun he => hne (T.vertex_injective he)
      have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
      exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1
  have firstFromMembership (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (hc : ∀ v, c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G rho v) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    as_aux_lemma =>
      clear * - G T rho sigma c hc
      have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
          c ∈ MissingColors G sigma (T.vertex i)) =
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            c ∈ MissingColors G rho (T.vertex i)) := by
        apply Finset.filter_congr
        intro i _
        exact hc _
      unfold HierarchyFirstMissingPosition
      rw [he]
  have hstoredFirst : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
    intro c hc
    have hct : c ≠ theta := by
      intro he
      have hs : theta ∈ HierarchyStoredColorsAt H q := he ▸ hc
      exact (Finset.mem_sdiff.mp hs).2 hthetaInA
    by_cases hca : c = alpha
    · exact hca.symm ▸ firstPreserved phi muOne alpha hElemOuter hmissingPointwise hAlphaMissingBplus
    · exact firstFromMembership phi muOne c (fun v => behaviorOne.2.2.2 v c hct hca)
  have hAlphaNoGamma : alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
    rcases D.normalizedAlternative with ⟨_, _, hnot⟩ | ⟨_, _, hnot⟩ | ⟨haStored, _⟩
    · exact hnot
    · exact hnot
    · intro hm
      exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 hm haStored
  have hthetaOwner : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      theta ∈ C.good.gamma q c → c = eta := by
    intro c hc hct
    by_contra hne
    exact Finset.disjoint_left.mp (C.good.disjointPairs q c eta hc hetaStored hne)
      hct hthetaGamma
  have hgammaCutoff : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      (alpha ∈ C.good.gamma q c ∨ theta ∈ C.good.gamma q c) →
        (HierarchyFirstMissingPosition phi T c).val ≤ Bplus.length := by
    intro c hc hp
    rcases hp with ha | ht
    · exact False.elim (hAlphaNoGamma (Finset.mem_biUnion.mpr ⟨c, hc, ha⟩))
    · have he := hthetaOwner c hc ht
      rw [he, hetaFirst]
      have hp := penPosition
      have hb := hPLouter
      omega
  have hmissingPairOne :
      theta ∈ TreeMissingColors muOne Bplus ∧
        alpha ∈ TreeMissingColors muOne Bplus := by
    exact htreeMissingEq.symm ▸ ⟨hthetaMissingBplus, hAlphaMissingBplus⟩
  have hsuffixPhi : TashkinovAugmentationSequence phi Bplus T := by
    apply Relation.ReflTransGen.single
    refine ⟨hPLouter.symm, hBplusTouter, theta, ?_, hthetaMissingBplus⟩
    have hi : Fin.cast hPLouter (Fin.last Bplus.length) = lastIndex :=
      Fin.ext (by
        have hl := lastPosition
        simp only [Fin.val_cast, Fin.val_last]
        clear * - hl hPLouter
        omega)
    rw [hi]
    exact lastColor
  obtain ⟨_, _, corrOne, maxOne, baseOne, KOne, goodOne, sameOne⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 input T phi ett base C ctx
      theta alpha hthetaAlphaNe canonicalMissing
      z hpath muOne rfl hChange hdisjointComponent
      Bplus hABplusouter (by
        change A.length < Bplus.length
        have htail := hTailAtLeast
        have hp := hPLouter
        have hell := hellOuter
        clear * - htail hp hell
        omega)
      (by rw [← hBplusDef]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      hfixedSplit hrouteOne hsuffixPhi hmissingPairOne
      (by rw [← hBplusDef]; exact hmissingPointwise)
      hstoredFirst (fun c hc hp => hgammaCutoff c hc hp.symm)
  obtain ⟨COne, sameOne⟩ : ∃ COne : HierarchyCounterexample baseOne,
      SameGoodHierarchy C.good COne.good := by
    refine ⟨{
      positive := by rw [corrOne.rungAgreement]; exact C.positive
      hierarchy := KOne
      good := goodOne
      maximum := maxOne
      notElementary := ?_ }, sameOne⟩
    intro he
    exact Finset.disjoint_left.mp
      (he (vertexMemOuter T (HierarchyFirstMissingPosition phi T theta))
        (vertexMemOuter T endIndex) hthetaTerminalNe)
      ((hmissingPointwise _ hThetaFirstBplus).symm ▸ hthetaAtFirst) hthetaTerminalOne
  obtain ⟨ctxOne⟩ := P2752_T2_MinimumContextTransport G k e0 input T phi muOne
    ett base C ctx corrOne baseOne COne sameOne
  let POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := muOne
    corresponding := corrOne
    maximum := maxOne
    replacementBase := baseOne
    counterexample := COne
    sameGood := sameOne
    minimumContext := ctxOne }
  let HOne := COne.hierarchy
  let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
  have starOne : HierarchyStarredStage HOne qOne = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy COne.hierarchy sameOne.1).1.symm
  have countOne : H.dividerCount = HOne.dividerCount := sameOne.2.choose
  have prefixOne : HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1) =
      Bplus := by
    unfold HierarchyFullTailPrefix HierarchyFullTailLength
    change TreeSequencePrefix T
      (min ((HierarchyStarredStage HOne qOne).length +
        (T.length - (HierarchyStarredStage HOne qOne).length - 1)) T.length) _ _ = Bplus
    simp only [starOne]
    exact hBplusDef.symm
  have elemOne : ColoredVertexSetElementary G muOne (TreeSequenceVertexSet Bplus) := by
    intro u hu v hv hne
    rw [hmissingPointwise u hu, hmissingPointwise v hv]
    exact hElemOuter hu hv hne
  have missingPrefixOne : ∀ X : TreeSequence G e0,
      TreeSequenceInitialSegment X Bplus → TreeMissingColors muOne X = TreeMissingColors phi X := by
    intro X hX
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      hmissingPointwise v (TreeSequenceInitialSegmentVertexSetSubset hX hv))
  have firstThetaOne : HierarchyFirstMissingPosition muOne T theta =
      HierarchyFirstMissingPosition phi T theta := firstPreserved phi muOne theta hElemOuter hmissingPointwise hthetaMissingBplus
  have firstEtaOne : HierarchyFirstMissingPosition muOne T eta =
      penIndex :=
    (firstPreserved phi muOne eta hElemOuter hmissingPointwise (Finset.mem_biUnion.mpr ⟨_, hPenultimateInBplus, hetaMissing⟩)).trans hetaFirst
  have thetaFirstOne : theta ∈ MissingColors G muOne
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) := by
    rw [hmissingPointwise _ hThetaFirstBplus]
    exact hthetaAtFirst
  have thetaEtaNe : theta ≠ eta := by
    intro he
    exact hetaNotA (he ▸ hthetaInA)
  have thetaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      muOne (T.edge t) ≠ some theta := by
    intro t ht
    by_cases hb : t.val < Bplus.length
    · rw [hfixedSplit t ht hb]
      exact thetaAvoidsSplit t ht hb
    · have he : t = lastIndex := by
        apply Fin.ext
        have hl := lastPosition
        have hp := hPLouter
        have htlt := t.isLt
        clear * - hl hp htlt hb
        omega
      rw [he, hlastOne]
      exact fun h => hthetaAlphaNe (Option.some.inj h).symm
  have sameLastOne : HierarchyStoredColorsAt H q = HierarchyStoredColorsAt HOne qOne ∧
      ∀ c ∈ HierarchyStoredColorsAt H q, C.good.gamma q c = COne.good.gamma qOne c := by
    obtain ⟨hc, hd⟩ := sameOne.2
    have hi : Fin.cast (congrArg (fun d => d + 1) hc) q = qOne :=
      Fin.ext hc
    simpa only [hi] using hd q
  have thetaStoredOne : theta ∉ HierarchyStoredColorsAt HOne qOne := by
    rw [← sameLastOne.1]
    exact fun hm => (Finset.mem_sdiff.mp hm).2 hthetaInA
  have etaStoredOne : eta ∈ HierarchyStoredColorsAt HOne qOne :=
    sameLastOne.1 ▸ hetaStored
  have etaGammaOne : theta ∈ COne.good.gamma qOne eta :=
    sameLastOne.2 eta hetaStored ▸ hthetaGamma
  have tnOne :
      corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc = Tn := by
    have hs : H.stage 0 = HOne.stage 0 := by
      have hs :=
        (Fin.heq_fun_iff (congrArg (fun d => d + 2) countOne)).mp sameOne.1.2.2.1 0
      exact hs.trans (congrArg HOne.stage (Fin.ext (by simp)))
    exact HOne.baseStage.symm.trans (hs.symm.trans H.baseStage)
  have thetaTnOne (hz : HOne.dividerCount = 0) :
      theta ∈ TreeMissingColors muOne
        (corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc) := by
    rw [tnOne, missingPrefixOne Tn hTnBplus]
    exact hThetaTn (countOne.trans hz)
  have positiveStarOne (hz : HOne.dividerCount ≠ 0) :
      HOne.stage ⟨HOne.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ = A := by
    have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ :=
      Fin.ext (by simp only [qOne, Fin.val_last, Fin.val_succ, Fin.val_mk]; omega)
    have hs := starOne
    rw [hi] at hs
    change HOne.stage _ = A at hs
    convert hs using 1
    apply congrArg HOne.stage
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]
    omega
  have caseTwo :
      (0 < HOne.dividerCount ∧ theta ∈ TreeMissingColors muOne
        (HOne.stage ⟨HOne.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩)) ∨
      (HOne.dividerCount = 0 ∧
        (theta ∈ TreeMissingColors muOne
          (corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc) ∨
          (theta ∈ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∧
            theta ∉ TashkinovStoredColors corrOne.replacementETT.series.data
              (Fin.last corrOne.replacementETT.rounds) ∧
            eta ∉ TashkinovStoredColors corrOne.replacementETT.series.data
              (Fin.last corrOne.replacementETT.rounds)))) := by
    by_cases hz : HOne.dividerCount = 0
    · exact Or.inr ⟨hz, Or.inl (thetaTnOne hz)⟩
    · exact Or.inl ⟨Nat.pos_of_ne_zero hz, by
        rw [positiveStarOne hz, missingPrefixOne A hABplusouter]
        exact hthetaInA⟩
  have etaMissingPrefixOne : eta ∈ TreeMissingColors muOne Bplus :=
    Finset.mem_biUnion.mpr ⟨_, hPenultimateInBplus, hetaPenultimateOne⟩
  have thetaMissingPrefixOne : theta ∈ TreeMissingColors muOne Bplus := hmissingPairOne.1
  have orderedTwo :
      (theta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∨
        eta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne)) →
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition muOne T theta))
        (T.vertex (HierarchyFirstMissingPosition muOne T eta)) ∧
      theta ∉ Finset.univ.filter (fun c =>
        ∃ t : Fin T.length, (HierarchyStarredStage HOne qOne).length ≤ t.val ∧
          t.val < (HierarchyFirstMissingPosition muOne T eta).val ∧
          muOne (T.edge t) = some c) := by
    intro _
    rw [firstThetaOne, firstEtaOne, starOne]
    refine ⟨⟨_, _, rfl, rfl, ?_⟩, ?_⟩
    · have hb := hthetaFirstBound
      have hp := penPosition
      have hl := hTailAtLeast
      have hell := hellOuter
      clear * - hb hp hl hell
      omega
    · intro hc
      obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
      exact thetaUnusedOne t ht he
  have changeTwo := ChangeLemma G k e0 corrOne.replacementInput T muOne
    corrOne.replacementETT baseOne COne ctxOne.proper ctxOne.oneEdgeUncolored
    ctxOne.lowerRung ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G muOne (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)))
      rw [prefixOne]; exact elemOne) ctxOne.largeMissingSet
    theta eta thetaEtaNe (by
      change theta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)) ∧
        eta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1))
      rw [prefixOne]
      exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩) orderedTwo
  have componentEqTwo :
      TwoColorComponent G muOne theta eta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
      TwoColorComponent G muOne theta eta (Sum.inl (T.vertex penIndex)) := by
    rw [← firstThetaOne, ← firstEtaOne]
    by_cases hz : HOne.dividerCount = 0
    · exact changeTwo.2.1 ⟨hz, Or.inl (thetaTnOne hz)⟩
    · exact changeTwo.1 ⟨Nat.pos_of_ne_zero hz, Or.inl (by
        rw [positiveStarOne hz, missingPrefixOne A hABplusouter]
        exact hthetaInA)⟩
  have thetaPenultimateNe : T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
      T.vertex penIndex := by
    intro he
    have hv := congrArg Fin.val (T.vertex_injective he)
    have hb := hthetaFirstBound
    have hp := penPosition
    have ht := hTailAtLeast
    have hell := hellOuter
    clear * - hv hb hp ht hell
    omega
  have penultimateTerminalNe : T.vertex penIndex ≠
      T.vertex endIndex := by
    intro he
    have hv := congrArg Fin.val (T.vertex_injective he)
    have hp := penPosition
    have ht := endPosition
    clear * - hv hp ht
    omega
  have disjointTwo := separateVertices muOne theta eta thetaEtaNe ctxOne.proper
    (T.vertex (HierarchyFirstMissingPosition phi T theta))
    (T.vertex penIndex) (T.vertex endIndex)
    thetaPenultimateNe hthetaTerminalNe penultimateTerminalNe
    thetaFirstOne hetaPenultimateOne (Or.inl hthetaTerminalOne) componentEqTwo
  let muTwo := TwoColorComponentSwap G muOne theta eta z
  have pathTwo : TwoColorPathComponent G muOne theta eta z :=
    ⟨thetaEtaNe, _, selfComponent muOne theta eta _,
      leafComponent muOne theta eta thetaEtaNe ctxOne.proper _ (Or.inl hthetaTerminalOne)⟩
  have thetaOutsideTwo : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta)) ∉
      TwoColorComponent G muOne theta eta z := by
    intro hm
    exact Set.disjoint_left.mp disjointTwo hm (selfComponent muOne theta eta _)
  have etaOutsideTwo : Sum.inl (T.vertex penIndex) ∉
      TwoColorComponent G muOne theta eta z := by
    intro hm
    apply Set.disjoint_left.mp disjointTwo hm
    rw [componentEqTwo]
    exact selfComponent muOne theta eta _
  have missingTwo : ∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G muTwo v = MissingColors G muOne v :=
    prefixMissing z muOne theta eta thetaEtaNe ctxOne.proper elemOne
      _ _ hThetaFirstBplus hPenultimateInBplus thetaFirstOne hetaPenultimateOne
      thetaOutsideTwo etaOutsideTwo
  have stableTwo := StableChangeCasesOneTwo G k e0 corrOne.replacementInput T muOne
    corrOne.replacementETT baseOne COne ctxOne.proper ctxOne.oneEdgeUncolored
    ctxOne.lowerRung ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G muOne (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)))
      rw [prefixOne]; exact elemOne) ctxOne.largeMissingSet
    theta eta thetaEtaNe (by
      change theta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)) ∧
        eta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1))
      rw [prefixOne]; exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩)
    z pathTwo muTwo rfl caseTwo (by
      dsimp only
      rw [firstThetaOne]
      exact disjointTwo)
  have exclusionEta := HierarchyTailMissingColorExclusion G k e0 input T phi ett base H canonicalElem
    (ell - 1) (by clear * - hTailAtLeast; omega)
    (by change ell - 1 < ell; clear * - hTailAtLeast; omega) eta (by
      have hv : Bplus.vertex (Fin.last Bplus.length) = T.vertex penIndex := by
        rw [← hBplusTouter.2.1 (Fin.last Bplus.length)]
        apply congrArg T.vertex
        apply Fin.ext
        have hp := penPosition
        have hb := hPLouter
        simp only [Fin.val_castLE, Fin.val_last]
        clear * - hp hb
        omega
      have hm : eta ∈ MissingColors G phi (Bplus.vertex (Fin.last Bplus.length)) := hv.symm ▸ hetaMissing
      subst Bplus
      exact hm)
  have exclusionEta' : ∀ t : Fin Bplus.length, A.length ≤ t.val →
      t.val < A.length + (ell - 1) → phi (Bplus.edge t) = some eta →
      H.dividerCount = 0 ∧ base.core = Tn ∧ t.val = A.length ∧
        ∃ f : E, TashkinovSeriesStep G k ett.rounds e0 input ett.series.data n ∧
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ett.series.data.connectingEdges n = {f} ∧ Bplus.edge t = f ∧
          phi f = some eta ∧ eta ∈ TashkinovStoredColors ett.series.data n := by
    subst Bplus
    exact exclusionEta
  have fixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val →
      muTwo (T.edge t) = muOne (T.edge t) := by
    intro t ht
    have hnt := thetaUnusedOne t ht
    by_cases heta : muOne (T.edge t) = some eta
    · have hb : t.val < Bplus.length := by
        by_contra hnot
        have he : t = lastIndex := by
          apply Fin.ext
          have hl := lastPosition
          have hp := hPLouter
          have htlt := t.isLt
          clear * - hl hp htlt hnot
          omega
        rw [he, hlastOne] at heta
        exact hAlphaEtaNe (Option.some.inj heta)
      let tB : Fin Bplus.length := ⟨t.val, hb⟩
      have hcast : Fin.castLE hBplusTouter.1 tB = t := Fin.ext rfl
      have heOld : phi (Bplus.edge tB) = some eta := by
        rw [← hBplusTouter.2.2 tB, hcast, ← hfixedSplit t ht hb]
        exact heta
      obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
        exclusionEta' tB ht (by
          change tB.val < A.length + (ell - 1)
          have hv := tB.isLt
          have hp := hPLouter
          have hell := hellOuter
          clear * - hv hp hell
          change tB.val < Bplus.length at hv
          omega) heOld
      have hzOne : HOne.dividerCount = 0 := countOne.symm.trans hz
      have htn : corrOne.replacementETT.series.data.tree
          (Fin.last corrOne.replacementETT.rounds).castSucc = A :=
        tnOne.trans ((lastZero hz).trans hcore).symm
      have hinc : TreeIncidentEdge
          (corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc)
          (T.edge t) := by
        rw [htn]
        obtain ⟨i, hi⟩ := T.attaches t
        let j : Fin (A.length + 1) := ⟨i.val, by have := i.isLt; change t.val = A.length at hpos; omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hATouter.1) j =
            Fin.castLE (by omega : t.val + 1 ≤ T.length + 1) i := Fin.ext rfl
        refine ⟨A.vertex j, vertexMemOuter A j, ?_⟩
        rw [← hATouter.2.1 j, he, Incident, hi]
        exact Sym2.mem_mk_right _ _
      have hsOne : eta ∈ TashkinovStoredColors corrOne.replacementETT.series.data
          (Fin.last corrOne.replacementETT.rounds) := by
        rw [P2752_T2_TerminalStoredColors ett corrOne]
        exact hs
      have hw := stableTwo.1
      have hi : (Fin.last HOne.dividerCount : Fin (HOne.dividerCount + 1)) = 0 :=
        Fin.ext hzOne
      rw [hi] at hw
      change (if corrOne.replacementETT.series.data.kind (Fin.last corrOne.replacementETT.rounds) =
        some TashkinovExtensionKind.PE then _ else _) at hw
      have stableSeed : StableColoring
          (corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc)
          (TashkinovStoredColors corrOne.replacementETT.series.data (Fin.last corrOne.replacementETT.rounds))
          muOne muTwo := by
        split_ifs at hw with hp
        · exact hw.1
        · exact hw
      exact stableSeed.1 _ hinc ⟨eta, Finset.mem_union_right _ hsOne, heta⟩
    · simp only [muTwo, TwoColorComponentSwap, hnt, heta, if_false, ite_self]
  have behaviorTwo := TwoColorComponentSwapMissingBehavior G muOne theta eta thetaEtaNe ctxOne.proper z
  have storedFirstTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition muOne T c := by
    intro c hc
    have hct : c ≠ theta := fun he => thetaStoredOne (he ▸ hc)
    by_cases hce : c = eta
    · exact hce.symm ▸ firstPreserved muOne muTwo eta elemOne missingTwo etaMissingPrefixOne
    · exact firstFromMembership muOne muTwo c (fun v => behaviorTwo.2.2.2 v c hct hce)
  obtain ⟨corrTwo, maxTwo, baseTwo, KTwo, goodTwo, sameTwo⟩ :=
    (StableChangeCasesOneTwoFullTail G k e0 corrOne.replacementInput T muOne
      corrOne.replacementETT baseOne COne ctxOne theta eta thetaEtaNe
      (by rw [prefixOne]; exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩)
      z pathTwo muTwo rfl caseTwo
      (by dsimp only; rw [firstThetaOne]; exact disjointTwo)
      (by dsimp only; rw [starOne]; exact fixedTailTwo)
      (by rw [prefixOne]; exact missingTwo) storedFirstTwo).2.2.2.2
  have etaTerminalTwo : eta ∈ MissingColors G muTwo (T.vertex endIndex) :=
    behaviorTwo.2.1 _ (selfComponent muOne theta eta _) hthetaTerminalOne
  have etaPenultimateTwo : eta ∈ MissingColors G muTwo (T.vertex penIndex) := by
    rw [missingTwo _ hPenultimateInBplus]
    exact hetaPenultimateOne
  have lastTailBound : A.length ≤ lastIndex.val := by
    have ht := hTailAtLeast
    have hell := hellOuter
    have hl := lastPosition
    clear * - ht hell hl
    omega
  have lastTwo : muTwo (T.edge lastIndex) = some alpha :=
    (fixedTailTwo lastIndex lastTailBound).trans hlastOne
  obtain ⟨CTwo, sameTwo⟩ : ∃ CTwo : HierarchyCounterexample baseTwo,
      SameGoodHierarchy COne.good CTwo.good := by
    refine ⟨{
      positive := by rw [corrTwo.rungAgreement]; exact COne.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := maxTwo
      notElementary := ?_ }, sameTwo⟩
    intro he
    exact Finset.disjoint_left.mp
      (he (vertexMemOuter T penIndex)
        (vertexMemOuter T endIndex) penultimateTerminalNe)
      etaPenultimateTwo etaTerminalTwo
  obtain ⟨PTwo, colorTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo sameTwo
  have alphaPresentPenultimate : alpha ∉ MissingColors G phi (T.vertex penIndex) := by
    intro hm
    have hne : T.vertex (HierarchyFirstMissingPosition phi T alpha) ≠
        T.vertex penIndex := by
      intro he
      have hi := congrArg Fin.val (T.vertex_injective he)
      have hb := hAlphaFirstBound
      have hp := penPosition
      have hl := hBLouter
      clear * - hi hb hp hl
      omega
    exact Finset.disjoint_left.mp (hElemOuter hAlphaFirstBplus hPenultimateInBplus hne) hAlphaAtFirst hm
  have alphaPresentTwo : alpha ∉ MissingColors G muTwo (T.vertex penIndex) := by
    rw [missingTwo _ hPenultimateInBplus, hmissingPointwise _ hPenultimateInBplus]
    exact alphaPresentPenultimate
  have starTwo : HierarchyStarredStage PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount) = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy PTwo.counterexample.hierarchy PTwo.sameGood.1).1.symm
  have pathTwoEq : HierarchyPathNumber C.hierarchy = HierarchyPathNumber PTwo.counterexample.hierarchy :=
    (P2752_T2_HierarchyMeasures C.hierarchy PTwo.counterexample.hierarchy PTwo.sameGood.1).2.1
  have etaStoredTwo : eta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount) := by
    obtain ⟨hc, hd⟩ := PTwo.sameGood.2
    have hi : Fin.cast (congrArg (fun d => d + 1) hc) q =
        Fin.last PTwo.counterexample.hierarchy.dividerCount := Fin.ext hc
    have hs := (hd q).1
    rw [hi] at hs
    exact hs ▸ hetaStored
  obtain ⟨gammaOne, gammaTwo, gammaDistinct, gammaPair⟩ :=
    Finset.card_eq_two.mp (PTwo.counterexample.good.twoColors _ eta etaStoredTwo)
  let finalData : HierarchySituationTwoCaseOneData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext := {
    tailAtLeastTwo := by
      change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
        (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [starTwo]
      exact hTailAtLeast
    pathNumberFull := by
      rw [← pathTwoEq]
      change HierarchyPathNumber C.hierarchy = T.length -
        (HierarchyStarredStage PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [starTwo]
      exact D.pathNumberFull
    lastEdgeIndex := lastIndex
    penultimateVertexIndex := penIndex
    terminalVertexIndex := endIndex
    lastEdgePosition := lastPosition
    penultimateVertexPosition := penPosition
    terminalVertexPosition := endPosition
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
    theta := alpha
    thetaOnLastEdge := colorTwo.symm ▸ lastTwo
    thetaPresentPenultimate := colorTwo.symm ▸ alphaPresentTwo
    alpha := eta
    gammaOne := gammaOne
    gammaTwo := gammaTwo
    alphaMissingPenultimate := colorTwo.symm ▸ etaPenultimateTwo
    alphaMissingTerminal := colorTwo.symm ▸ etaTerminalTwo
    alphaStored := etaStoredTwo
    gammaPair := gammaPair
    gammaDistinct := gammaDistinct }
  exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData
