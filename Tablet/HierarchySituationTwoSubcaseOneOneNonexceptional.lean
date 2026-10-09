import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyPathNumber
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStoredColorsAt
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.SameGoodHierarchy
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSpanningPath
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.MissingColorIncidenceEndpoint

-- [TABLET NODE: HierarchySituationTwoSubcaseOneOneNonexceptional]
theorem HierarchySituationTwoSubcaseOneOneNonexceptional {V E : Type*}
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
    (hnonexceptional :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      D.theta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∨
        ∃ eta, eta ∈ HierarchyStoredColorsAt H q ∧
          D.theta ∈ C.good.gamma q eta ∧
          eta ∉ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
    False := by
-- BODY
  set_option maxHeartbeats 1000000 in
    classical
    let H := C.hierarchy
    let q := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
    let P := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    have transSegment {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
    have stageSegment : ∀ a d : ℕ, ∀ hb : a + d ≤ H.dividerCount + 1,
        TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
          (H.stage ⟨a + d, by omega⟩) := by
      intro a d
      induction d with
      | zero => intro hb; exact ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
      | succ d ih =>
        intro hb
        have hp := ih (by omega)
        have hn := H.nested ⟨a + d, by omega⟩
        exact transSegment hp (by simpa [Nat.add_assoc] using hn)
    have starredAt (j : Fin (H.dividerCount + 1)) (hj : j.val ≠ 0) :
        HierarchyStarredStage H j = H.stage j.castSucc := by
      obtain hz | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · exact False.elim (hj (congrArg Fin.val hz))
      · rfl
    have hAT : TreeSequenceInitialSegment A T := by
      by_cases hz : H.dividerCount = 0
      · have hq : q = 0 := Fin.ext (by simp [q, hz])
        have hs : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
            Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
        simpa [A, hq, HierarchyStarredStage, hs, H.terminalStage] using H.coreInsideFirst
      · have ha : A = H.stage q.castSucc := starredAt q (by simpa [q] using hz)
        rw [ha]
        have hs : H.stage q.succ = T := by
          convert H.terminalStage using 1
          congr 1
        simpa only [hs] using H.nested q
    have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    have hBL : B.length + 2 = T.length := by
      change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
      omega
    have hPL : P.length + 1 = T.length := by
      change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
      omega
    have hBT : TreeSequenceInitialSegment B T :=
      ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
    have hPT : TreeSequenceInitialSegment P T :=
      ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
    have restrictSegment {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z)
        (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
        TreeSequenceInitialSegment X Y := by
      refine ⟨hXY, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
    have hAB : TreeSequenceInitialSegment A B := restrictSegment hAT hBT (by omega)
    have hBP : TreeSequenceInitialSegment B P := restrictSegment hBT hPT (by omega)
    have hPE : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) :=
      HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
        ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
        ctx.lexicographicMinimality ctx.largeMissingSet
    have vertexMem (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
        X.vertex i ∈ TreeSequenceVertexSet X := by
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
    have firstLe (X : TreeSequence G e0) (c : Fin k)
        (i : Fin (X.length + 1)) (hi : c ∈ MissingColors G phi (X.vertex i)) :
        (HierarchyFirstMissingPosition phi X c).val ≤ i.val := by
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
      intro hm
      have := firstLe X c i hm
      omega
    have firstLower (X : TreeSequence G e0) (c : Fin k) (t : ℕ)
        (ht : t ≤ X.length)
        (hn : ∀ i : Fin (X.length + 1), i.val < t →
          c ∉ MissingColors G phi (X.vertex i)) :
        t ≤ (HierarchyFirstMissingPosition phi X c).val := by
      by_contra hlt
      have hp : (HierarchyFirstMissingPosition phi X c).val < t := by omega
      have hm : c ∈ TreeMissingColors phi X := by
        by_contra hm
        have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
          unfold HierarchyFirstMissingPosition
          dsimp only
          rw [dif_neg]
          rintro ⟨i, hi⟩
          exact hm (Finset.mem_biUnion.mpr
            ⟨X.vertex i, vertexMem X i, (Finset.mem_filter.mp hi).2⟩)
        have := congrArg Fin.val he
        simp only [Fin.val_last] at this
        omega
      exact hn _ hp (firstMissing X c hm)
    have alphaNotB : D.alpha ∉ TreeMissingColors phi B := by
      intro hm
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      have hne : B.vertex i ≠ T.vertex D.penultimateVertexIndex := by
        intro he
        have hh := T.vertex_injective ((hBT.2.1 i).trans he)
        have hv := congrArg Fin.val hh
        have hi := i.isLt
        have hp := D.penultimateVertexPosition
        simp only [Fin.val_castLE] at hv
        omega
      have hp : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet P := by
        have he : Fin.castLE (Nat.succ_le_succ hPT.1) (Fin.last P.length) =
            D.penultimateVertexIndex := Fin.ext (by simpa using hPL.trans D.penultimateVertexPosition.symm)
        rw [← he, hPT.2.1]
        exact vertexMem P _
      exact Finset.disjoint_left.mp
        (hPE (TreeSequenceInitialSegmentVertexSetSubset hBP (vertexMem B i)) hp hne)
        hcv D.alphaMissingPenultimate
    have alphaFirst : HierarchyFirstMissingPosition phi T D.alpha =
        D.penultimateVertexIndex := by
      apply Fin.ext
      have hu := firstLe T D.alpha D.penultimateVertexIndex D.alphaMissingPenultimate
      have hl := firstLower T D.alpha (B.length + 1) (by omega) (by
        intro i hi hm
        let j : Fin (B.length + 1) := ⟨i.val, hi⟩
        have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
        apply alphaNotB
        refine Finset.mem_biUnion.mpr ⟨B.vertex j, vertexMem B j, ?_⟩
        simpa [← hBT.2.1 j, he] using hm)
      have hp := D.penultimateVertexPosition
      omega
    obtain ⟨R, hroute, hminusRoute, hstarRoute, corrMinus, mpMinus,
      baseMinus, coreMinus, closureMinus, supportMinus, HMinus, countMinus,
      stagesMinus, positionsMinus, corrStar, mpStar, baseStar, coreStar,
      closureStar, supportStar, HStar, countStar, stagesStar, positionsStar⟩ :=
      HierarchySituationTwoReorderedTreesCertified G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData
    obtain ⟨minusLength, hBM, minusEdge⟩ := R.minusFinal
    obtain ⟨starLength, hMS, starEdge⟩ := R.starFinal
    change R.minus.length = B.length + 1 at minusLength
    change TreeSequenceInitialSegment B R.minus at hBM
    change HMinus.dividerCount = H.dividerCount at countMinus
    change HStar.dividerCount = H.dividerCount at countStar
    change ∀ j : Fin (HMinus.dividerCount + 1), HMinus.stage j.castSucc =
      H.stage (Fin.cast (congrArg (fun d => d + 1) countMinus) j).castSucc at stagesMinus
    change ∀ j : Fin (HStar.dividerCount + 1), HStar.stage j.castSucc =
      H.stage (Fin.cast (congrArg (fun d => d + 1) countStar) j).castSucc at stagesStar
    have hBS := transSegment hBM hMS
    have hML : R.minus.length + 1 = T.length := by omega
    have hSL : R.star.length = T.length := by omega
    have terminalData (U : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U) :
        corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc =
            ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
            TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
      rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hf,
        ht, hd, he, hk, hp, ho, hstable⟩
      cases newETT with
      | mk rounds positive data above strict below generating =>
        cases hr
        have hseries : data = newSeries := eq_of_heq hs
        cases hseries
        let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
        have hi : i.succ = Fin.last ett.rounds := Fin.ext (by
          simp [i]; have := ett.roundsPositive; omega)
        have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc =
            ett.series.data.tree (Fin.last ett.rounds).castSucc := by
          rw [← hi]
          exact ht i
        refine ⟨htree, hk _, ?_⟩
        unfold TashkinovStoredColors
        have hn : (Fin.last ett.rounds).val ≠ 0 := by
          have := ett.roundsPositive
          simpa using Nat.ne_of_gt (Nat.zero_lt_of_lt ett.roundsPositive)
        simp only [if_neg hn]
        simp_rw [hd]
        rw [← hf, ← ett.generatingColoring, htree]
    have dataMinus := terminalData R.minus corrMinus
    have dataStar := terminalData R.star corrStar
    have hierarchyData (U : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
        (b : HierarchyBase corr.replacementETT phi)
        (hc : b.core = base.core)
        (K : TashkinovHierarchy corr.replacementETT b)
        (hn : K.dividerCount = H.dividerCount)
        (hs : ∀ j : Fin (K.dividerCount + 1), K.stage j.castSucc =
          H.stage (Fin.cast (congrArg (fun d => d + 1) hn) j).castSucc) :
        ∀ j : Fin (K.dividerCount + 1),
          let jo := Fin.cast (congrArg (fun d => d + 1) hn) j
          HierarchyStarredStage K j = HierarchyStarredStage H jo ∧
          HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H jo ∧
          HierarchyStageMissingColors K j = HierarchyStageMissingColors H jo := by
      intro j
      let index := fun j : Fin (K.dividerCount + 1) =>
        Fin.cast (congrArg (fun d => d + 1) hn) j
      have hz : index 0 = 0 := Fin.ext rfl
      have hstar : HierarchyStarredStage K j = HierarchyStarredStage H (index j) := by
        obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · subst j
          simpa [hz, HierarchyStarredStage] using hc
        · have hi : (index i.succ).val ≠ 0 := by simp [index]
          rw [starredAt (index i.succ) hi]
          exact hs i.succ
      refine ⟨hstar, ?_, ?_⟩
      · unfold HierarchyStoredColorsAt
        dsimp only
        rw [(terminalData U corr).2.2, hstar]
      · obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · subst j
          change TreeMissingColors phi (corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc) = HierarchyStageMissingColors H (index 0)
          rw [hz]
          change TreeMissingColors phi (corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc) =
            TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          rw [(terminalData U corr).1]
        · let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
          have hi : index i.succ = io.succ := Fin.ext rfl
          simp only [HierarchyStageMissingColors, hi, Fin.cases_succ]
          exact congrArg (TreeMissingColors phi) (hs i.succ)
    have infoMinus := hierarchyData R.minus corrMinus baseMinus coreMinus HMinus
      countMinus stagesMinus
    have infoStar := hierarchyData R.star corrStar baseStar coreStar HStar countStar stagesStar
    have firstMissingBelow (X : TreeSequence G e0) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition phi X c).val < X.length) :
        c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
      let candidates := Finset.univ.filter fun i : Fin (X.length + 1) =>
        c ∈ MissingColors G phi (X.vertex i)
      by_cases hn : candidates.Nonempty
      · have he : HierarchyFirstMissingPosition phi X c = candidates.min' hn := by
          simp only [HierarchyFirstMissingPosition, candidates, dif_pos hn]
        rw [he]
        exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      · have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
          simp only [HierarchyFirstMissingPosition, candidates, dif_neg hn]
        rw [he] at hlt
        simp only [Fin.val_last] at hlt
        omega
    have oldAvoid (eta c : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
        (hc : c ∈ C.good.gamma q eta) :
        c ∉ Finset.univ.filter (fun c => ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
          phi (T.edge r) = some c) := by
      have hh := (Finset.mem_sdiff.mp (C.good.avoidance q eta hs hc)).2
      change c ∉ HierarchySegmentColors H q eta at hh
      unfold HierarchySegmentColors at hh
      dsimp only at hh
      have hend : H.stage q.succ = T := by convert H.terminalStage using 1; congr 1
      rw [hend] at hh
      exact hh
    have thetaCutoff (eta : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
        (hc : D.theta ∈ C.good.gamma q eta) :
        (HierarchyFirstMissingPosition phi T eta).val ≤ B.length := by
      have hpresent : eta ∉ MissingColors G phi (T.vertex D.penultimateVertexIndex) := by
        rcases hnonexceptional with hout | ⟨selected, hselected, hpair, hpresent⟩
        · exact False.elim (hout (Finset.mem_biUnion.mpr ⟨eta, hs, hc⟩))
        · by_cases he : eta = selected
          · simpa [he] using hpresent
          · exact False.elim (Finset.disjoint_left.mp
              (C.good.disjointPairs q eta selected hs hselected he) hc hpair)
      have hu : (HierarchyFirstMissingPosition phi T eta).val ≤
          D.lastEdgeIndex.val := by
        by_contra hlt
        apply oldAvoid eta D.theta hs hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.lastEdgeIndex,
          by have := D.lastEdgePosition; omega,
          by have := D.lastEdgeIndex.isLt; omega, D.thetaOnLastEdge⟩
      by_contra hlt
      have he : HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex := by
        apply Fin.ext
        have := D.penultimateVertexPosition
        have := D.lastEdgePosition
        omega
      have hm := firstMissingBelow T eta (by have := D.lastEdgeIndex.isLt; omega)
      rw [he] at hm
      exact hpresent hm
    have terminalAvoid (U : TreeSequence G e0)
        (hBU : TreeSequenceInitialSegment B U)
        (hedges : ∀ r : Fin U.length,
          (∃ t : Fin T.length, t.val = r.val ∧ r.val < B.length ∧ U.edge r = T.edge t) ∨
          (r.val = B.length ∧ U.edge r = T.edge D.lastEdgeIndex) ∨
          (r.val = B.length + 1 ∧ U.edge r = T.edge R.penultimateEdgeIndex)) :
        ∀ eta c, eta ∈ HierarchyStoredColorsAt H q → c ∈ C.good.gamma q eta →
          c ∉ Finset.univ.filter (fun c => ∃ r : Fin U.length,
            A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
            phi (U.edge r) = some c) := by
      intro eta c hs hc hmem
      obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hmem
      have hnew : r.val < (HierarchyFirstMissingPosition phi U eta).val := lt_of_lt_of_le hhi (Nat.min_le_left _ _)
      have commonAbsent : ∀ i : Fin (T.length + 1), i.val ≤ B.length → i.val ≤ r.val →
          eta ∉ MissingColors G phi (T.vertex i) := by
        intro i hi hir
        let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
        have hn := firstBefore U eta (Fin.castLE (Nat.succ_le_succ hBU.1) j) (by
          change i.val < (HierarchyFirstMissingPosition phi U eta).val
          omega)
        rw [hBU.2.1 j, ← hBT.2.1 j, he] at hn
        exact hn
      rcases hedges r with ⟨t, ht, htb, hedge⟩ | ⟨hr, hedge⟩ | ⟨hr, hedge⟩
      · have hcut := firstLower T eta (t.val + 1) (by have := t.isLt; omega) (by
          intro i hi
          exact commonAbsent i (by omega) (by omega))
        apply oldAvoid eta c hs hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, by omega,
          by have := t.isLt; omega, by rwa [hedge] at hcol⟩
      · have he : c = D.theta := by rw [hedge, D.thetaOnLastEdge] at hcol; exact (Option.some.inj hcol).symm
        subst c
        have hcut := thetaCutoff eta hs hc
        let i := HierarchyFirstMissingPosition phi T eta
        let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
        have hm := firstMissingBelow T eta (by omega)
        have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
        have hmu : eta ∈ MissingColors G phi
            (U.vertex (Fin.castLE (Nat.succ_le_succ hBU.1) j)) := by
          rw [hBU.2.1 j, ← hBT.2.1 j, he]
          exact hm
        have := firstLe U eta _ hmu
        simp only [Fin.val_castLE] at this
        omega
      · have ht : R.penultimateEdgeIndex.val = B.length := by
          have := R.penultimateEdgePosition
          omega
        have hcut := firstLower T eta (B.length + 1) (by omega) (by
          intro i hi
          exact commonAbsent i (by omega) (by omega))
        apply oldAvoid eta c hs hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.penultimateEdgeIndex,
          by omega, by have := R.penultimateEdgeIndex.isLt; omega,
          by rwa [hedge] at hcol⟩
    have edgesMinus (r : Fin R.minus.length) :
        (∃ t : Fin T.length, t.val = r.val ∧ r.val < B.length ∧ R.minus.edge r = T.edge t) ∨
        (r.val = B.length ∧ R.minus.edge r = T.edge D.lastEdgeIndex) ∨
        (r.val = B.length + 1 ∧ R.minus.edge r = T.edge R.penultimateEdgeIndex) := by
      by_cases hr : r.val < B.length
      · let i : Fin B.length := ⟨r.val, hr⟩
        have he : Fin.castLE hBM.1 i = r := Fin.ext rfl
        refine Or.inl ⟨Fin.castLE hBT.1 i, rfl, hr, ?_⟩
        rw [← he, hBM.2.2 i, hBT.2.2 i]
      · have he : r = Fin.cast minusLength.symm (Fin.last B.length) := Fin.ext (by simp; omega)
        exact Or.inr (Or.inl ⟨by omega, by rw [he]; exact minusEdge⟩)
    have edgesStar (r : Fin R.star.length) :
        (∃ t : Fin T.length, t.val = r.val ∧ r.val < B.length ∧ R.star.edge r = T.edge t) ∨
        (r.val = B.length ∧ R.star.edge r = T.edge D.lastEdgeIndex) ∨
        (r.val = B.length + 1 ∧ R.star.edge r = T.edge R.penultimateEdgeIndex) := by
      by_cases hr : r.val < R.minus.length
      · let i : Fin R.minus.length := ⟨r.val, hr⟩
        have he : Fin.castLE hMS.1 i = r := Fin.ext rfl
        rw [← he, hMS.2.2 i]
        simpa using edgesMinus i
      · have he : r = Fin.cast starLength.symm (Fin.last R.minus.length) := Fin.ext (by simp; omega)
        exact Or.inr (Or.inr ⟨by omega, by rw [he]; exact starEdge⟩)
    have avoidMinus := terminalAvoid R.minus hBM edgesMinus
    have avoidStar := terminalAvoid R.star hBS edgesStar
    have nextBound (i : Fin H.dividerCount) :
        (H.stage i.succ.castSucc).length ≤ B.length := by
      have hp : H.dividerCount ≠ 0 := by have := i.isLt; omega
      have ha : A = H.stage q.castSucc := starredAt q (by simpa [q] using hp)
      have hh := stageSegment (i.val + 1) (H.dividerCount - (i.val + 1)) (by omega)
      have hlo : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc := Fin.ext rfl
      have hhi : (⟨i.val + 1 + (H.dividerCount - (i.val + 1)), by omega⟩ :
          Fin (H.dividerCount + 2)) = q.castSucc := Fin.ext (by simp [q])
      rw [hlo, hhi, ← ha] at hh
      exact le_trans hh.1 hAB.1
    have makeGood (U : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
        (b : HierarchyBase corr.replacementETT phi)
        (hc : b.core = base.core) (hcl : b.closure = base.closure)
        (K : TashkinovHierarchy corr.replacementETT b)
        (hn : K.dividerCount = H.dividerCount)
        (hs : ∀ j : Fin (K.dividerCount + 1), K.stage j.castSucc =
          H.stage (Fin.cast (congrArg (fun d => d + 1) hn) j).castSucc)
        (hBU : TreeSequenceInitialSegment B U)
        (hav : ∀ eta c, eta ∈ HierarchyStoredColorsAt H q → c ∈ C.good.gamma q eta →
          c ∉ Finset.univ.filter (fun c => ∃ r : Fin U.length,
            A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
            phi (U.edge r) = some c)) :
        ∃ good : GoodHierarchy K, ∀ j eta,
          good.gamma j eta = C.good.gamma
            (Fin.cast (congrArg (fun d => d + 1) hn) j) eta := by
      let index := fun j : Fin (K.dividerCount + 1) =>
        Fin.cast (congrArg (fun d => d + 1) hn) j
      let gamma := fun j eta => C.good.gamma (index j) eta
      have info := hierarchyData U corr b hc K hn hs
      have stageEq (j : Fin (K.dividerCount + 1)) :
          K.stage j.castSucc = H.stage (index j).castSucc := hs j
      have starEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStarredStage K j = HierarchyStarredStage H (index j) := (info j).1
      have storedEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (index j) := (info j).2.1
      have missingEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStageMissingColors K j = HierarchyStageMissingColors H (index j) := (info j).2.2
      have indexZero : index 0 = 0 := Fin.ext rfl
      have indexLast : index (Fin.last K.dividerCount) = q := Fin.ext (by simp [index, q, hn])
      have segmentEq (i : Fin K.dividerCount) (eta : Fin k) :
          HierarchySegmentColors K i.castSucc eta =
            HierarchySegmentColors H (index i.castSucc) eta := by
        let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
        have hprev : index i.castSucc = io.castSucc := Fin.ext rfl
        have hnext : index i.succ = io.succ := Fin.ext rfl
        have hcutOld := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta
          (H.stage io.succ.castSucc).length (nextBound io)
        have hcutNew := HierarchyFirstMissingPositionPrefixCutoff phi B U hBU eta
          (H.stage io.succ.castSucc).length (nextBound io)
        have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        have hio : io.castSucc.succ = io.succ.castSucc := Fin.ext rfl
        unfold HierarchySegmentColors
        dsimp only
        rw [hi, stageEq i.succ, starEq i.castSucc, hnext, hprev, hio,
          ← hcutOld, ← hcutNew]
      let good : GoodHierarchy K :=
        { gamma := gamma
          twoColors := by
            intro j eta heta
            exact C.good.twoColors (index j) eta ((storedEq j) ▸ heta)
          avoidance := by
            intro j eta heta c hcg
            have oldStored := (storedEq j) ▸ heta
            have oldAvoidance := Finset.mem_sdiff.mp (C.good.avoidance (index j) eta oldStored hcg)
            refine Finset.mem_sdiff.mpr ⟨(missingEq j).symm ▸ oldAvoidance.1, ?_⟩
            by_cases hj : j.val < K.dividerCount
            · let i : Fin K.dividerCount := ⟨j.val, hj⟩
              have hi : i.castSucc = j := Fin.ext rfl
              rw [← hi, segmentEq i eta]
              simpa [hi] using oldAvoidance.2
            · have hjlast : j = Fin.last K.dividerCount := Fin.ext (by simp; have := j.isLt; omega)
              subst j
              have hh := hav eta c (by simpa [indexLast] using oldStored)
                (by simpa [gamma, indexLast] using hcg)
              unfold HierarchySegmentColors
              dsimp only
              have hend : K.stage (Fin.last K.dividerCount).succ = U := by
                convert K.terminalStage using 1
                congr 1
              rw [hend, starEq, indexLast]
              exact hh
          disjointPairs := by
            intro j eta theta heta htheta hne
            exact C.good.disjointPairs (index j) eta theta
              ((storedEq j) ▸ heta) ((storedEq j) ▸ htheta) hne
          uniqueRefresh := by
            intro i
            let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
            have hnext : io.succ = index i.succ := Fin.ext rfl
            have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
            obtain ⟨eta, heta, hunique⟩ := C.good.uniqueRefresh io
            refine ⟨eta, ?_, ?_⟩
            · refine ⟨?_, ?_, ?_⟩
              · rw [storedEq i.succ, ← hnext]
                exact heta.1
              · rw [stageEq i.succ, starEq i.castSucc]
                have hh := heta.2.1
                rw [hnext, hprev] at hh
                exact hh
              · intro theta htheta hne
                have hh := heta.2.2 theta (by simpa [storedEq, hnext] using htheta) hne
                simpa [gamma, hnext, hprev] using hh
            · intro theta htheta
              apply hunique theta
              refine ⟨?_, ?_, ?_⟩
              · simpa [storedEq, hnext] using htheta.1
              · have hh := htheta.2.1
                rw [stageEq i.succ, starEq i.castSucc] at hh
                rw [hnext, hprev]
                exact hh
              · intro z hz hne
                have hh := htheta.2.2 z (by simpa [storedEq, hnext] using hz) hne
                simpa [gamma, hnext, hprev] using hh
          parallelBase := by
            dsimp only
            intro hpe
            have hpeOld := (terminalData U corr).2.1 ▸ hpe
            have hold := C.good.parallelBase hpeOld
            have hz : (HierarchyStoredColorsAt K 0).biUnion (gamma 0) =
                (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
              rw [storedEq 0, indexZero]
              simp only [gamma, indexZero]
            rw [hc, hcl, hz, (terminalData U corr).1]
            exact hold
          minusClosed := by
            intro i
            let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
            have hnext : io.succ = index i.succ := Fin.ext rfl
            have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
            rw [stageEq i.succ, storedEq i.succ]
            have hh := C.good.minusClosed io
            rw [hnext, hprev] at hh
            exact hh }
      exact ⟨good, by intro j eta; rfl⟩
    obtain ⟨goodMinus, gammaMinus⟩ := makeGood R.minus corrMinus baseMinus coreMinus
      closureMinus HMinus countMinus stagesMinus hBM avoidMinus
    obtain ⟨goodStar, gammaStar⟩ := makeGood R.star corrStar baseStar coreStar
      closureStar HStar countStar stagesStar hBS avoidStar
    have missingSubset {X Y : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y) :
        TreeMissingColors phi X ⊆ TreeMissingColors phi Y := by
      intro c hc
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hcv⟩
    have stageMissingA : HierarchyStageMissingColors H q ⊆ TreeMissingColors phi A := by
      by_cases hz : H.dividerCount = 0
      · have hq : q = 0 := Fin.ext (by simp [q, hz])
        have hcore : A = base.core := by simp [A, hq, HierarchyStarredStage]
        rw [hq]
        change TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆ _
        rw [hcore]
        by_cases hpe : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
        · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hpe
          exact missingSubset u.leftSegment
        · rw [base.nonparallel hpe]
      · have hp : q.val ≠ 0 := by simpa [q] using hz
        obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
        · exact False.elim (hp (congrArg Fin.val hzero))
        · rw [hi]
          change TreeMissingColors phi (H.stage i.succ.castSucc) ⊆ _
          rw [show A = H.stage i.succ.castSucc by dsimp only [A]; rw [hi]; rfl]
    have gammaMem : D.gammaOne ∈ C.good.gamma q D.alpha := by
      rw [D.gammaPair]
      simp
    have gammaStage : D.gammaOne ∈ HierarchyStageMissingColors H q :=
      (Finset.mem_sdiff.mp (C.good.avoidance q D.alpha D.alphaStored gammaMem)).1
    have gammaA := stageMissingA gammaStage
    have alphaNotA : D.alpha ∉ TreeMissingColors phi A :=
      (Finset.mem_sdiff.mp D.alphaStored).2
    have gammaNe : D.gammaOne ≠ D.alpha := by
      intro he
      exact alphaNotA (he ▸ gammaA)
    let ig := HierarchyFirstMissingPosition phi T D.gammaOne
    let vg := T.vertex ig
    have gammaT := missingSubset hAT gammaA
    have gammaAt : D.gammaOne ∈ MissingColors G phi vg := firstMissing T D.gammaOne gammaT
    have igBound : ig.val ≤ A.length := by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp gammaA
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      have hm : D.gammaOne ∈ MissingColors G phi
          (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i)) := by
        rw [hAT.2.1 i]
        exact hcv
      have hh := firstLe T D.gammaOne _ hm
      have := i.isLt
      simp only [Fin.val_castLE] at hh
      omega
    have vgA : vg ∈ TreeSequenceVertexSet A := by
      let i : Fin (A.length + 1) := ⟨ig.val, by omega⟩
      have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ig := Fin.ext rfl
      dsimp only [vg]
      rw [← hi, hAT.2.1 i]
      exact vertexMem A _
    have vgPen : vg ≠ T.vertex D.penultimateVertexIndex := by
      intro he
      have hh := congrArg Fin.val (T.vertex_injective he)
      have := D.penultimateVertexPosition
      omega
    have vgTerminal : vg ≠ T.vertex D.terminalVertexIndex := by
      intro he
      have hh := congrArg Fin.val (T.vertex_injective he)
      have := D.terminalVertexPosition
      omega
    have penTerminal : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
      intro he
      have hh := congrArg Fin.val (T.vertex_injective he)
      have := D.penultimateVertexPosition
      have := D.terminalVertexPosition
      omega
    have penInP : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet P := by
      have he : Fin.castLE (Nat.succ_le_succ hPT.1) (Fin.last P.length) =
          D.penultimateVertexIndex := Fin.ext (by simp; have := D.penultimateVertexPosition; omega)
      rw [← he, hPT.2.1]
      exact vertexMem P _
    have oldPrefixMissing : D.gammaOne ∈ TreeMissingColors phi P ∧ D.alpha ∈ TreeMissingColors phi P :=
      ⟨missingSubset (transSegment hAB hBP) gammaA,
        Finset.mem_biUnion.mpr ⟨_, penInP, D.alphaMissingPenultimate⟩⟩
    have oldOrderedUnused :
        TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T D.gammaOne))
          (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
        D.gammaOne ∉ Finset.univ.filter (fun c => ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < (HierarchyFirstMissingPosition phi T D.alpha).val ∧
          phi (T.edge r) = some c) := by
      refine ⟨⟨ig, D.penultimateVertexIndex, rfl, by rw [alphaFirst], ?_⟩, ?_⟩
      · have := D.penultimateVertexPosition
        omega
      · intro hm
        obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hm
        apply oldAvoid D.alpha D.gammaOne D.alphaStored gammaMem
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hlo,
          lt_min hhi r.isLt, hcol⟩
    have changeOld := ChangeLemma G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality hPE ctx.largeMissingSet D.gammaOne D.alpha gammaNe
      oldPrefixMissing (by dsimp only; intro _; exact oldOrderedUnused)
    have lastMissingPositive {U : TreeSequence G e0} {inp : PartialEdgeColoring E k}
        {et : ExtendedTashkinovTree G k e0 inp U phi} {b : HierarchyBase et phi}
        (K : TashkinovHierarchy et b) (hp : 0 < K.dividerCount) :
        HierarchyStageMissingColors K (Fin.last K.dividerCount) =
          TreeMissingColors phi (K.stage ⟨K.dividerCount, by omega⟩) := by
      let i : Fin K.dividerCount := ⟨K.dividerCount - 1, by omega⟩
      have hi : Fin.last K.dividerCount = i.succ := Fin.ext (by simp [i]; omega)
      rw [hi]
      change TreeMissingColors phi (K.stage i.succ.castSucc) = _
      congr 2
      apply Fin.ext
      simp [i]
      omega
    have componentOld : TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg) =
        TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
      have hh := changeOld
      dsimp only at hh
      rw [alphaFirst] at hh
      by_cases hz : H.dividerCount = 0
      · apply hh.2.1
        refine ⟨hz, Or.inl ?_⟩
        have hq : q = 0 := Fin.ext (by simp [q, hz])
        simpa [hq, HierarchyStageMissingColors] using gammaStage
      · apply hh.1
        refine ⟨Nat.pos_of_ne_zero hz, Or.inl ?_⟩
        rwa [lastMissingPositive H (by omega)] at gammaStage
    have lastMinus : HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) = A := by
      have hi : Fin.cast (congrArg (fun d => d + 1) countMinus) (Fin.last HMinus.dividerCount) = q :=
        Fin.ext (by simp [q, countMinus])
      simpa [hi] using (infoMinus (Fin.last HMinus.dividerCount)).1
    have lastStar : HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A := by
      have hi : Fin.cast (congrArg (fun d => d + 1) countStar) (Fin.last HStar.dividerCount) = q :=
        Fin.ext (by simp [q, countStar])
      simpa [hi] using (infoStar (Fin.last HStar.dividerCount)).1
    have pathBound {U : TreeSequence G e0} {inp : PartialEdgeColoring E k}
        {et : ExtendedTashkinovTree G k e0 inp U phi} {b : HierarchyBase et phi}
        (K : TashkinovHierarchy et b) :
        HierarchyPathNumber K ≤ U.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length := by
      unfold HierarchyPathNumber
      dsimp only
      split
      · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ _)).1).2
      · exact le_rfl
    have vgMinus := TreeSequenceInitialSegmentVertexSetSubset (transSegment hAB hBM) vgA
    have terminalMinus : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet R.minus := by
      rw [← R.minusTerminalVertex]
      exact vertexMem R.minus _
    have gammaNotTerminal : D.gammaOne ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) := by
      intro hm
      have hnot : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet R.minus) := by
        intro he
        exact Finset.disjoint_left.mp (he vgMinus terminalMinus vgTerminal) gammaAt hm
      let CM : HierarchyCounterexample baseMinus :=
        { positive := by rw [corrMinus.rungAgreement]; exact C.positive
          hierarchy := HMinus
          good := goodMinus
          maximum := mpMinus
          notElementary := hnot }
      have hbound := pathBound HMinus
      rw [lastMinus] at hbound
      apply ctx.lexicographicMinimality CM corrMinus.rungAgreement countMinus
      apply Or.inl
      change HierarchyPathNumber HMinus < HierarchyPathNumber H
      rw [D.pathNumberFull]
      change HierarchyPathNumber HMinus < T.length - A.length
      omega
    let CS : HierarchyCounterexample baseStar :=
      { positive := by rw [corrStar.rungAgreement]; exact C.positive
        hierarchy := HStar
        good := goodStar
        maximum := mpStar
        notElementary := by rw [R.starVertexSet]; exact C.notElementary }
    have pathStar : HierarchyPathNumber HStar = HierarchyPathNumber H := by
      have hbound := pathBound HStar
      rw [lastStar, hSL] at hbound
      have hnot : ¬ HierarchyPathNumber HStar < HierarchyPathNumber H := by
        intro hh
        apply ctx.lexicographicMinimality CS corrStar.rungAgreement countStar
        exact Or.inl hh
      have hfull : HierarchyPathNumber H = T.length - A.length := D.pathNumberFull
      omega
    have measureStar : HierarchyCounterexampleMeasure CS = HierarchyCounterexampleMeasure C := by
      apply Prod.ext
      · exact pathStar
      · change R.star.length - (HStar.stage ⟨HStar.dividerCount, by omega⟩).length =
          T.length - (H.stage ⟨H.dividerCount, by omega⟩).length
        have hs := stagesStar (Fin.last HStar.dividerCount)
        have hi : (Fin.cast (congrArg (fun d => d + 1) countStar)
            (Fin.last HStar.dividerCount)).castSucc =
            (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext (by simp [countStar])
        rw [hi] at hs
        have hj : (Fin.last HStar.dividerCount).castSucc =
            (⟨HStar.dividerCount, by omega⟩ : Fin (HStar.dividerCount + 2)) := Fin.ext rfl
        rw [hj] at hs
        simpa only [hSL] using congrArg (fun U : TreeSequence G e0 => T.length - U.length) hs
    let ctxStar : HierarchyMinimumCounterexampleContext G k e0 corrStar.replacementInput
        R.star phi corrStar.replacementETT baseStar CS :=
      { proper := ctx.proper
        oneEdgeUncolored := ctx.oneEdgeUncolored
        lowerRung := by
          intro inp U generating et hp hl hm
          exact ctx.lowerRung et hp (by rwa [corrStar.rungAgreement] at hl) hm
        fewerDividers := by
          intro inp U generating et hr hm b K hg hn
          apply ctx.fewerDividers et (hr.trans corrStar.rungAgreement) hm b K hg
          change K.dividerCount < H.dividerCount
          simpa [CS, countStar] using hn
        lexicographicMinimality := by
          intro inp U generating et b other hr hn hh
          rw [measureStar] at hh
          exact ctx.lexicographicMinimality other (hr.trans corrStar.rungAgreement)
            (hn.trans countStar) hh
        largeMissingSet := by
          dsimp only
          rw [dataStar.1, corrStar.rungAgreement]
          exact ctx.largeMissingSet }
    let PS := HierarchyFullTailPrefix CS (HierarchyFullTailLength CS - 1)
    have elementaryPS : ColoredVertexSetElementary G phi (TreeSequenceVertexSet PS) :=
      HierarchyCounterexamplePenultimateElementary G k e0 corrStar.replacementInput
        R.star phi corrStar.replacementETT baseStar CS ctxStar.proper ctxStar.oneEdgeUncolored
        ctxStar.lowerRung ctxStar.fewerDividers ctxStar.lexicographicMinimality ctxStar.largeMissingSet
    have hPSL : PS.length = R.minus.length := by
      change min ((HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length +
        (R.star.length - (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length - 1)) R.star.length = _
      rw [lastStar]
      omega
    have hPSS : TreeSequenceInitialSegment PS R.star :=
      ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
    have hMPS := restrictSegment hMS hPSS (by omega)
    have hPSM := restrictSegment hPSS hMS (by omega)
    have elementaryMinus : ColoredVertexSetElementary G phi (TreeSequenceVertexSet R.minus) := by
      intro u hu v hv hne
      exact elementaryPS (TreeSequenceInitialSegmentVertexSetSubset hMPS hu)
        (TreeSequenceInitialSegmentVertexSetSubset hMPS hv) hne
    have thetaNe : D.theta ≠ D.gammaOne := by
      intro he
      rcases hnonexceptional with hout | ⟨eta, heta, htheta, hpresent⟩
      · apply hout
        exact Finset.mem_biUnion.mpr ⟨D.alpha, D.alphaStored, he.symm ▸ gammaMem⟩
      · have hne : eta ≠ D.alpha := by
          intro ha
          exact hpresent (ha.symm ▸ D.alphaMissingPenultimate)
        exact Finset.disjoint_left.mp
          (C.good.disjointPairs q eta D.alpha heta D.alphaStored hne) htheta (he.symm ▸ gammaMem)
    let ia : Fin (R.star.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hMS.1) (Fin.last R.minus.length)
    have alphaStarAt : D.alpha ∈ MissingColors G phi (R.star.vertex ia) := by
      rw [hMS.2.1, R.minusTerminalVertex]
      exact D.alphaMissingTerminal
    have alphaStarFirst : HierarchyFirstMissingPosition phi R.star D.alpha = ia := by
      apply Fin.ext
      have hu := firstLe R.star D.alpha ia alphaStarAt
      have hl := firstLower R.star D.alpha (B.length + 1) (by omega) (by
        intro i hi hm
        let j : Fin (B.length + 1) := ⟨i.val, hi⟩
        have he : Fin.castLE (Nat.succ_le_succ hBS.1) j = i := Fin.ext rfl
        apply alphaNotB
        refine Finset.mem_biUnion.mpr ⟨B.vertex j, vertexMem B j, ?_⟩
        rw [← he, hBS.2.1 j] at hm
        exact hm)
      have hi : ia.val = R.minus.length := rfl
      omega
    let jg : Fin (B.length + 1) := ⟨ig.val, by omega⟩
    let isg : Fin (R.star.length + 1) := Fin.castLE (Nat.succ_le_succ hBS.1) jg
    have gammaStarVertex : R.star.vertex isg = vg := by
      rw [hBS.2.1 jg, ← hBT.2.1 jg]
      rfl
    have gammaStarFirst : HierarchyFirstMissingPosition phi R.star D.gammaOne = isg := by
      apply Fin.ext
      have hu := firstLe R.star D.gammaOne isg (gammaStarVertex.symm ▸ gammaAt)
      have hl := firstLower R.star D.gammaOne ig.val (by omega) (by
        intro i hi
        let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hBS.1) j = i := Fin.ext rfl
        have hn := firstBefore T D.gammaOne (Fin.castLE (Nat.succ_le_succ hBT.1) j) (by
          simp only [Fin.val_castLE]; exact hi)
        rwa [hBT.2.1 j, ← hBS.2.1 j, he] at hn)
      change (HierarchyFirstMissingPosition phi R.star D.gammaOne).val = ig.val
      change (HierarchyFirstMissingPosition phi R.star D.gammaOne).val ≤ ig.val at hu
      omega
    have newPrefixMissing : D.gammaOne ∈ TreeMissingColors phi PS ∧ D.alpha ∈ TreeMissingColors phi PS := by
      constructor
      · exact Finset.mem_biUnion.mpr
          ⟨vg, TreeSequenceInitialSegmentVertexSetSubset hMPS vgMinus, gammaAt⟩
      · exact Finset.mem_biUnion.mpr
          ⟨_, TreeSequenceInitialSegmentVertexSetSubset hMPS terminalMinus, D.alphaMissingTerminal⟩
    have newOrderedUnused :
        TreeVertexOrder R.star
          (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.gammaOne))
          (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha)) ∧
        D.gammaOne ∉ Finset.univ.filter (fun c => ∃ r : Fin R.star.length,
          (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length ≤ r.val ∧
            r.val < (HierarchyFirstMissingPosition phi R.star D.alpha).val ∧
            phi (R.star.edge r) = some c) := by
      rw [gammaStarFirst, alphaStarFirst]
      refine ⟨⟨isg, ia, rfl, rfl, ?_⟩, ?_⟩
      · change ig.val < R.minus.length
        omega
      · intro hm
        obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hm
        rw [lastStar] at hlo
        have hia : ia.val = R.minus.length := rfl
        rcases edgesStar r with ⟨t, ht, htb, hedge⟩ | ⟨hr, hedge⟩ | ⟨hr, hedge⟩
        · apply oldAvoid D.alpha D.gammaOne D.alphaStored gammaMem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, t, by omega, ?_, ?_⟩
          · rw [alphaFirst]
            have := D.penultimateVertexPosition
            omega
          · rwa [hedge] at hcol
        · rw [hedge, D.thetaOnLastEdge] at hcol
          exact thetaNe (Option.some.inj hcol)
        · omega
    have changeStar := ChangeLemma G k e0 corrStar.replacementInput R.star phi
      corrStar.replacementETT baseStar CS ctxStar.proper ctxStar.oneEdgeUncolored
      ctxStar.lowerRung ctxStar.fewerDividers ctxStar.lexicographicMinimality
      elementaryPS ctxStar.largeMissingSet D.gammaOne D.alpha gammaNe newPrefixMissing
      (by dsimp only; intro _; exact newOrderedUnused)
    have gammaStarStage : D.gammaOne ∈ HierarchyStageMissingColors HStar (Fin.last HStar.dividerCount) := by
      have hi : Fin.cast (congrArg (fun d => d + 1) countStar) (Fin.last HStar.dividerCount) = q :=
        Fin.ext (by simp [q, countStar])
      rw [(infoStar _).2.2, hi]
      exact gammaStage
    have componentStar : TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg) =
        TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl (T.vertex D.terminalVertexIndex)) := by
      have hh := changeStar
      dsimp only at hh
      rw [gammaStarFirst, alphaStarFirst, gammaStarVertex, hMS.2.1, R.minusTerminalVertex] at hh
      by_cases hz : HStar.dividerCount = 0
      · apply hh.2.1
        refine ⟨hz, Or.inl ?_⟩
        have hq : Fin.last HStar.dividerCount = (0 : Fin (HStar.dividerCount + 1)) :=
          Fin.ext (by simp [hz])
        simpa [hq, HierarchyStageMissingColors] using gammaStarStage
      · apply hh.1
        refine ⟨Nat.pos_of_ne_zero hz, Or.inl ?_⟩
        rwa [lastMissingPositive HStar (by omega)] at gammaStarStage
    obtain ⟨u, v, path, hpath, hsupport⟩ :=
      TwoColorComponentSpanningPath G phi D.gammaOne D.alpha ctx.proper (Sum.inl vg)
    have endpoint (w : V)
        (hw : Sum.inl w ∈ TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg))
        (hm : D.gammaOne ∈ MissingColors G phi w ∨ D.alpha ∈ MissingColors G phi w) :
        Sum.inl w = u ∨ Sum.inl w = v := by
      let graph := TwoColorIncidenceGraph G phi D.gammaOne D.alpha
      have hdegree : @SimpleGraph.degree _ graph (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
        rcases hm with hm | hm
        · exact MissingColorIncidenceEndpoint G phi D.gammaOne D.alpha gammaNe ctx.proper w hm
        · have he : graph = TwoColorIncidenceGraph G phi D.alpha D.gammaOne := by
            ext x y
            cases x <;> cases y <;> simp [graph, TwoColorIncidenceGraph, or_comm]
          rw [he]
          exact MissingColorIncidenceEndpoint G phi D.alpha D.gammaOne gammaNe.symm ctx.proper w hm
      have hleaf : (graph.neighborSet (Sum.inl w)).Subsingleton := by
        letI : Fintype (graph.neighborSet (Sum.inl w)) := Fintype.ofFinite _
        intro x hx y hy
        have hcard : Fintype.card (graph.neighborSet (Sum.inl w)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact hdegree
        exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
      have hmem : Sum.inl w ∈ path.support := by
        change Sum.inl w ∈ {x | x ∈ path.support}
        rw [hsupport]
        exact hw
      by_contra hn
      push_neg at hn
      exact (hpath.isTrail.not_mem_support_of_subsingleton_neighborSet hn.1 hn.2 hleaf) hmem
    have gammaComponent : Sum.inl vg ∈ TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg) := by
      change (TwoColorIncidenceGraph G phi D.gammaOne D.alpha).connectedComponentMk (Sum.inl vg) = _
      rfl
    have penComponent : Sum.inl (T.vertex D.penultimateVertexIndex) ∈
        TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg) := by
      rw [componentOld]
      change (TwoColorIncidenceGraph G phi D.gammaOne D.alpha).connectedComponentMk _ = _
      rfl
    have terminalComponent : Sum.inl (T.vertex D.terminalVertexIndex) ∈
        TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl vg) := by
      rw [componentStar]
      change (TwoColorIncidenceGraph G phi D.gammaOne D.alpha).connectedComponentMk _ = _
      rfl
    have eg := endpoint vg gammaComponent (Or.inl gammaAt)
    have ep := endpoint _ penComponent (Or.inr D.alphaMissingPenultimate)
    have et := endpoint _ terminalComponent (Or.inr D.alphaMissingTerminal)
    have hgp : (Sum.inl vg : Sum V E) ≠ Sum.inl (T.vertex D.penultimateVertexIndex) :=
      fun hh => vgPen (Sum.inl.inj hh)
    have hgt : (Sum.inl vg : Sum V E) ≠ Sum.inl (T.vertex D.terminalVertexIndex) :=
      fun hh => vgTerminal (Sum.inl.inj hh)
    have hpt : (Sum.inl (T.vertex D.penultimateVertexIndex) : Sum V E) ≠
        Sum.inl (T.vertex D.terminalVertexIndex) := fun hh => penTerminal (Sum.inl.inj hh)
    rcases eg with eg | eg <;> rcases ep with ep | ep <;> rcases et with et | et
    · exact hgp (eg.trans ep.symm)
    · exact hgp (eg.trans ep.symm)
    · exact hgt (eg.trans et.symm)
    · exact hpt (ep.trans et.symm)
    · exact hpt (ep.trans et.symm)
    · exact hgt (eg.trans et.symm)
    · exact hgp (eg.trans ep.symm)
    · exact hgp (eg.trans ep.symm)
