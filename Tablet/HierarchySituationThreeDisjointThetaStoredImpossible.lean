import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationThreeDisjointData
import Tablet.HierarchySituationThreeEligibleIndexBound
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceSuffix
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
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: HierarchySituationThreeDisjointThetaStoredImpossible]
theorem HierarchySituationThreeDisjointThetaStoredImpossible
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : forall (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu -> IsOneEdgeUncolored mu e0 ->
        forall v : V, (MissingColors G mu v).Nonempty)
    (d : HierarchySituationThreeDisjointData
      G k e0 input T phi ett base C ctx P alpha beta)
    (hthetaStored :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      d.theta ∈ HierarchyStoredColorsAt H q) : False := by
-- BODY
  as_aux_lemma =>
    classical
    generalize hj : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper
    let R := d.switched
    let sigma := R.coloring
    let H := R.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := HierarchyFullTailLength C
    let X := HierarchyFullTailPrefix C (j - 1)
    let B := HierarchyFullTailPrefix C (j - 2)
    let Y := HierarchyFullTailPrefix C j
    let Z := HierarchyFullTailPrefix C (ell - 1)
    let D := HierarchyStoredColorsAt H q
    have hthetaStored' : d.theta ∈ D := hthetaStored
    have hbetaB : beta ∈ TreeMissingColors sigma B := by
      simpa only [B, sigma, R, hj] using d.betaMissingTwoBefore
    have hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        t.val < A.length + j → sigma (T.edge t) ≠ some beta := by
      as_aux_lemma =>
        have hc := d.conditionNine
        rw [hj] at hc
        change (beta ∉ _ ∧ beta ∉ _ ∧ beta ∉ _ ∧ beta ∉ D) ∨
          (beta ∈ D ∧ beta ∈ TreeMissingColors sigma B ∧
            Disjoint (R.counterexample.good.gamma q beta ∪ {beta})
              (Finset.univ.filter fun c => ∃ t : Fin T.length,
                A.length ≤ t.val ∧ t.val < A.length + j ∧
                  sigma (T.edge t) = some c)) at hc
        intro t hlo hhi he
        have hm : beta ∈ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < A.length + j ∧ sigma (T.edge t) = some c) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi, he⟩
        rcases hc with hc | hc
        · exact hc.2.1 hm
        · exact Finset.disjoint_left.mp hc.2.2 (by simp) hm
    have hthetaMissingY : d.theta ∈ MissingColors G sigma
        (Y.vertex (Fin.last Y.length)) := by
      have ht := d.thetaMissingAtJ
      change d.theta ∈ MissingColors G d.switched.coloring
        ((HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).vertex
          (Fin.last (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).length)) at ht
      rw [hj] at ht
      exact ht
    obtain ⟨gamma, gamma₂, hgammaNe₂, hgammaPair⟩ :=
      Finset.card_eq_two.mp (R.counterexample.good.twoColors q d.theta hthetaStored')
    have hgammaTheta : gamma ∈ R.counterexample.good.gamma q d.theta := by
      rw [hgammaPair]
      simp
    have hgammaA : gamma ∈ TreeMissingColors sigma A :=
      (GoodHierarchyReservedDisjoint R.counterexample.good q).1 d.theta hthetaStored'
        hgammaTheta
    have hgammaInGammaUnion : gamma ∈ D.biUnion (R.counterexample.good.gamma q) :=
      Finset.mem_biUnion.mpr ⟨d.theta, hthetaStored', hgammaTheta⟩
    have hgammaNeBeta : gamma ≠ beta := by
      intro heq
      exact d.betaOutsideGamma (heq ▸ hgammaInGammaUnion)
    have sameStar : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A := by
      as_aux_lemma =>
        clear * - G e0 base C R H q A
        have helper : ∀ (n m : ℕ) (X Y : TreeSequence G e0)
            (s : Fin (n + 2) → TreeSequence G e0)
            (t : Fin (m + 2) → TreeSequence G e0), n = m → X = Y → HEq s t →
            Fin.cases (motive := fun _ => TreeSequence G e0)
              X (fun i : Fin n => s i.succ.castSucc) (Fin.last n) =
            Fin.cases (motive := fun _ => TreeSequence G e0)
              Y (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
          intro n m X Y s t hnm hXY hst
          subst m
          have hs : s = t := eq_of_heq hst
          simp [hXY, hs]
        simpa [A, q, HierarchyStarredStage] using (helper _ _ base.core R.replacementBase.core C.hierarchy.stage
          H.stage R.sameGood.1.2.1 R.sameGood.1.1
          R.sameGood.1.2.2.1)
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun t => H.nested t.succ) i
    have hAtoT : TreeSequenceInitialSegment A T := by
      simpa only [q, Fin.succ_last, H.terminalStage] using starNext q
    have htail : j ≤ T.length - A.length := by
      have h := hpathUpper
      simpa [ell, HierarchyFullTailLength, sameStar] using Nat.le_of_lt h
    have hjLower : 2 ≤ j := hpathLower
    have hjUpper : j < ell := hpathUpper
    have hcutJ : A.length + j ≤ T.length := by
      have hAT := hAtoT.1
      clear * - htail hAT
      clear_value A
      omega
    have hcutJstrict : A.length + j < T.length := by
      have hj : j < T.length - A.length := by
        simpa only [ell, HierarchyFullTailLength, sameStar] using hjUpper
      have hAT := hAtoT.1
      clear * - hj hAT
      clear_value A
      omega
    have fullPrefixEq (m : ℕ) : HierarchyFullTailPrefix C m =
        TreeSequencePrefix T (min (A.length + m) T.length)
          (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (Nat.min_le_right _ _) := by
      unfold HierarchyFullTailPrefix
      simp only [sameStar]
    have prefixToTree (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T.length) :
        TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
      as_aux_lemma =>
        clear * - m hm hmT T
        refine ⟨hmT, ?_, ?_⟩
        · intro i
          simp [TreeSequencePrefix]
        · intro i
          simp [TreeSequencePrefix]
    have commonPrefix {U W : TreeSequence G e0}
        (hUT : TreeSequenceInitialSegment U T)
        (hWT : TreeSequenceInitialSegment W T) (hUW : U.length ≤ W.length) :
        TreeSequenceInitialSegment U W := by
      as_aux_lemma =>
        clear * - hUT hWT hUW
        rcases hUT with ⟨hu, huv, hue⟩
        rcases hWT with ⟨hw, hwv, hwe⟩
        refine ⟨hUW, ?_, ?_⟩
        · intro i
          calc
            W.vertex (Fin.castLE (Nat.succ_le_succ hUW) i) =
                T.vertex (Fin.castLE (Nat.succ_le_succ hw)
                  (Fin.castLE (Nat.succ_le_succ hUW) i)) := (hwv _).symm
            _ = T.vertex (Fin.castLE (Nat.succ_le_succ hu) i) := by congr 1
            _ = U.vertex i := huv i
        · intro i
          calc
            W.edge (Fin.castLE hUW i) = T.edge (Fin.castLE hw (Fin.castLE hUW i)) :=
              (hwe _).symm
            _ = T.edge (Fin.castLE hu i) := by congr 1
            _ = U.edge i := hue i
    have hYlen : Y.length = A.length + j := by
      change (HierarchyFullTailPrefix C j).length = A.length + j
      rw [fullPrefixEq j]
      simp only [TreeSequencePrefix, min_eq_left hcutJ]
    have hBtoT : TreeSequenceInitialSegment B T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 2)) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hXtoT : TreeSequenceInitialSegment X T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 1)) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hYtoT : TreeSequenceInitialSegment Y T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C j) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hBtoX : TreeSequenceInitialSegment B X :=
      commonPrefix hBtoT hXtoT (by
        change (HierarchyFullTailPrefix C (j - 2)).length ≤
          (HierarchyFullTailPrefix C (j - 1)).length
        rw [fullPrefixEq (j - 2), fullPrefixEq (j - 1)]
        simp only [TreeSequencePrefix]
        exact min_le_min_right _ (Nat.add_le_add_left (Nat.sub_le_sub_left (by decide) j) _))
    have hXtoY : TreeSequenceInitialSegment X Y :=
      commonPrefix hXtoT hYtoT (by
        change (HierarchyFullTailPrefix C (j - 1)).length ≤
          (HierarchyFullTailPrefix C j).length
        rw [fullPrefixEq (j - 1), fullPrefixEq j]
        simp only [TreeSequencePrefix]
        exact min_le_min_right _ (Nat.add_le_add_left (Nat.sub_le j 1) _))
    have hYtoZ : TreeSequenceInitialSegment Y Z :=
      commonPrefix hYtoT (by
        change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (ell - 1)) T
        rw [fullPrefixEq]
        exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (min_le_right _ _))
        (by
          change (HierarchyFullTailPrefix C j).length ≤
            (HierarchyFullTailPrefix C (ell - 1)).length
          rw [fullPrefixEq j, fullPrefixEq (ell - 1)]
          simp only [TreeSequencePrefix]
          exact min_le_min_right _ (Nat.add_le_add_left (Nat.le_sub_one_of_lt hjUpper) _))
    have hZtoT : TreeSequenceInitialSegment Z T :=
      by
        change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (ell - 1)) T
        rw [fullPrefixEq]
        exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (min_le_right _ _)
    have hAtoY : TreeSequenceInitialSegment A Y :=
      commonPrefix hAtoT hYtoT (by rw [hYlen]; exact Nat.le_add_right _ _)
    have hAtoB : TreeSequenceInitialSegment A B :=
      commonPrefix hAtoT hBtoT (by
        change A.length ≤ (HierarchyFullTailPrefix C (j - 2)).length
        rw [fullPrefixEq]
        simp only [TreeSequencePrefix]
        exact le_min (Nat.le_add_right _ _) hAtoT.1)
    have penultimatePrefixEq : HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1) = Z := by
      simp only [Z, ell, HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar]
      rfl
    have hElemZ : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z) := by
      as_aux_lemma =>
        clear * - G k e0 T R sigma Z penultimatePrefixEq
        have hp : ColoredVertexSetElementary G sigma
            (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
              (HierarchyFullTailLength R.counterexample - 1))) :=
          HierarchyCounterexamplePenultimateElementary G k e0
            R.corresponding.replacementInput T sigma R.corresponding.replacementETT
            R.replacementBase R.counterexample R.minimumContext.proper
            R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
            R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
            R.minimumContext.largeMissingSet
        intro u hu v hv huv
        apply hp
        · rw [penultimatePrefixEq]; exact hu
        · rw [penultimatePrefixEq]; exact hv
        · exact huv
    have firstWitness (rho : PartialEdgeColoring E k) (W : TreeSequence G e0)
        (hWT : TreeSequenceInitialSegment W T) (c : Fin k)
        (hc : c ∈ TreeMissingColors rho W) :
        c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
          (HierarchyFirstMissingPosition rho T c).val ≤ W.length := by
      as_aux_lemma =>
        clear * - G T rho W hWT c hc
        rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and] at hv
        rcases hv with ⟨i, rfl⟩
        let candidates := Finset.univ.filter fun a : Fin (T.length + 1) =>
          c ∈ MissingColors G rho (T.vertex a)
        have hi : Fin.castLE (Nat.succ_le_succ hWT.1) i ∈ candidates := by
          simp [candidates, hWT.2.1 i, hcv]
        have hn : candidates.Nonempty := ⟨_, hi⟩
        have hmin := Finset.min'_le candidates _ hi
        have hmiss : c ∈ MissingColors G rho (T.vertex (candidates.min' hn)) :=
          (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
        have hpos : HierarchyFirstMissingPosition rho T c = candidates.min' hn := by
          simp [HierarchyFirstMissingPosition, candidates, hn]
        constructor
        · simpa [HierarchyFirstMissingPosition, candidates, hn] using hmiss
        · rw [hpos]
          have hle : (candidates.min' hn).val ≤ i.val := by
            change (candidates.min' hn).val ≤ (Fin.castLE (Nat.succ_le_succ hWT.1) i).val at hmin
            simpa using hmin
          exact le_trans hle (Nat.le_of_lt_succ i.isLt)
    have hgammaFirst := firstWitness sigma A hAtoT gamma hgammaA
    have hbetaFirst := firstWitness sigma B hBtoT beta hbetaB
    have hgammaFirstLe : (HierarchyFirstMissingPosition sigma T gamma).val ≤ A.length :=
      hgammaFirst.2
    have hbetaFirstLe : (HierarchyFirstMissingPosition sigma T beta).val ≤ B.length :=
      hbetaFirst.2
    have vertexMemT (W : TreeSequence G e0) (hWT : TreeSequenceInitialSegment W T)
        (i : Fin (T.length + 1)) (hi : i.val ≤ W.length) :
        T.vertex i ∈ TreeSequenceVertexSet W := by
      as_aux_lemma =>
        clear * - G T W hWT i hi
        let jW : Fin (W.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
        have hcast : Fin.castLE (Nat.succ_le_succ hWT.1) jW = i := Fin.ext rfl
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨jW, ?_⟩
        rw [← hWT.2.1 jW, hcast]
    have vertexMemSelf (W : TreeSequence G e0) (i : Fin (W.length + 1)) :
        W.vertex i ∈ TreeSequenceVertexSet W := by
      as_aux_lemma =>
        clear * - W i
        simp [TreeSequenceVertexSet]
    have treeMissingIntro (rho : PartialEdgeColoring E k) (W : TreeSequence G e0)
        (v : V) (c : Fin k) (hv : v ∈ TreeSequenceVertexSet W)
        (hc : c ∈ MissingColors G rho v) : c ∈ TreeMissingColors rho W := by
      as_aux_lemma =>
        clear * - rho W v c hv hc
        exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    have hthetaY : d.theta ∈ TreeMissingColors sigma Y := by
      as_aux_lemma =>
        clear * - G sigma Y d hthetaMissingY vertexMemSelf treeMissingIntro
        clear_value Y
        exact treeMissingIntro sigma Y (Y.vertex (Fin.last Y.length)) d.theta
          (vertexMemSelf Y (Fin.last Y.length)) hthetaMissingY
    have hthetaFirst : d.theta ∈ MissingColors G sigma
          (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
        (HierarchyFirstMissingPosition sigma T d.theta).val ≤ Y.length := by
      as_aux_lemma =>
        clear * - G T sigma Y d hYtoT hthetaY firstWitness
        clear_value Y
        exact firstWitness sigma Y hYtoT d.theta hthetaY
    have hthetaFirstIndex : (HierarchyFirstMissingPosition sigma T d.theta).val = Y.length := by
      as_aux_lemma =>
        clear * - G T sigma d Y Z hthetaFirst hYtoT hYtoZ hZtoT hElemZ hthetaMissingY vertexMemT
        clear_value Y Z
        apply Nat.le_antisymm hthetaFirst.2
        by_contra hne
        have hlt : (HierarchyFirstMissingPosition sigma T d.theta).val < Y.length :=
          Nat.lt_of_not_ge hne
        have iZ : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ∈
            TreeSequenceVertexSet Z := vertexMemT Z hZtoT
              (HierarchyFirstMissingPosition sigma T d.theta)
              (Nat.le_trans (Nat.le_of_lt hlt) hYtoZ.1)
        have yZ : Y.vertex (Fin.last Y.length) ∈ TreeSequenceVertexSet Z :=
          TreeSequenceInitialSegmentVertexSetSubset hYtoZ
            (by simp [TreeSequenceVertexSet])
        have hvne : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠
            Y.vertex (Fin.last Y.length) := by
          intro heq
          let jY : Fin (Y.length + 1) :=
            ⟨(HierarchyFirstMissingPosition sigma T d.theta).val,
              Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩
          have hcast : Fin.castLE (Nat.succ_le_succ hYtoT.1) jY =
              HierarchyFirstMissingPosition sigma T d.theta := Fin.ext rfl
          have heqY : Y.vertex jY = Y.vertex (Fin.last Y.length) := by
            have htree := hYtoT.2.1 jY
            have hcastV := congrArg T.vertex hcast
            exact htree.symm.trans (hcastV.trans heq)
          have hidx := Y.vertex_injective heqY
          have hval := congrArg Fin.val hidx
          dsimp [jY] at hval
          exact (Nat.ne_of_lt hlt) hval
        exact Finset.disjoint_left.mp (hElemZ iZ yZ hvne)
          hthetaFirst.1 hthetaMissingY
    have hthetaOutsideGamma : d.theta ∉ D.biUnion (R.counterexample.good.gamma q) := by
      simpa [R, H, q, D] using d.thetaOutsideGamma
    have hgammaNeTheta : gamma ≠ d.theta := by
      intro heq
      exact hthetaOutsideGamma (heq ▸ hgammaInGammaUnion)
    have hgammaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        t.val < Y.length → sigma (T.edge t) ≠ some gamma := by
      as_aux_lemma =>
        have havoid : gamma ∉ HierarchySegmentColors H q d.theta :=
          (Finset.mem_sdiff.mp
            (R.counterexample.good.avoidance q d.theta hthetaStored' hgammaTheta)).2
        have hterminal : H.stage q.succ = T := by
          simpa only [q, Fin.succ_last] using H.terminalStage
        unfold HierarchySegmentColors at havoid
        dsimp only at havoid
        rw [hterminal, hthetaFirstIndex] at havoid
        intro t hlo hhi hc
        exact havoid (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, t, hlo, Nat.lt_min.mpr ⟨hhi, t.isLt⟩, hc⟩)
    have horderedUnusedGammaBeta :
        (gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A) →
          TreeVertexOrder T
              (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
              (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
            gamma ∉ (Finset.univ.filter fun c =>
              ∃ t : Fin T.length,
                A.length ≤ t.val ∧
                  t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
                    sigma (T.edge t) = some c) := by
      as_aux_lemma =>
        intro h
        rcases h with h | h
        · exact (h hgammaA).elim
        · have hafter : A.length < (HierarchyFirstMissingPosition sigma T beta).val := by
            by_contra hh
            have hb := vertexMemT A hAtoT (HierarchyFirstMissingPosition sigma T beta)
              (Nat.le_of_not_gt hh)
            exact h (treeMissingIntro sigma A _ beta hb hbetaFirst.1)
          refine ⟨⟨_, _, rfl, rfl, hgammaFirstLe.trans_lt hafter⟩, ?_⟩
          intro hc
          obtain ⟨_, t, hlo, hhi, he⟩ := Finset.mem_filter.mp hc
          exact hgammaUnused t hlo
            (hhi.trans_le (hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1))) he
    have hAtoZ : TreeSequenceInitialSegment A Z :=
      commonPrefix hAtoT hZtoT (hAtoY.1.trans hYtoZ.1)
    have hBtoZ : TreeSequenceInitialSegment B Z :=
      commonPrefix hBtoT hZtoT (hBtoX.1.trans (hXtoY.1.trans hYtoZ.1))
    have treeMissingSubset {U W : TreeSequence G e0}
        (hUW : TreeSequenceInitialSegment U W) :
        TreeMissingColors sigma U ⊆ TreeMissingColors sigma W := by
      as_aux_lemma =>
        clear * - G sigma hUW
        intro c hc
        obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hc
        exact Finset.mem_biUnion.mpr ⟨v,
          TreeSequenceInitialSegmentVertexSetSubset hUW hv, hmiss⟩
    have hgammaMissingZ : gamma ∈ TreeMissingColors sigma Z :=
      treeMissingSubset hAtoZ hgammaA
    have hbetaMissingZ : beta ∈ TreeMissingColors sigma Z :=
      treeMissingSubset hBtoZ hbetaB
    have htailSame : HierarchyFullTailLength R.counterexample = ell := by
      change T.length - A.length =
        T.length - (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length
      rw [← sameStar]
    have hEll : ell = T.length - A.length := by
      simp [ell, HierarchyFullTailLength, sameStar]
    have hstarR : HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = A := rfl
    have hchangeElementary :
        ColoredVertexSetElementary G sigma
          (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - 1))) := by
      rw [penultimatePrefixEq]
      exact hElemZ
    have hchangeMissing : gamma ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1)) ∧
        beta ∈ TreeMissingColors sigma
          (HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - 1)) := by
      rw [penultimatePrefixEq]
      exact ⟨hgammaMissingZ, hbetaMissingZ⟩
    have firstChange := by
      as_aux_lemma =>
        clear * - G k e0 T R sigma gamma beta hgammaNeBeta hchangeElementary
          hchangeMissing horderedUnusedGammaBeta sameStar
        exact ChangeLemma G k e0 R.corresponding.replacementInput T sigma
          R.corresponding.replacementETT R.replacementBase R.counterexample
          R.minimumContext.proper R.minimumContext.oneEdgeUncolored
          R.minimumContext.lowerRung R.minimumContext.fewerDividers
          R.minimumContext.lexicographicMinimality hchangeElementary
          R.minimumContext.largeMissingSet gamma beta hgammaNeBeta hchangeMissing
          (by
            change (gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A) →
              TreeVertexOrder T
                  (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
                  (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
                gamma ∉ (Finset.univ.filter fun c =>
                  ∃ t : Fin T.length, A.length ≤ t.val ∧
                    t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
                      sigma (T.edge t) = some c)
            exact horderedUnusedGammaBeta)
    have hgammaStageMissing : gamma ∈ HierarchyStageMissingColors H q :=
      (Finset.mem_sdiff.mp
        (R.counterexample.good.avoidance q d.theta hthetaStored' hgammaTheta)).1
    have hApositive (hq : 0 < H.dividerCount) :
        A = H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ := by
      as_aux_lemma =>
        clear * - H q A hq
        have hlast : q =
            (⟨H.dividerCount - 1, Nat.sub_lt hq (by decide)⟩ : Fin H.dividerCount).succ := by
          apply Fin.ext
          change H.dividerCount = H.dividerCount - 1 + 1
          exact (Nat.sub_add_cancel hq).symm
        change HierarchyStarredStage H q = _
        rw [hlast]
        change H.stage _ = H.stage _
        congr 1
        apply Fin.ext
        change H.dividerCount - 1 + 1 = H.dividerCount
        exact Nat.sub_add_cancel hq
    have sameGammaBeta :
        TwoColorComponent G sigma gamma beta
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
          TwoColorComponent G sigma gamma beta
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) := by
      by_cases hzero : H.dividerCount = 0
      · have hgammaRaw : gamma ∈ TreeMissingColors sigma
          (R.corresponding.replacementETT.series.data.tree
            (Fin.last R.corresponding.replacementETT.rounds).castSucc) := by
          have hq0 : q = 0 := by
            apply Fin.ext
            simp [q, hzero]
          rw [hq0] at hgammaStageMissing
          simpa [HierarchyStageMissingColors] using hgammaStageMissing
        exact firstChange.2.1 ⟨hzero, Or.inl hgammaRaw⟩
      · have hgammaLast : gamma ∈ TreeMissingColors sigma
          (H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩) := by
          have hstar : A = H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ :=
            hApositive (Nat.pos_of_ne_zero hzero)
          rw [← hstar]
          exact hgammaA
        exact firstChange.1 ⟨Nat.pos_of_ne_zero hzero, Or.inl hgammaLast⟩
    have componentSelf (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
        Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by rfl
    have hgammaTerminalDistinct :
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
          T.vertex (Fin.last T.length) := by
      intro he
      have hv := congrArg Fin.val (T.vertex_injective he)
      simp only [Fin.val_last] at hv
      have hlt : A.length < T.length := (Nat.le_add_right A.length j).trans_lt hcutJstrict
      exact Nat.ne_of_lt (hgammaFirstLe.trans_lt hlt) hv
    have hbetaTerminalDistinct :
        T.vertex (HierarchyFirstMissingPosition sigma T beta) ≠
          T.vertex (Fin.last T.length) := by
      intro he
      have hv := congrArg Fin.val (T.vertex_injective he)
      simp only [Fin.val_last] at hv
      have hlt : Y.length < T.length := hYlen.symm ▸ hcutJstrict
      exact Nat.ne_of_lt
        ((hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1)).trans_lt hlt) hv
    have separation1 := P2905_T2_ElementaryTerminalComponent G sigma gamma beta
      hgammaNeBeta R.minimumContext.proper (TreeSequenceVertexSet Z) hElemZ
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
      (T.vertex (HierarchyFirstMissingPosition sigma T beta))
      (T.vertex (Fin.last T.length))
      (vertexMemT Z hZtoT _ (hgammaFirstLe.trans hAtoZ.1))
      (vertexMemT Z hZtoT _ (hbetaFirstLe.trans hBtoZ.1))
      hgammaTerminalDistinct.symm hbetaTerminalDistinct.symm
      hgammaFirst.1 hbetaFirst.1 (Or.inr d.betaMissingTerminal) sameGammaBeta
    have hterminalDisjoint := separation1.1
    let z : Sum V E := Sum.inl (T.vertex (Fin.last T.length))
    let mu2 := TwoColorComponentSwap G sigma gamma beta z
    have hmu2Proper : IsProperEdgeColoring G mu2 := by
      exact TwoColorComponentSwapProper G sigma gamma beta hgammaNeBeta
        R.minimumContext.proper z
    have hmu2One : IsOneEdgeUncolored mu2 e0 := by
      as_aux_lemma =>
        constructor
        · have he0 : sigma e0 = none := R.minimumContext.oneEdgeUncolored.1
          simp [mu2, TwoColorComponentSwap, he0]
        · intro e he0
          obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 e he0
          by_cases heK : Sum.inr e ∈ TwoColorComponent G sigma gamma beta z
          · by_cases heGamma : sigma e = some gamma
            · exact ⟨beta, by simp [mu2, TwoColorComponentSwap, heK, heGamma]
              ⟩
            · by_cases heBeta : sigma e = some beta
              · exact ⟨gamma, by
                  simp [mu2, TwoColorComponentSwap, heK, heGamma, heBeta,
                    hgammaNeBeta]
                ⟩
              · exact ⟨c, by
                  simpa [mu2, TwoColorComponentSwap, heK, heGamma, heBeta] using hc⟩
          · exact ⟨c, by simpa [mu2, TwoColorComponentSwap, heK] using hc⟩
    have hfirstGammaOutside : Sum.inl
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∉
          TwoColorComponent G sigma gamma beta z := by
      intro hv
      exact (Set.disjoint_left.mp hterminalDisjoint) hv
        (componentSelf sigma gamma beta
          (T.vertex (HierarchyFirstMissingPosition sigma T gamma)))
    have hfirstBetaOutside : Sum.inl
        (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∉
          TwoColorComponent G sigma gamma beta z := by
      intro hv
      have hv' : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∈
        TwoColorComponent G sigma gamma beta
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) := by
        rw [sameGammaBeta]
        exact componentSelf sigma gamma beta
          (T.vertex (HierarchyFirstMissingPosition sigma T beta))
      exact (Set.disjoint_left.mp hterminalDisjoint) hv hv'
    have hswapBehavior := TwoColorComponentSwapMissingBehavior G sigma gamma beta
      hgammaNeBeta R.minimumContext.proper z
    have hgammaFirstMu2 : gamma ∈ MissingColors G mu2
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) := by
      rw [(hswapBehavior.1 _ hfirstGammaOutside)]
      exact hgammaFirst.1
    have hbetaFirstMu2 : beta ∈ MissingColors G mu2
        (T.vertex (HierarchyFirstMissingPosition sigma T beta)) := by
      rw [(hswapBehavior.1 _ hfirstBetaOutside)]
      exact hbetaFirst.1
    have hgammaTerminalMu2 : gamma ∈ MissingColors G mu2
        (T.vertex (Fin.last T.length)) := by
      exact hswapBehavior.2.2.1 _ (componentSelf sigma gamma beta
        (T.vertex (Fin.last T.length))) d.betaMissingTerminal
    have hfixedThroughY : ∀ t : Fin T.length, A.length ≤ t.val →
        t.val < A.length + j → mu2 (T.edge t) = sigma (T.edge t) := by
      as_aux_lemma =>
        intro t hlo hhi
        have hga := hgammaUnused t hlo (hYlen.symm ▸ hhi)
        have hbe := hbetaUnused t hlo hhi
        simp only [mu2, TwoColorComponentSwap, hga, hbe, if_false, ite_self]
    have firstPreserved (W : TreeSequence G e0)
        (hWT : TreeSequenceInitialSegment W T) (rho sigma : PartialEdgeColoring E k) (c : Fin k)
        (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet W))
        (hmiss : ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v)
        (hc : c ∈ TreeMissingColors rho W) :
        HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
      as_aux_lemma =>
        clear * - G T W rho sigma c helem hmiss hc firstWitness hWT
        have hr := firstWitness rho W hWT c hc
        have hc' : c ∈ TreeMissingColors sigma W := by
          obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
          exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
        have hs := firstWitness sigma W hWT c hc'
        have pref (i : Fin (T.length + 1)) (hi : i.val ≤ W.length) :
            T.vertex i ∈ TreeSequenceVertexSet W := by
          let j : Fin (W.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
          have he : Fin.castLE (Nat.succ_le_succ hWT.1) j = i := Fin.ext rfl
          exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
            ⟨j, Finset.mem_univ _, (hWT.2.1 j).symm.trans (congrArg T.vertex he)⟩
        by_contra hne
        have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
            T.vertex (HierarchyFirstMissingPosition rho T c) :=
          fun he => hne (T.vertex_injective he)
        have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
        exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1
    have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
        (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
        HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
          HierarchyFirstMissingPosition rho T c := by
      clear * - G T z rho a b c hne hp hca hcb
      have hb := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
      have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
          c ∈ MissingColors G (TwoColorComponentSwap G rho a b z) (T.vertex i)) =
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            c ∈ MissingColors G rho (T.vertex i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb.2.2.2 _ c hca hcb
      unfold HierarchyFirstMissingPosition
      rw [he]
    have hmissingMu2 : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G mu2 v = MissingColors G sigma v := separation1.2.2
    have missingTransport (old new : PartialEdgeColoring E k)
        (hm : ∀ v ∈ TreeSequenceVertexSet Z,
          MissingColors G new v = MissingColors G old v)
        (W : TreeSequence G e0) (hWZ : TreeSequenceInitialSegment W Z) :
        TreeMissingColors new W = TreeMissingColors old W := by
      as_aux_lemma =>
        clear_value Z
        clear * - old new hm W hWZ Z
        unfold TreeMissingColors
        exact Finset.biUnion_congr rfl (fun v hv =>
          hm v (TreeSequenceInitialSegmentVertexSetSubset hWZ hv))
    have hstoredMu2 : ∀ eta ∈ D,
        HierarchyFirstMissingPosition mu2 T eta =
          HierarchyFirstMissingPosition sigma T eta := by
      intro eta heta
      have hneGamma : eta ≠ gamma := by
        intro he
        exact (Finset.mem_sdiff.mp heta).2 (he.symm ▸ hgammaA)
      by_cases he : eta = beta
      · subst eta
        exact firstPreserved Z hZtoT sigma mu2 beta hElemZ hmissingMu2 hbetaMissingZ
      · exact firstUnaffected z sigma gamma beta eta hgammaNeBeta
          R.minimumContext.proper hneGamma he
    have hgammaCutoff : ∀ eta ∈ D,
        (gamma ∈ R.counterexample.good.gamma q eta ∨
          beta ∈ R.counterexample.good.gamma q eta) →
        (HierarchyFirstMissingPosition sigma T eta).val ≤ Y.length := by
      intro eta heta hmem
      have he : eta = d.theta := by
        by_contra hne
        rcases hmem with hg | hb
        · exact Finset.disjoint_left.mp
            (R.counterexample.good.disjointPairs q eta d.theta heta hthetaStored' hne)
            hg hgammaTheta
        · exact d.betaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hb⟩)
      subst eta
      exact hthetaFirst.2
    have originalStar (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount) := by
      as_aux_lemma =>
        clear * - G e0 C S base
        have helper : ∀ (n m : ℕ) (U W : TreeSequence G e0)
            (s : Fin (n + 2) → TreeSequence G e0)
            (t : Fin (m + 2) → TreeSequence G e0),
            n = m → U = W → HEq s t →
            Fin.cases (motive := fun _ => TreeSequence G e0)
              U (fun i : Fin n => s i.succ.castSucc) (Fin.last n) =
            Fin.cases (motive := fun _ => TreeSequence G e0)
              W (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
          intro n m U W s t hnm hUW hst
          subst m
          have he : s = t := eq_of_heq hst
          simp only [hUW, he]
        exact helper _ _ _ _ _ _ S.sameGood.1.2.1 S.sameGood.1.1 S.sameGood.1.2.2.1
    have sameStarAll (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) = A :=
      (originalStar S).symm.trans sameStar
    have samePenultimate (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        HierarchyFullTailPrefix S.counterexample
          (HierarchyFullTailLength S.counterexample - 1) = Z := by
      simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStarAll S]
      simp only [Z, ell, HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar]
    have lastData (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
          C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
            S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
      as_aux_lemma =>
        clear * - C S
        obtain ⟨hc, hd⟩ := S.sameGood.2
        have hi : Fin.cast (congrArg (fun n => n + 1) hc)
            (Fin.last C.hierarchy.dividerCount) =
              Fin.last S.counterexample.hierarchy.dividerCount := Fin.ext hc
        simpa only [hi] using hd (Fin.last C.hierarchy.dividerCount)
    have sameLast (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        D = HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ D, R.counterexample.good.gamma q eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
      refine ⟨(lastData R).1.symm.trans (lastData S).1, ?_⟩
      intro eta heta
      have hc : eta ∈ HierarchyStoredColorsAt C.hierarchy
          (Fin.last C.hierarchy.dividerCount) := (lastData R).1.symm ▸ heta
      exact ((lastData R).2 eta hc).symm.trans ((lastData S).2 eta hc)
    have weakEdges {input' : PartialEdgeColoring E k}
        (old new : PartialEdgeColoring E k)
        (et : ExtendedTashkinovTree G k e0 input' T old)
        (bs : HierarchyBase et old) (K : TashkinovHierarchy et bs)
        (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
        (ho : IsOneEdgeUncolored old e0) (hn : IsOneEdgeUncolored new e0) :
        ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
          new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
            old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
      as_aux_lemma =>
        clear * - G k e0 input' T old new et bs K hw ho hn
        by_cases hz : K.dividerCount = 0
        · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
          rw [hi] at hw ⊢
          exact P2813_T1_BaseDisplayedEdges G k e0 input' T old et bs new ho hn hw
        · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
              (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
            Fin.ext (by simp only [Fin.val_last, Fin.val_succ, Fin.val_mk]; omega)
          rw [hi] at hw ⊢
          intro t
          by_cases ht : 1 ≤ t.val
          · exact hw.2.1 t ht
          · let W := HierarchyStarredStage K
              (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ
            have he : t = ⟨0, W.positive⟩ := Fin.ext (by change t.val = 0; omega)
            rw [he, W.first_edge, hn.1, ho.1]
    have hXYlen : Y.length = X.length + 1 := by
      change (HierarchyFullTailPrefix C j).length =
        (HierarchyFullTailPrefix C (j - 1)).length + 1
      rw [fullPrefixEq j, fullPrefixEq (j - 1)]
      simp only [TreeSequencePrefix]
      have hj : 2 ≤ j := hpathLower
      have hl : A.length + j ≤ T.length := by
        have hAT := hAtoT.1
        clear * - htail hAT
        omega
      clear * - hj hl
      omega
    have routeToY (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) (nu : PartialEdgeColoring E k)
        (hn : IsOneEdgeUncolored nu e0)
        (hw : HierarchyWeaklyStable S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) nu)
        (hf : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
          nu (T.edge t) = S.coloring (T.edge t))
        (hm : ∀ v ∈ TreeSequenceVertexSet Z,
          MissingColors G nu v = MissingColors G S.coloring v) :
        let et := S.corresponding.replacementETT
        let n := Fin.last et.rounds
        let Tn := et.series.data.tree n.castSucc
        (et.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence nu Tn Y) ∨
        ((et.series.data.kind n = some TashkinovExtensionKind.SE ∨
          et.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            et.series.data.connectingEdges n = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
            TashkinovAugmentationSequence nu seed Y) := by
      as_aux_lemma =>
        have hj : 2 ≤ j := hpathLower
        clear * - G k e0 input T phi ett base C ctx S nu hn hw hf hm
          A X Y Z hAtoT hYtoT hXtoY hYtoZ hXYlen hAtoY hYlen hj j sameStarAll
          commonPrefix weakEdges
        clear_value A X Y Z
        let et := S.corresponding.replacementETT
        let K := S.counterexample.hierarchy
        let Tn := et.series.data.tree (Fin.last et.rounds).castSucc
        have hTnT : TreeSequenceInitialSegment Tn T := et.abovePenultimate
        have hTnA : Tn.length ≤ A.length := by
          by_cases hz : K.dividerCount = 0
          · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
            have hs := sameStarAll S
            change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
            rw [hi] at hs
            change S.replacementBase.core = A at hs
            by_cases hp : et.series.data.kind (Fin.last et.rounds) =
                some TashkinovExtensionKind.PE
            · rw [← hs]; exact (Classical.choice (S.replacementBase.parallel hp).2.2).leftSegment.1
            · rw [← hs, S.replacementBase.nonparallel hp]
          · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
                (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
              Fin.ext (by simp only [Fin.val_last, Fin.val_succ, Fin.val_mk]; omega)
            have hs := sameStarAll S
            change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
            rw [hi] at hs
            have hmono : Monotone (fun i : Fin (K.dividerCount + 2) => (K.stage i).length) :=
              Fin.monotone_iff_le_succ.mpr (fun i => (K.nested i).1)
            rw [← hs]
            change Tn.length ≤ (K.stage _).length
            rw [show Tn = K.stage 0 from K.baseStage.symm]
            exact hmono (Fin.zero_le _)
        have hAYstrict : A.length < Y.length := by
          clear * - hj hYlen
          omega
        have fixedA : ∀ t : Fin A.length, nu (A.edge t) = S.coloring (A.edge t) := by
          have he := weakEdges S.coloring nu et S.replacementBase K hw
            S.minimumContext.oneEdgeUncolored hn
          change ∀ t : Fin (HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount)).length,
              nu ((HierarchyStarredStage S.counterexample.hierarchy
                (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) =
              S.coloring ((HierarchyStarredStage S.counterexample.hierarchy
                (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) at he
          rw [sameStarAll S] at he
          exact he
        have fixedY : ∀ t : Fin Y.length, nu (Y.edge t) = S.coloring (Y.edge t) := by
          intro t
          let tT : Fin T.length := Fin.castLE hYtoT.1 t
          have he : T.edge tT = Y.edge t := hYtoT.2.2 t
          by_cases ht : t.val < A.length
          · let tA : Fin A.length := ⟨t.val, ht⟩
            have hcast : Fin.castLE hAtoT.1 tA = tT := Fin.ext rfl
            rw [← he, ← hcast, hAtoT.2.2 tA]
            exact fixedA tA
          · rw [← he]
            exact hf tT (Nat.le_of_not_gt ht) t.isLt
        have transport (W : TreeSequence G e0)
            (hr : TashkinovAugmentationSequence S.coloring W Y) :
            TashkinovAugmentationSequence nu W Y :=
          TashkinovAugmentationSequenceColoringTransport S.coloring nu W X Y hr
            hXtoY hXYlen (fun t _ => fixedY t)
            (fun v hv => hm v (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
              (TreeSequenceInitialSegmentVertexSetSubset hXtoY hv)))
        rcases P2813_T1_TerminalRoute G k e0 S.corresponding.replacementInput T
          S.coloring et with ⟨hp, hr⟩ | ⟨hk, f, seed, he, ha, _, _, hr⟩
        · have hTY : TreeSequenceInitialSegment Tn Y :=
            commonPrefix hTnT hYtoT (hTnA.trans hAtoY.1)
          exact Or.inl ⟨hp, transport Tn
            (TashkinovAugmentationSequenceRestrict S.coloring Tn Y T hr hTY hYtoT)⟩
        · have hseedT : TreeSequenceInitialSegment seed T :=
            TashkinovAugmentationSequenceInitialSegment S.coloring seed T hr
          have hseedY : TreeSequenceInitialSegment seed Y :=
            commonPrefix hseedT hYtoT (by
              have hl := ha.1
              change seed.length = Tn.length + 1 at hl
              clear * - hl hTnA hAYstrict
              omega)
          exact Or.inr ⟨hk, f, seed, he, ha, transport seed
            (TashkinovAugmentationSequenceRestrict S.coloring seed Y T hr hseedY hYtoT)⟩
    have caseGamma (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) :
        (0 < S.counterexample.hierarchy.dividerCount ∧
          gamma ∈ TreeMissingColors S.coloring (S.counterexample.hierarchy.stage
            ⟨S.counterexample.hierarchy.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
        (S.counterexample.hierarchy.dividerCount = 0 ∧
          gamma ∈ TreeMissingColors S.coloring
            (S.corresponding.replacementETT.series.data.tree
              (Fin.last S.corresponding.replacementETT.rounds).castSucc)) := by
      as_aux_lemma =>
        have hs : d.theta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount) := (sameLast S).1 ▸ hthetaStored'
        have hg : gamma ∈ S.counterexample.good.gamma
            (Fin.last S.counterexample.hierarchy.dividerCount) d.theta :=
          (sameLast S).2 d.theta hthetaStored' ▸ hgammaTheta
        have hm := (Finset.mem_sdiff.mp (S.counterexample.good.avoidance _ d.theta hs hg)).1
        clear * - S gamma hm
        let K := S.counterexample.hierarchy
        cases hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) using Fin.cases with
        | zero =>
          have hz : K.dividerCount = 0 := congrArg Fin.val hi
          refine Or.inr ⟨hz, ?_⟩
          change gamma ∈ HierarchyStageMissingColors K (Fin.last K.dividerCount) at hm
          rw [hi] at hm
          exact hm
        | succ i =>
          have hv : K.dividerCount = i.val + 1 := congrArg Fin.val hi
          have hc : i.succ.castSucc =
              (⟨K.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ : Fin (K.dividerCount + 2)) :=
            Fin.ext hv.symm
          refine Or.inl ⟨Nat.lt_of_lt_of_eq (Nat.succ_pos i.val) hv.symm, ?_⟩
          change gamma ∈ HierarchyStageMissingColors K (Fin.last K.dividerCount) at hm
          rw [hi] at hm
          change gamma ∈ TreeMissingColors S.coloring (K.stage i.succ.castSucc) at hm
          rw [hc] at hm
          exact hm
    have hcase1 :
        (0 < H.dividerCount ∧ gamma ∈ TreeMissingColors sigma
          (H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
        (H.dividerCount = 0 ∧
          (gamma ∈ TreeMissingColors sigma
              (R.corresponding.replacementETT.series.data.tree
                (Fin.last R.corresponding.replacementETT.rounds).castSucc) ∨
            (gamma ∈ TreeMissingColors sigma A ∧
              gamma ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
                (Fin.last R.corresponding.replacementETT.rounds) ∧
              beta ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
                (Fin.last R.corresponding.replacementETT.rounds)))) := by
      rcases caseGamma R with h | ⟨hz, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨hz, Or.inl hm⟩
    have hpath1 : TwoColorPathComponent G sigma gamma beta z := separation1.2.1
    have hweak1 : HierarchyWeaklyStable H q mu2 := by
      as_aux_lemma =>
        exact (StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T sigma
          R.corresponding.replacementETT R.replacementBase R.counterexample
          R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
          R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
          hchangeElementary R.minimumContext.largeMissingSet gamma beta hgammaNeBeta
          hchangeMissing z hpath1 mu2 rfl hcase1 hterminalDisjoint).1
    have hsuffixX : TashkinovAugmentationSequence sigma X T := by
      simpa only [X, sigma, R, hj] using d.transportedSuffix
    have hsuffixY : TashkinovAugmentationSequence sigma Y T :=
      TashkinovAugmentationSequenceSuffix sigma X Y T hsuffixX hXtoY hYtoT
    have hsplitMissing2 : gamma ∈ TreeMissingColors mu2 Y ∧ beta ∈ TreeMissingColors mu2 Y := by
      rw [missingTransport sigma mu2 hmissingMu2 Y hYtoZ]
      exact ⟨treeMissingSubset hAtoY hgammaA,
        treeMissingSubset (commonPrefix hBtoT hYtoT (hBtoX.1.trans hXtoY.1)) hbetaB⟩
    have hAYstrict : A.length < Y.length := by
      have hj : 2 ≤ j := hpathLower
      clear * - hj hYlen
      omega
    have hroute2 := routeToY R mu2 hmu2One hweak1
      (fun t hlo hhi => hfixedThroughY t hlo (hYlen ▸ hhi)) hmissingMu2
    obtain ⟨_, _, corr1, hmax1, bs1, K1, good1, same1⟩ :=
      StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T sigma
        R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
        gamma beta hgammaNeBeta hchangeMissing z hpath1 mu2 rfl hcase1 hterminalDisjoint
        Y hAtoY hAYstrict (by rw [penultimatePrefixEq]; exact hYtoZ)
        (fun t hlo hhi => hfixedThroughY t hlo (hYlen ▸ hhi)) hroute2 hsuffixY
        hsplitMissing2 (by rw [penultimatePrefixEq]; exact hmissingMu2)
        hstoredMu2 hgammaCutoff
    let C1 : HierarchyCounterexample bs1 := {
      positive := Nat.lt_of_lt_of_le (by decide) corr1.replacementETT.roundsPositive
      hierarchy := K1
      good := good1
      maximum := hmax1
      notElementary := by
        intro he
        exact Finset.disjoint_left.mp (he
          (vertexMemSelf T (HierarchyFirstMissingPosition sigma T gamma))
          (vertexMemSelf T (Fin.last T.length)) hgammaTerminalDistinct)
          hgammaFirstMu2 hgammaTerminalMu2 }
    obtain ⟨R1, hR1⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
      ett base C ctx R mu2 corr1 bs1 C1 same1
    have sameFullPrefix (S : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx) (m : ℕ) :
        HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m := by
      simp only [HierarchyFullTailPrefix, sameStarAll S, sameStar]
    let rho := R1.coloring
    have hmissingRho : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G rho v = MissingColors G sigma v := by
      rw [show rho = mu2 from hR1]
      exact hmissingMu2
    have hElemRho : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Z) := by
      intro u hu v hv huv
      rw [hmissingRho u hu, hmissingRho v hv]
      exact hElemZ hu hv huv
    have hthetaMissingZ : d.theta ∈ TreeMissingColors sigma Z := treeMissingSubset hYtoZ hthetaY
    have hfirstGammaRho : HierarchyFirstMissingPosition rho T gamma =
        HierarchyFirstMissingPosition sigma T gamma :=
      firstPreserved Z hZtoT sigma rho gamma hElemZ hmissingRho hgammaMissingZ
    have hfirstThetaRho : HierarchyFirstMissingPosition rho T d.theta =
        HierarchyFirstMissingPosition sigma T d.theta :=
      firstPreserved Z hZtoT sigma rho d.theta hElemZ hmissingRho hthetaMissingZ
    have hfirstBetaRho : HierarchyFirstMissingPosition rho T beta =
        HierarchyFirstMissingPosition sigma T beta :=
      firstPreserved Z hZtoT sigma rho beta hElemZ hmissingRho hbetaMissingZ
    have hgammaWitnessRho : gamma ∈ MissingColors G rho
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) := by
      rw [hmissingRho _ (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T gamma)
        (hgammaFirstLe.trans hAtoZ.1))]
      exact hgammaFirst.1
    have hthetaWitnessRho : d.theta ∈ MissingColors G rho
        (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) := by
      rw [hmissingRho _ (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T d.theta)
        (hthetaFirst.2.trans hYtoZ.1))]
      exact hthetaFirst.1
    have hthetaYRho : d.theta ∈ MissingColors G rho (Y.vertex (Fin.last Y.length)) := by
      rw [hmissingRho _ (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
        (vertexMemSelf Y (Fin.last Y.length)))]
      exact hthetaMissingY
    have hgammaTerminalRho : gamma ∈ MissingColors G rho (T.vertex (Fin.last T.length)) := by
      rw [show rho = mu2 from hR1]
      exact hgammaTerminalMu2
    have hgammaUnusedRho : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
        rho (T.edge t) ≠ some gamma := by
      intro t hlo hhi hc
      rw [show rho = mu2 from hR1, hfixedThroughY t hlo (hYlen ▸ hhi)] at hc
      exact hgammaUnused t hlo hhi hc
    have hgammaBeforeTheta : (HierarchyFirstMissingPosition sigma T gamma).val <
        (HierarchyFirstMissingPosition sigma T d.theta).val := by
      rw [hthetaFirstIndex]
      exact hgammaFirstLe.trans_lt hAYstrict
    have hpairMissingRho : gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho Z := by
      have he := missingTransport sigma rho hmissingRho Z ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      rw [he]
      exact ⟨hgammaMissingZ, hthetaMissingZ⟩
    have changeRho := by
      as_aux_lemma =>
        exact ChangeLemma G k e0 R1.corresponding.replacementInput T rho
          R1.corresponding.replacementETT R1.replacementBase R1.counterexample
          R1.minimumContext.proper R1.minimumContext.oneEdgeUncolored R1.minimumContext.lowerRung
          R1.minimumContext.fewerDividers R1.minimumContext.lexicographicMinimality
          (by change ColoredVertexSetElementary G rho
                (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
                  (HierarchyFullTailLength R1.counterexample - 1)))
              rw [samePenultimate R1]; exact hElemRho)
          R1.minimumContext.largeMissingSet gamma d.theta hgammaNeTheta
          (by change gamma ∈ TreeMissingColors rho
                (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample - 1)) ∧
                d.theta ∈ TreeMissingColors rho
                  (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample - 1))
              rw [samePenultimate R1]; exact hpairMissingRho)
          (by
            dsimp only
            rw [sameStarAll R1, hfirstGammaRho, hfirstThetaRho]
            intro _
            refine ⟨⟨_, _, rfl, rfl, hgammaBeforeTheta⟩, ?_⟩
            intro hc
            obtain ⟨_, t, hlo, hhi, he⟩ := Finset.mem_filter.mp hc
            rw [hthetaFirstIndex] at hhi
            exact hgammaUnusedRho t hlo hhi he)
    have sameGammaTheta : TwoColorComponent G rho gamma d.theta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
        TwoColorComponent G rho gamma d.theta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))) := by
      have he : TwoColorComponent G rho gamma d.theta
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T gamma))) =
          TwoColorComponent G rho gamma d.theta
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T d.theta))) := by
        rcases caseGamma R1 with ⟨hp, hm⟩ | ⟨hz, hm⟩
        · exact changeRho.1 ⟨hp, Or.inl hm⟩
        · exact changeRho.2.1 ⟨hz, Or.inl hm⟩
      rw [hfirstGammaRho, hfirstThetaRho] at he
      exact he
    have hgammaThetaDistinct : T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
        T.vertex (HierarchyFirstMissingPosition sigma T d.theta) := by
      intro he
      exact ne_of_lt hgammaBeforeTheta (congrArg Fin.val (T.vertex_injective he))
    have hthetaTerminalDistinct : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠
        T.vertex (Fin.last T.length) := by
      intro he
      have hv := congrArg Fin.val (T.vertex_injective he)
      simp only [Fin.val_last] at hv
      rw [hthetaFirstIndex] at hv
      have hlt : Y.length < T.length := hYlen.symm ▸ hcutJstrict
      exact Nat.ne_of_lt hlt hv
    have separation3 := P2905_T2_ElementaryTerminalComponent G rho gamma d.theta
      hgammaNeTheta R1.minimumContext.proper (TreeSequenceVertexSet Z) hElemRho
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
      (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))
      (T.vertex (Fin.last T.length))
      (vertexMemT Z hZtoT _ (hgammaFirstLe.trans hAtoZ.1))
      (vertexMemT Z hZtoT _ (hthetaFirst.2.trans hYtoZ.1))
      hgammaTerminalDistinct.symm hthetaTerminalDistinct.symm
      hgammaWitnessRho hthetaWitnessRho (Or.inl hgammaTerminalRho) sameGammaTheta
    have hdisjoint3 := separation3.1
    let mu3 := TwoColorComponentSwap G rho gamma d.theta z
    have hpath3 : TwoColorPathComponent G rho gamma d.theta z := separation3.2.1
    have swapOne (old : PartialEdgeColoring E k) (a b : Fin k)
        (ho : IsOneEdgeUncolored old e0) :
        IsOneEdgeUncolored (TwoColorComponentSwap G old a b z) e0 := by
      as_aux_lemma =>
        clear * - G z old a b e0 ho
        constructor
        · simp only [TwoColorComponentSwap, ho.1, reduceCtorEq, if_false, ite_self]
        · intro e he
          obtain ⟨c, hc⟩ := ho.2 e he
          by_cases hm : Sum.inr e ∈ TwoColorComponent G old a b z
          · by_cases ha : old e = some a
            · exact ⟨b, by simp only [TwoColorComponentSwap, hm, ha, if_true]⟩
            · by_cases hb : old e = some b
              · refine ⟨a, ?_⟩
                unfold TwoColorComponentSwap
                rw [if_pos hm, if_neg ha, if_pos hb]
              · exact ⟨c, by simpa only [TwoColorComponentSwap, hm, ha, hb, if_true, if_false] using hc⟩
          · exact ⟨c, by simpa only [TwoColorComponentSwap, hm, if_false] using hc⟩
    have hmu3One : IsOneEdgeUncolored mu3 e0 := swapOne rho gamma d.theta R1.minimumContext.oneEdgeUncolored
    have hgammaOutside3 : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∉
        TwoColorComponent G rho gamma d.theta z := by
      intro hm
      exact Set.disjoint_left.mp hdisjoint3 hm (componentSelf rho gamma d.theta _)
    have hthetaOutside3 : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∉
        TwoColorComponent G rho gamma d.theta z := by
      intro hm
      apply Set.disjoint_left.mp hdisjoint3 hm
      rw [sameGammaTheta]
      exact componentSelf rho gamma d.theta _
    have hmissing3 : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G mu3 v = MissingColors G rho v := separation3.2.2
    have hcase3 :
        let K := R1.counterexample.hierarchy
        (0 < K.dividerCount ∧ gamma ∈ TreeMissingColors rho
          (K.stage ⟨K.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
        (K.dividerCount = 0 ∧
          (gamma ∈ TreeMissingColors rho
              (R1.corresponding.replacementETT.series.data.tree
                (Fin.last R1.corresponding.replacementETT.rounds).castSucc) ∨
            (gamma ∈ TreeMissingColors rho (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
              gamma ∉ TashkinovStoredColors R1.corresponding.replacementETT.series.data
                (Fin.last R1.corresponding.replacementETT.rounds) ∧
              d.theta ∉ TashkinovStoredColors R1.corresponding.replacementETT.series.data
                (Fin.last R1.corresponding.replacementETT.rounds)))) := by
      rcases caseGamma R1 with h | ⟨hz, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨hz, Or.inl hm⟩
    have hdisjoint3First : Disjoint (TwoColorComponent G rho gamma d.theta z)
        (TwoColorComponent G rho gamma d.theta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T gamma)))) := by
      rw [hfirstGammaRho]
      exact hdisjoint3
    have hmissingPairCurrent : gamma ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample - 1)) ∧
        d.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample - 1)) := by
      rw [samePenultimate R1]
      exact hpairMissingRho
    have hweak3 : HierarchyWeaklyStable R1.counterexample.hierarchy
        (Fin.last R1.counterexample.hierarchy.dividerCount) mu3 := by
      as_aux_lemma =>
        exact (StableChangeCasesOneTwo G k e0 R1.corresponding.replacementInput T rho
          R1.corresponding.replacementETT R1.replacementBase R1.counterexample
          R1.minimumContext.proper R1.minimumContext.oneEdgeUncolored R1.minimumContext.lowerRung
          R1.minimumContext.fewerDividers R1.minimumContext.lexicographicMinimality
          (by
            change ColoredVertexSetElementary G rho
              (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
                (HierarchyFullTailLength R1.counterexample - 1)))
            rw [samePenultimate R1]
            exact hElemRho) R1.minimumContext.largeMissingSet
          gamma d.theta hgammaNeTheta hmissingPairCurrent z hpath3 mu3 rfl hcase3 hdisjoint3First).1
    have hfixed3 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
        mu3 (T.edge t) = rho (T.edge t) := by
      as_aux_lemma =>
        let K := R1.counterexample.hierarchy
        let et := R1.corresponding.replacementETT
        let n := Fin.last et.rounds
        let Tn := et.series.data.tree n.castSucc
        have hpref : HierarchyFullTailPrefix R1.counterexample j = Y :=
          sameFullPrefix R1 j
        have exclusion := HierarchyTailMissingColorExclusion G k e0
          R1.corresponding.replacementInput T rho et R1.replacementBase K
          (by
            change ColoredVertexSetElementary G rho
              (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
                (HierarchyFullTailLength R1.counterexample - 1)))
            rw [samePenultimate R1]
            exact hElemRho)
          j ((by decide : 1 ≤ 2).trans hpathLower)
          (by
            change j < T.length - (HierarchyStarredStage R1.counterexample.hierarchy
              (Fin.last R1.counterexample.hierarchy.dividerCount)).length
            rw [sameStarAll R1]
            simpa only [ell, HierarchyFullTailLength, sameStar] using hpathUpper)
          d.theta (by
            change d.theta ∈ MissingColors G rho
              ((HierarchyFullTailPrefix R1.counterexample j).vertex
                (Fin.last (HierarchyFullTailPrefix R1.counterexample j).length))
            rw [hpref]
            exact hthetaYRho)
        intro t hlo hhi
        have hga := hgammaUnusedRho t hlo hhi
        by_cases htheta : rho (T.edge t) = some d.theta
        · let tY : Fin Y.length := ⟨t.val, hhi⟩
          have hcast : Fin.castLE hYtoT.1 tY = t := Fin.ext rfl
          have hc : rho (Y.edge tY) = some d.theta := by
            rw [← hYtoT.2.2 tY, hcast]
            exact htheta
          change ∀ t : Fin (HierarchyFullTailPrefix R1.counterexample j).length,
            (HierarchyStarredStage K (Fin.last K.dividerCount)).length ≤ t.val →
            t.val < (HierarchyStarredStage K (Fin.last K.dividerCount)).length + j →
            rho ((HierarchyFullTailPrefix R1.counterexample j).edge t) = some d.theta →
            K.dividerCount = 0 ∧ R1.replacementBase.core = Tn ∧
              t.val = (HierarchyStarredStage K (Fin.last K.dividerCount)).length ∧
              ∃ f : E,
                TashkinovSeriesStep G k et.rounds e0 R1.corresponding.replacementInput
                  et.series.data n ∧
                (et.series.data.kind n = some TashkinovExtensionKind.SE ∨
                  et.series.data.kind n = some TashkinovExtensionKind.RE) ∧
                et.series.data.connectingEdges n = {f} ∧
                (HierarchyFullTailPrefix R1.counterexample j).edge t = f ∧
                rho f = some d.theta ∧ d.theta ∈ TashkinovStoredColors et.series.data n
            at exclusion
          rw [hpref, sameStarAll R1] at exclusion
          obtain ⟨hz, hcore, hpos, f, hcert, hkind, hedges, hedge, hfc, hraw⟩ :=
            exclusion tY hlo (hYlen ▸ hhi) hc
          have hzero : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 :=
            Fin.ext hz
          have hTnA : Tn = A := by
            have hs := sameStarAll R1
            change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
            rw [hzero] at hs
            change R1.replacementBase.core = A at hs
            exact hcore.symm.trans hs
          have hincident : TreeIncidentEdge Tn (T.edge t) := by
            rw [hTnA]
            obtain ⟨i, hi⟩ := T.attaches t
            let iA : Fin (A.length + 1) := ⟨i.val, by
              have hiLt := i.isLt
              change t.val = A.length at hpos
              omega⟩
            have hiEq : Fin.castLE (Nat.succ_le_succ hAtoT.1) iA =
                Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt)) :=
              Fin.ext rfl
            refine ⟨A.vertex iA, vertexMemSelf A iA, ?_⟩
            rw [← hAtoT.2.1 iA, hiEq, Incident, hi]
            exact Sym2.mem_mk_right _ _
          have hw := hweak3
          change HierarchyWeaklyStable K (Fin.last K.dividerCount) mu3 at hw
          rw [hzero] at hw
          change (if et.series.data.kind n = some TashkinovExtensionKind.PE then
            CombinedStableColoring Tn R1.replacementBase.closure
              (TashkinovStoredColors et.series.data n) rho mu3
            else StableColoring Tn (TashkinovStoredColors et.series.data n) rho mu3) at hw
          have hstable : StableColoring Tn (TashkinovStoredColors et.series.data n)
              rho mu3 := by
            split_ifs at hw with hp
            · exact hw.1
            · exact hw
          exact hstable.1 _ hincident
            ⟨d.theta, Finset.mem_union_right _ hraw, htheta⟩
        · simp only [mu3, TwoColorComponentSwap, hga, htheta, if_false, ite_self]
    have hstored3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
          (Fin.last R1.counterexample.hierarchy.dividerCount),
        HierarchyFirstMissingPosition mu3 T eta = HierarchyFirstMissingPosition rho T eta := by
      intro eta heta
      have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
      have hneGamma : eta ≠ gamma := by
        intro he
        exact (Finset.mem_sdiff.mp hetaD).2 (he.symm ▸ hgammaA)
      by_cases he : eta = d.theta
      · subst eta
        exact firstPreserved Z hZtoT rho mu3 d.theta hElemRho hmissing3 hpairMissingRho.2
      · exact firstUnaffected z rho gamma d.theta eta hgammaNeTheta
          R1.minimumContext.proper hneGamma he
    have hgammaCutoff3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
          (Fin.last R1.counterexample.hierarchy.dividerCount),
        (gamma ∈ R1.counterexample.good.gamma (Fin.last R1.counterexample.hierarchy.dividerCount) eta ∨
          d.theta ∈ R1.counterexample.good.gamma (Fin.last R1.counterexample.hierarchy.dividerCount) eta) →
        (HierarchyFirstMissingPosition rho T eta).val ≤ Y.length := by
      intro eta heta hmem
      have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
      rw [← (sameLast R1).2 eta hetaD] at hmem
      have he : eta = d.theta := by
        by_contra hne
        rcases hmem with hg | ht
        · exact Finset.disjoint_left.mp
            (R.counterexample.good.disjointPairs q eta d.theta hetaD hthetaStored' hne)
            hg hgammaTheta
        · exact hthetaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, hetaD, ht⟩)
      subst eta
      rw [hfirstThetaRho]
      exact hthetaFirst.2
    have hsuffixMu2 : TashkinovAugmentationSequence mu2 Y T :=
      TashkinovAugmentationSequenceComponentSwap G k e0 sigma gamma beta hgammaNeBeta z
        Y T hsuffixY hsplitMissing2.1 hsplitMissing2.2
    have hsuffixRho : TashkinovAugmentationSequence rho Y T := by
      change TashkinovAugmentationSequence R1.coloring Y T
      rw [hR1]
      exact hsuffixMu2
    have hsplitMissing3 : gamma ∈ TreeMissingColors mu3 Y ∧ d.theta ∈ TreeMissingColors mu3 Y := by
      rw [missingTransport rho mu3 hmissing3 Y hYtoZ,
        missingTransport sigma rho hmissingRho Y hYtoZ]
      exact ⟨treeMissingSubset hAtoY hgammaA, hthetaY⟩
    have hroute3 := routeToY R1 mu3 hmu3One hweak3 hfixed3 hmissing3
    obtain ⟨_, _, corr2, hmax2, bs2, K2, good2, same2⟩ :=
      StableChangeCasesOneTwoSplitTail G k e0 R1.corresponding.replacementInput T rho
        R1.corresponding.replacementETT R1.replacementBase R1.counterexample R1.minimumContext
        gamma d.theta hgammaNeTheta hmissingPairCurrent z hpath3 mu3 rfl hcase3 hdisjoint3First
        Y (by dsimp only; rw [sameStarAll R1]; exact hAtoY)
        (by dsimp only; rw [sameStarAll R1]; exact hAYstrict)
        (by rw [samePenultimate R1]; exact hYtoZ)
        (by dsimp only; rw [sameStarAll R1]; exact hfixed3) hroute3 hsuffixRho
        hsplitMissing3 (by rw [samePenultimate R1]; exact hmissing3)
        hstored3 hgammaCutoff3
    have hthetaTerminalMu3 : d.theta ∈ MissingColors G mu3 (T.vertex (Fin.last T.length)) :=
      (TwoColorComponentSwapMissingBehavior G rho gamma d.theta hgammaNeTheta
        R1.minimumContext.proper z).2.1 _ (componentSelf rho gamma d.theta _) hgammaTerminalRho
    have hthetaYMu3 : d.theta ∈ MissingColors G mu3 (Y.vertex (Fin.last Y.length)) := by
      rw [hmissing3 _ (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
        (vertexMemSelf Y (Fin.last Y.length)))]
      exact hthetaYRho
    have hYTerminalDistinct : Y.vertex (Fin.last Y.length) ≠ T.vertex (Fin.last T.length) := by
      intro he
      have hi := T.vertex_injective ((hYtoT.2.1 (Fin.last Y.length)).trans he)
      have hv := congrArg Fin.val hi
      simp only [Fin.val_castLE, Fin.val_last] at hv
      exact Nat.ne_of_lt (hYlen.symm ▸ hcutJstrict) hv
    let C2 : HierarchyCounterexample bs2 := {
      positive := Nat.lt_of_lt_of_le (by decide) corr2.replacementETT.roundsPositive
      hierarchy := K2
      good := good2
      maximum := hmax2
      notElementary := by
        intro he
        exact Finset.disjoint_left.mp (he
          (TreeSequenceInitialSegmentVertexSetSubset hYtoT (vertexMemSelf Y (Fin.last Y.length)))
          (vertexMemSelf T (Fin.last T.length)) hYTerminalDistinct)
          hthetaYMu3 hthetaTerminalMu3 }
    obtain ⟨R2, hR2⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
      ett base C ctx R1 mu3 corr2 bs2 C2 same2
    have hjEligible : j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, R2, d.theta, ?_, ?_⟩
      · exact (by decide : 1 ≤ 2).trans hpathLower
      · exact Nat.le_sub_one_of_lt hpathUpper
      · rw [hR2]
        exact hthetaYMu3
      · rw [hR2]
        exact hthetaTerminalMu3
    have hbound := HierarchySituationThreeEligibleIndexBound G k e0 input T phi ett base C ctx
      (by rw [hj]; exact hpathLower) (by rw [hj]; exact hpathUpper) hvertexMissing j hjEligible
    rw [hj] at hbound
    exact Nat.lt_irrefl j hbound
