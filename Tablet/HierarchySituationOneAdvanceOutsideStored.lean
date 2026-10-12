import Tablet.P2963_T1_TerminalKempeStageSwitch
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TreeSequencePrefix
import Tablet.P2813_T1_TerminalRoute
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.Incident
import Tablet.HierarchyEligibleCommonMissingIndices
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
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableChangeCaseThree
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.StableColoring
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
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: HierarchySituationOneAdvanceOutsideStored]
theorem HierarchySituationOneAdvanceOutsideStored {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (i : ℕ) (hiLower : 1 ≤ i)
    (hiUpper : i < HierarchyFullTailLength C - 1)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hcommon :
      alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (houtside :
      let H := P.counterexample.hierarchy
      alpha ∉ HierarchyStoredColorsAt H (Fin.last H.dividerCount)) :
    i + 1 ∈ HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx := by
-- BODY
  classical
  have hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C := by
    rw [hsituation]
    omega
  have componentData (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hproper : IsProperEdgeColoring G psi)
      (B : Finset V) (helem : ColoredVertexSetElementary G psi B)
      (u v w : V) (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v)
      (hwu : w ≠ u) (hwv : w ≠ v)
      (hau : a ∈ MissingColors G psi u) (hbv : b ∈ MissingColors G psi v)
      (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w)
      (hsame : TwoColorComponent G psi a b (Sum.inl u) =
        TwoColorComponent G psi a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G psi a b (Sum.inl w))
          (TwoColorComponent G psi a b (Sum.inl u)) ∧
        TwoColorPathComponent G psi a b (Sum.inl w) ∧
        (∀ x ∈ B,
          MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
            MissingColors G psi x) := by

    exact P2905_T2_ElementaryTerminalComponent G psi a b hne hproper
      B helem u v w hu hv hwu hwv hau hbv hw hsame
  classical
  open scoped Sym2 in
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      clear * - hXY hYZ
      refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
    have common {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z)
        (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
        TreeSequenceInitialSegment X Y := by
      clear * - hXZ hYZ hXY
      refine ⟨hXY, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
    have sameLast : ∀ {a b : ℕ}
        (s : Fin (a + 2) → TreeSequence G e0)
        (t : Fin (b + 2) → TreeSequence G e0)
        (u v : TreeSequence G e0),
        a = b → HEq s t → u = v →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      clear * -
      intro a b s t u v hab hst huv
      cases hab
      have he : s = t := eq_of_heq hst
      cases he
      cases huv
      rfl
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
      (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
    have hAT : TreeSequenceInitialSegment A T := by
      have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
          TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
            (C.hierarchy.stage j.succ) :=
        Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
      simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
        starNext (Fin.last C.hierarchy.dividerCount)
    have htail : 3 ≤ T.length - A.length := by
      have hu := hiUpper
      change i < (T.length - A.length) - 1 at hu
      omega
    have hlen : 4 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    have hBT : TreeSequenceInitialSegment B T := ⟨by dsimp [B, TreeSequencePrefix]; omega,
      fun _ => rfl, fun _ => rfl⟩
    have hAB : TreeSequenceInitialSegment A B :=
      common hAT hBT (by dsimp [B, TreeSequencePrefix]; omega)
    have fullEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) : HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j := by
      unfold HierarchyFullTailPrefix
      dsimp only
      simp only [starEq R]
      rfl
    have fullB (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1) = B := by
      have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)).length +
          (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
        unfold HierarchyFullTailLength
        dsimp only
        rw [starEq R]
        omega
      simp only [HierarchyFullTailPrefix, hn]
      rfl
    have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
      have h : ColoredVertexSetElementary G R.coloring
        (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1))) := by
        exact HierarchyCounterexamplePenultimateElementary G k e0
          R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
          R.replacementBase R.counterexample R.minimumContext.proper
          R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
          R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
          R.minimumContext.largeMissingSet
      intro u hu v hv hne
      exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne
    have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
        U.vertex j ∈ TreeSequenceVertexSet U := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
        (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
        HierarchyFirstMissingPosition psi T c ≤ j := by
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
        c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
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
    have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1))
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by
      clear * - G T B R c j hc elementary vertexMem firstLe firstMem hBT
      have hcT : c ∈ MissingColors G R.coloring
          (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j)) := by
        rw [hBT.2.1 j]; exact hc
      have hle := firstLe R.coloring c _ hcT
      have hlt : (HierarchyFirstMissingPosition R.coloring T c).val < T.length := by
        have := j.isLt
        change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
        have hblen : B.length = T.length - 1 := rfl
        omega
      let x : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T c).val, by
        change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
        omega⟩
      have hxT : Fin.castLE (Nat.succ_le_succ hBT.1) x =
          HierarchyFirstMissingPosition R.coloring T c := Fin.ext rfl
      have hcx : c ∈ MissingColors G R.coloring (B.vertex x) := by
        rw [← hBT.2.1 x, hxT]
        exact firstMem R.coloring c hlt
      have he : B.vertex x = B.vertex j := by
        by_contra hn
        exact Finset.disjoint_left.mp (elementary R (vertexMem B x) (vertexMem B j) hn) hcx hc
      exact congrArg Fin.val (B.vertex_injective he)
    have stageSwitch := P2963_T1_TerminalKempeStageSwitch G k e0 input T phi ett base C ctx
      A B (by omega) rfl rfl
    have lastData (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
          C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
            R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta := by
      clear * - R
      obtain ⟨hcount, hdata⟩ := R.sameGood.2
      have hh := hdata (Fin.last C.hierarchy.dividerCount)
      have hidx : Fin.cast (congrArg (fun q => q + 1) hcount)
          (Fin.last C.hierarchy.dividerCount) =
          Fin.last R.counterexample.hierarchy.dividerCount := Fin.ext hcount
      simpa only [hidx] using hh
    have gammaTransport
        (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        eta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
      clear * - R S eta heta lastData
      have hOrig : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) := by
        rw [(lastData R).1]; exact heta
      refine ⟨?_, ((lastData R).2 eta hOrig).symm.trans ((lastData S).2 eta hOrig)⟩
      rw [← (lastData S).1]
      exact hOrig
    have gammaUnused (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta a : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount))
        (ha : a ∈ R.counterexample.good.gamma
          (Fin.last R.counterexample.hierarchy.dividerCount) eta)
        (t : Fin T.length) (hlo : A.length ≤ t.val)
        (hhi : t.val < (HierarchyFirstMissingPosition R.coloring T eta).val) :
        R.coloring (T.edge t) ≠ some a := by
      clear * - R eta a heta ha t hlo hhi starEq
      intro hc
      have hnot := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance
        (Fin.last R.counterexample.hierarchy.dividerCount) eta heta ha)).2
      apply hnot
      unfold HierarchySegmentColors
      dsimp only
      rw [starEq R, Fin.succ_last, R.counterexample.hierarchy.terminalStage]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo,
        lt_min hhi t.isLt, hc⟩
    have outsideA (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1)) (hj : A.length < j.val)
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        c ∉ TreeMissingColors R.coloring A := by
      clear * - R c j hj hc hAT hBT hAB elementary vertexMem
      rintro hm
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨a, ha⟩ : ∃ a, A.vertex a = v := by simpa [TreeSequenceVertexSet] using hv
      have hne : v ≠ B.vertex j := by
        intro he
        have hh := T.vertex_injective ((hAT.2.1 a).trans
          (ha.trans (he.trans (hBT.2.1 j).symm)))
        have hh := congrArg Fin.val hh
        have := a.isLt
        change a.val = j.val at hh
        omega
      exact Finset.disjoint_left.mp (elementary R
        (TreeSequenceInitialSegmentVertexSetSubset hAB hv) (vertexMem B j) hne) hcv hc
    have notRaw (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (hcA : c ∉ TreeMissingColors R.coloring A)
        (hcD : c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        c ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
          (Fin.last R.corresponding.replacementETT.rounds) := by
      clear * - R c hcA hcD starEq
      intro hm
      apply hcD
      unfold HierarchyStoredColorsAt
      dsimp only
      rw [starEq R]
      exact Finset.mem_sdiff.mpr ⟨hm, hcA⟩
    have tailException (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) (hj : 1 ≤ j) (hjlt : j < T.length - A.length)
        (c : Fin k)
        (hc : c ∈ MissingColors G R.coloring
          ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length)))
        (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < A.length + j)
        (hcol : R.coloring (T.edge t) = some c) :
        TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
          c ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
            (Fin.last R.corresponding.replacementETT.rounds) := by
      clear * - R j hj hjlt c hc t hlo hhi hcol starEq hAT hBT fullEq fullB elementary vertexMem
      let U := HierarchyFullTailPrefix R.counterexample j
      have hUlen : U.length = A.length + j := by
        simp only [U, HierarchyFullTailPrefix, TreeSequencePrefix]
        rw [starEq R]
        exact min_eq_left (by have := hAT.1; omega)
      have hUT : TreeSequenceInitialSegment U T :=
        ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
      let u : Fin U.length := ⟨t.val, by rw [hUlen]; omega⟩
      have hut : Fin.castLE hUT.1 u = t := Fin.ext rfl
      have hcU : c ∈ MissingColors G R.coloring (U.vertex (Fin.last U.length)) := by
        dsimp only [U]
        rw [fullEq R]
        exact hc
      have hcolU : R.coloring (U.edge u) = some c := by
        rw [← hUT.2.2 u, hut]; exact hcol
      have hex := HierarchyTailMissingColorExclusion G k e0 R.corresponding.replacementInput T
        R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample.hierarchy
        (by
          change ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet
            (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)))
          rw [fullB R]
          exact elementary R)
        j hj (by
          change j < T.length - (HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount)).length
          rw [starEq R]
          exact hjlt) c hcU u
        (by
          change (HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount)).length ≤ t.val
          rw [starEq R]
          exact hlo)
        (by
          change t.val < (HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount)).length + j
          rw [starEq R]
          exact hhi) hcolU
      obtain ⟨hzero, hcore, hval, f, hstep, hkind, hedges, hedge, hcF, hstored⟩ := hex
      have hAval : t.val = A.length := by
        change u.val = _ at hval
        rw [starEq R] at hval
        exact hval
      have hAn : A = R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc := by
        rw [← starEq R]
        have hs : HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount) = R.replacementBase.core := by
          simp [HierarchyStarredStage, hzero, Fin.last]
        exact hs.trans hcore
      obtain ⟨i, hi⟩ := T.attaches t
      let a : Fin (A.length + 1) := ⟨i.val, by simpa only [hAval] using i.isLt⟩
      let old : Fin (T.length + 1) :=
        Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))
      have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a = old := Fin.ext rfl
      refine ⟨⟨T.vertex old, ?_, ?_⟩, hstored⟩
      · rw [← hAn, ← ha, hAT.2.1 a]
        exact vertexMem A a
      · rw [Incident, hi]
        exact Sym2.mem_mk_right _ _
    have consecutive (t : Fin T.length)
        (ht : A.length + HierarchyPathNumber C.hierarchy ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      clear * - G T A C t ht hpathUpper
      let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
        ∀ t : Fin T.length, A.length + i ≤ t.val →
          G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
      have hp : HierarchyPathNumber C.hierarchy =
          (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
      have hn : candidates.Nonempty := by
        by_contra hn
        rw [dif_neg hn] at hp
        have hu : HierarchyPathNumber C.hierarchy < T.length - A.length := hpathUpper
        omega
      have hm : candidates.min' hn = HierarchyPathNumber C.hierarchy := by
        simpa only [dif_pos hn] using hp.symm
      have hh := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      rw [hm] at hh
      exact hh t ht
    have gammaChoice (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) (f : E) :
        ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
          R.coloring f ≠ some a := by
      clear * - R eta heta f
      by_contra hn
      push_neg at hn
      have hc : (R.counterexample.good.gamma
          (Fin.last R.counterexample.hierarchy.dividerCount) eta).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact Option.some.inj ((hn a ha).symm.trans (hn b hb))
      rw [R.counterexample.good.twoColors _ eta heta] at hc
      omega
    have advance (m : ℕ) (hmLower : HierarchyPathNumber C.hierarchy ≤ m)
        (hmUpper : m < HierarchyFullTailLength C - 1)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k)
        (ha : alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C m).vertex (Fin.last (HierarchyFullTailPrefix C m).length)))
        (haLast : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
        (hAlphaStored : alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)) :
        m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      have hm : 1 ≤ m := by simpa only [hsituation] using hmLower
      have hmT : A.length + (m + 1) < T.length := by
        change m < (T.length - A.length) - 1 at hmUpper
        have := hAT.1
        omega
      let X := TreeSequencePrefix T (A.length + (m + 1)) (by have := A.positive; omega) (by omega)
      let Y := TreeSequencePrefix T (A.length + m) (by have := A.positive; omega) (by omega)
      have hXT : TreeSequenceInitialSegment X T := ⟨by exact le_of_lt hmT, fun _ => rfl, fun _ => rfl⟩
      have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by dsimp [X, TreeSequencePrefix]; omega)
      have hXB : TreeSequenceInitialSegment X B :=
        common hXT hBT (by dsimp [X, B, TreeSequencePrefix]; omega)
      have hAXlt : A.length < X.length := by dsimp [X, TreeSequencePrefix]; omega
      let jm : Fin (B.length + 1) := ⟨A.length + m, by dsimp [B, TreeSequencePrefix]; omega⟩
      let jnext : Fin (B.length + 1) := ⟨A.length + (m + 1), by dsimp [B, TreeSequencePrefix]; omega⟩
      let tnext : Fin T.length := ⟨A.length + m, by omega⟩
      have hfullY : HierarchyFullTailPrefix C m = Y := by
        have hn : min (A.length + m) T.length = A.length + m := min_eq_left (by omega)
        simp only [HierarchyFullTailPrefix]
        change TreeSequencePrefix T (min (A.length + m) T.length) _ _ = Y
        simp only [hn]
        rfl
      have hfullX : HierarchyFullTailPrefix C (m + 1) = X := by
        have hn : min (A.length + (m + 1)) T.length = A.length + (m + 1) := min_eq_left (by omega)
        simp only [HierarchyFullTailPrefix]
        change TreeSequencePrefix T (min (A.length + (m + 1)) T.length) _ _ = X
        simp only [hn]
        rfl
      have hYvertex : Y.vertex (Fin.last Y.length) = B.vertex jm := rfl
      have hXvertex : X.vertex (Fin.last X.length) = B.vertex jnext := rfl
      have haM : alpha ∈ MissingColors G P.coloring (B.vertex jm) := by
        rw [hfullY, hYvertex] at ha
        exact ha
      obtain ⟨theta, htheta⟩ := hvertexMissing P.coloring P.minimumContext.proper
        P.minimumContext.oneEdgeUncolored (B.vertex jnext)
      have nextMember (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
          (c : Fin k) (hc : c ∈ MissingColors G S.coloring (B.vertex jnext))
          (hcLast : c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) :
          m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, S, c, ?_, hcLast⟩
        rw [hfullX, hXvertex]
        exact hc
      have excNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
          (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jnext))
          (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
          (hcol : R.coloring (T.edge t) = some b) :
          TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
            (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
          b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
            (Fin.last R.corresponding.replacementETT.rounds) := by
        apply tailException R (m + 1) (by omega) (by have := hAT.1; omega) b
          (by rw [hfullX, hXvertex]; exact hb) t hlo
          (by exact hhi) hcol
      have excM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
          (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jm))
          (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
          (hcol : R.coloring (T.edge t) = some b) :
          TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
            (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
          b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
            (Fin.last R.corresponding.replacementETT.rounds) := by
        by_cases ht : t.val < A.length + m
        · exact tailException R m (by omega) (by have := hAT.1; omega) b
            (by rw [hfullY, hYvertex]; exact hb) t hlo ht hcol
        · have htEq : t = tnext := Fin.ext (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
          subst t
          have he := consecutive tnext (by dsimp [tnext]; omega)
          have hv : T.vertex tnext.castSucc = B.vertex jm := rfl
          have hi : Incident G (B.vertex jm) (T.edge tnext) := by
            rw [Incident, he, hv]
            exact Sym2.mem_mk_left _ _
          exact ((Finset.mem_sdiff.mp hb).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge tnext, hi, hcol⟩)).elim
      have avoidNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
          (eta a : Fin k)
          (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount))
          (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
          (he : eta ∈ MissingColors G R.coloring (B.vertex jnext)) :
          ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
            R.coloring (T.edge t) ≠ some a := by
        intro t hlo hhi
        apply gammaUnused R eta a heta ha t hlo
        rw [firstAt R eta jnext he]
        exact hhi
      have avoidM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
          (eta a : Fin k)
          (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount))
          (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
          (he : eta ∈ MissingColors G R.coloring (B.vertex jm))
          (hgap : R.coloring (T.edge tnext) ≠ some a) :
          ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
            R.coloring (T.edge t) ≠ some a := by
        intro t hlo hhi
        by_cases ht : t.val < A.length + m
        · apply gammaUnused R eta a heta ha t hlo
          rw [firstAt R eta jm he]
          exact ht
        · have htEq : t = tnext := Fin.ext (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
          simpa only [htEq] using hgap
      by_cases hThetaStored : theta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)
      · obtain ⟨gamma, hgamma, _⟩ := gammaChoice P theta hThetaStored (T.edge tnext)
        obtain ⟨P1, hmissing1, _, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
          gamma alpha theta hThetaStored hgamma
          (by rw [firstAt P theta jnext htheta]; exact le_rfl)
          jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
          haM (Or.inr haLast) (avoidNext P theta gamma hThetaStored hgamma htheta)
          (excM P alpha haM)
        have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1 haLast
        have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
          rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
        obtain ⟨hThetaStored1, heqGamma⟩ := gammaTransport P P1 theta hThetaStored
        have hgamma1 : gamma ∈ P1.counterexample.good.gamma
            (Fin.last P1.counterexample.hierarchy.dividerCount) theta := by
          rw [← heqGamma]; exact hgamma
        obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
          gamma theta theta hThetaStored1 hgamma1
          (by rw [firstAt P1 theta jnext htheta1]; exact le_rfl)
          jnext (by dsimp [jnext]; omega) (by rfl)
          htheta1 (Or.inl hgLast) (avoidNext P1 theta gamma hThetaStored1 hgamma1 htheta1)
          (excNext P1 theta htheta1)
        exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
          (hterminal2 hgLast)
      · have haOutside := outsideA P alpha jm (by dsimp [jm]; omega) haM
        have hthetaOutside := outsideA P theta jnext (by dsimp [jnext]; omega) htheta
        have haRaw := notRaw P alpha haOutside hAlphaStored
        have hthetaRaw := notRaw P theta hthetaOutside hThetaStored
        have haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
            P.coloring (T.edge t) ≠ some alpha := by
          intro t hlo hhi hc
          exact haRaw (excM P alpha haM t hlo hhi hc).2
        have hne : alpha ≠ theta := by
          intro he
          have hvertices : B.vertex jm ≠ B.vertex jnext := by
            intro hh
            have hh := congrArg Fin.val (B.vertex_injective hh)
            dsimp [jm, jnext] at hh
            omega
          exact Finset.disjoint_left.mp (elementary P
            (vertexMem B jm) (vertexMem B jnext) hvertices) haM (he ▸ htheta)
        have iaEq := firstAt P alpha jm haM
        have ibEq := firstAt P theta jnext htheta
        have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) jm =
            HierarchyFirstMissingPosition P.coloring T alpha := Fin.ext iaEq.symm
        have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jnext =
            HierarchyFirstMissingPosition P.coloring T theta := Fin.ext ibEq.symm
        have hordered : TreeVertexOrder T
            (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))
            (T.vertex (HierarchyFirstMissingPosition P.coloring T theta)) :=
          ⟨_, _, rfl, rfl, by dsimp [jm, jnext] at iaEq ibEq; omega⟩
        have hunused : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition P.coloring T theta).val ∧
              P.coloring (T.edge t) = some c) := by
          intro hh
          obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
          exact haUnused t hlo (by rw [ibEq] at hhi; exact hhi) hc
        have haB : alpha ∈ TreeMissingColors P.coloring B :=
          Finset.mem_biUnion.mpr ⟨B.vertex jm, vertexMem B jm, haM⟩
        have hthetaB : theta ∈ TreeMissingColors P.coloring B :=
          Finset.mem_biUnion.mpr ⟨B.vertex jnext, vertexMem B jnext, htheta⟩
        have hprefixP : ColoredVertexSetElementary G P.coloring
            (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
              (HierarchyFullTailLength P.counterexample - 1))) := by
          rw [fullB P]
          exact elementary P
        have hmissingP : alpha ∈ TreeMissingColors P.coloring
            (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)) ∧
            theta ∈ TreeMissingColors P.coloring
            (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)) := by
          rw [fullB P]
          exact ⟨haB, hthetaB⟩
        have change := ChangeLemma G k e0 P.corresponding.replacementInput T P.coloring
          P.corresponding.replacementETT P.replacementBase P.counterexample
          P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
          P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
          P.minimumContext.largeMissingSet alpha theta hne hmissingP
          (by dsimp only; rw [starEq P]; intro _; exact ⟨hordered, hunused⟩)
        have hdisStored : Disjoint ({alpha, theta} : Finset (Fin k))
            (HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount)) := by
          apply Finset.disjoint_left.mpr
          intro c hc hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc
          rcases hc with rfl | rfl
          · exact hAlphaStored hd
          · exact hThetaStored hd
        have hdisRaw : Disjoint ({alpha, theta} : Finset (Fin k))
            (TashkinovStoredColors P.corresponding.replacementETT.series.data
              (Fin.last P.corresponding.replacementETT.rounds)) := by
          apply Finset.disjoint_left.mpr
          intro c hc hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc
          rcases hc with rfl | rfl
          · exact haRaw hd
          · exact hthetaRaw hd
        have hsame : TwoColorComponent G P.coloring alpha theta (Sum.inl (B.vertex jm)) =
            TwoColorComponent G P.coloring alpha theta (Sum.inl (B.vertex jnext)) := by
          have hh : TwoColorComponent G P.coloring alpha theta
              (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))) =
              TwoColorComponent G P.coloring alpha theta
              (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T theta))) := by
            by_cases hq : P.counterexample.hierarchy.dividerCount = 0
            · exact change.2.1 ⟨hq, Or.inr hdisRaw⟩
            · exact change.1 ⟨by omega, Or.inr hdisStored⟩
          rw [← jaEq, ← jbEq, hBT.2.1 jm, hBT.2.1 jnext] at hh
          exact hh
        obtain ⟨hdis, hpath, hmissing⟩ := componentData P.coloring alpha theta hne
          P.minimumContext.proper (TreeSequenceVertexSet B) (elementary P)
          (B.vertex jm) (B.vertex jnext) (T.vertex (Fin.last T.length))
          (vertexMem B jm) (vertexMem B jnext)
          (by intro hh; have hh := congrArg Fin.val (B.vertex_injective hh)
              dsimp [jm, jnext] at hh; omega)
          (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jm).symm)
              have hh := congrArg Fin.val hh; dsimp [jm] at hh; omega)
          (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jnext).symm)
              have hh := congrArg Fin.val hh; dsimp [jnext] at hh; omega)
          haM htheta (Or.inl haLast) hsame
        let sigma := TwoColorComponentSwap G P.coloring alpha theta
          (Sum.inl (T.vertex (Fin.last T.length)))
        have hprecedes : ∀ v ∈ TreeSequenceVertexSet A,
            TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha)) := by
          intro v hv
          obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
          refine ⟨Fin.castLE (Nat.succ_le_succ hAT.1) j, _, (hAT.2.1 j).trans hj, rfl, ?_⟩
          change j.val < (HierarchyFirstMissingPosition P.coloring T alpha).val
          rw [iaEq]
          have := j.isLt
          dsimp [jm]
          omega
        have hunusedBetween : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            (HierarchyFirstMissingPosition P.coloring T alpha).val ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition P.coloring T theta).val ∧
            P.coloring (T.edge t) = some c) := by
          intro hh
          obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
          rw [iaEq] at hlo
          rw [ibEq] at hhi
          exact haUnused t (by dsimp [jm] at hlo; omega) hhi hc
        obtain ⟨_, _, _, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
          StableChangeCaseThree G k e0 P.corresponding.replacementInput T P.coloring
            P.corresponding.replacementETT P.replacementBase P.counterexample
            P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
            P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
            P.minimumContext.largeMissingSet alpha theta hne hmissingP _ sigma rfl
            (by dsimp only; rw [starEq P]; exact hprecedes) hordered
            ⟨hAlphaStored, hThetaStored⟩ hunusedBetween
        have hthetaLast : theta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
          (TwoColorComponentSwapMissingBehavior G P.coloring alpha theta hne
            P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.1 _ (by rfl) haLast
        have hthetaNext : theta ∈ MissingColors G sigma (B.vertex jnext) := by
          rw [hmissing _ (vertexMem B jnext)]
          exact htheta
        have hnot : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
          intro he
          exact Finset.disjoint_left.mp (he
            (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jnext))
            (vertexMem T (Fin.last T.length)) (by
              intro hh
              have hh := T.vertex_injective ((hBT.2.1 jnext).trans hh)
              have hh := congrArg Fin.val hh; dsimp [jnext] at hh; omega)) hthetaNext hthetaLast
        let CS : HierarchyCounterexample bs := {
          positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
          hierarchy := K
          good := goodK
          maximum := hmaximum
          notElementary := hnot }
        obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
          P sigma corr bs CS hsameGood
        exact nextMember S theta (by rw [hS]; exact hthetaNext) (by rw [hS]; exact hthetaLast)
    exact advance i (by simpa only [hsituation] using hiLower) hiUpper
      P alpha hcommon.1 hcommon.2 houtside
