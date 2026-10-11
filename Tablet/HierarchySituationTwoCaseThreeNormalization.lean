import Tablet.ChangeLemma
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.ColoredVertexSetClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyLEMStable
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchySituationTwoCommonTailData
import Tablet.HierarchySituationTwoOutsidePenultimateReconstruction
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.NineN
import Tablet.RevisitingExtensionCertificate
import Tablet.SameGoodHierarchy
import Tablet.sc1
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.P2752_T2_NormalizedDatum
import Mathlib.Data.Finset.Option
import Tablet.TashkinovAlternatingSegmentAppend
import Tablet.TwoColorComponentNearestSegment
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.P2752_T2_MinimumContextTransport
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.P2813_T1_BaseDisplayedEdges

-- [TABLET NODE: HierarchySituationTwoCaseThreeNormalization]
theorem HierarchySituationTwoCaseThreeNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      Nonempty (HierarchySituationTwoCaseThreeNormalizedData
        G k e0 P.corresponding.replacementInput T P.coloring
          P.corresponding.replacementETT P.replacementBase
          P.counterexample P.minimumContext) := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let A := HierarchyStarredStage H q
  let ell := T.length - A.length
  let B := HierarchyFullTailPrefix C (ell - 2)
  let M0 := (TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G phi v
  let U := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length, A.length ≤ r.val ∧
      r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let X := (TreeMissingColors phi B \ M0) \ U
  let Dn := TashkinovStoredColors ett.series.data n
  let Dnq := HierarchyStoredColorsAt H q
  let Gamma := Dnq.biUnion (C.good.gamma q)
  let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c
  -- Only the two terminal edges add obstructions to the color choice.
  have hchoice : ∃ beta : Fin k,
      beta ∈ TreeMissingColors phi B ∧
      (∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta) ∧
      ((0 < H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma) ∨
        (H.dividerCount = 0 ∧ beta ∉ Dn ∧ beta ∉ Gamma) ∨
        (beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed)) := by
    let Tn := ett.series.data.tree n.castSucc
    let M0 := (TreeSequenceVertexSet base.core \
        TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G phi v
    let U := (Finset.univ : Finset (Fin k)).filter fun c =>
      ∃ r : Fin T.length, A.length ≤ r.val ∧
        r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
    let X := (TreeMissingColors phi B \ M0) \ U
    have hell : 2 ≤ ell := D.tailAtLeastTwo
    have hT : 2 ≤ T.length := le_trans hell (Nat.sub_le _ _)
    let t1 : Fin T.length := ⟨T.length - 2, by omega⟩
    let t2 : Fin T.length := ⟨T.length - 1, by omega⟩
    let L := (phi (T.edge t1)).toFinset ∪ (phi (T.edge t2)).toFinset
    have hLcard : L.card ≤ 2 := by
      have h1 : (phi (T.edge t1)).toFinset.card ≤ 1 := by
        cases phi (T.edge t1) <;> simp
      have h2 : (phi (T.edge t2)).toFinset.card ≤ 1 := by
        cases phi (T.edge t2) <;> simp
      have h := Finset.card_union_le (phi (T.edge t1)).toFinset
        (phi (T.edge t2)).toFinset
      change L.card ≤ _ at h
      omega
    have hcut : A.length + (ell - 2) = T.length - 2 := by
      dsimp [ell] at hell ⊢
      omega
    have hused : tailUsed ⊆ U ∪ L := by
      intro c hc
      obtain ⟨t, hAt, ht⟩ := (Finset.mem_filter.mp hc).2
      by_cases hsmall : t.val < T.length - 2
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hAt,
          hcut ▸ hsmall, ht⟩
      · apply Finset.mem_union_right
        have hindices : t = t1 ∨ t = t2 := by
          have hv : t.val = T.length - 2 ∨ t.val = T.length - 1 := by omega
          rcases hv with hv | hv
          · exact Or.inl (Fin.ext hv)
          · exact Or.inr (Fin.ext hv)
        rcases hindices with rfl | rfl
        · exact Finset.mem_union_left _ (by simp [ht])
        · exact Finset.mem_union_right _ (by simp [ht])
    have hunusedTail (c : Fin k) (hU : c ∉ U) (hL : c ∉ L) :
        ∀ t : Fin T.length, A.length ≤ t.val →
          phi (T.edge t) ≠ some c := by
      intro t hAt ht
      have hc : c ∈ tailUsed := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, t, hAt, ht⟩
      rcases Finset.mem_union.mp (hused hc) with hc | hc
      · exact hU hc
      · exact hL hc
    have hprefix : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1))) := by
      exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi
        ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung
        ctx.fewerDividers ctx.lexicographicMinimality ctx.largeMissingSet
    have hnine := NineN G k e0 input T phi ett C.positive base H C.good
      hprefix ctx.largeMissingSet (ell - 2)
      (show ell - 2 < ell from by omega)
    change 2 * ett.rounds + 11 ≤ X.card ∧
      ((X \ (Gamma ∪ Dnq)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h : Fin 7, eta h ∈ Dnq ∧ eta h ∈ TreeMissingColors phi B ∧
            Disjoint (C.good.gamma q (eta h) ∪ {eta h}) U) at hnine
    by_cases hsmall : (X \ (Gamma ∪ Dnq)).card ≤ 4
    · obtain ⟨eta, hinj, heta⟩ := hnine.2 hsmall
      let block := fun h : Fin 7 => C.good.gamma q (eta h) ∪ {eta h}
      have hreserved : Disjoint Gamma Dnq :=
        (GoodHierarchyReservedDisjoint C.good q).2
      have hblocks : ∀ i j : Fin 7, i ≠ j → Disjoint (block i) (block j) := by
        intro i j hij
        have hne : eta i ≠ eta j := fun he => hij (hinj he)
        rw [Finset.disjoint_left]
        intro c hc hd
        simp only [block, Finset.mem_union, Finset.mem_singleton] at hc hd
        rcases hc with hc | hc <;> rcases hd with hd | hd
        · exact Finset.disjoint_left.mp
            (C.good.disjointPairs q _ _ (heta i).1 (heta j).1 hne) hc hd
        · exact Finset.disjoint_left.mp hreserved
            (Finset.mem_biUnion.mpr ⟨eta i, (heta i).1, hc⟩)
            (hd.symm ▸ (heta j).1)
        · exact Finset.disjoint_left.mp hreserved
            (Finset.mem_biUnion.mpr ⟨eta j, (heta j).1, hd⟩)
            (hc.symm ▸ (heta i).1)
        · exact hne (hc.symm.trans hd)
      let bad := (Finset.univ : Finset (Fin 7)).filter fun h =>
        (block h ∩ L).Nonempty
      have hbad : bad.card ≤ L.card := by
        have chooseColor (h : {h : Fin 7 // h ∈ bad}) :
            ∃ c, c ∈ block h.val ∧ c ∈ L := by
          obtain ⟨c, hc⟩ := (Finset.mem_filter.mp h.property).2
          exact ⟨c, (Finset.mem_inter.mp hc).1, (Finset.mem_inter.mp hc).2⟩
        let color : {h : Fin 7 // h ∈ bad} → {c : Fin k // c ∈ L} :=
          fun h => ⟨Classical.choose (chooseColor h),
            (Classical.choose_spec (chooseColor h)).2⟩
        have hcolor : Function.Injective color := by
          intro i j heq
          apply Subtype.ext
          by_contra hne
          have hc := congrArg Subtype.val heq
          change Classical.choose (chooseColor i) =
            Classical.choose (chooseColor j) at hc
          exact Finset.disjoint_left.mp (hblocks i.val j.val hne)
            (Classical.choose_spec (chooseColor i)).1
            (hc.symm ▸ (Classical.choose_spec (chooseColor j)).1)
        simpa only [Fintype.card_coe] using
          Fintype.card_le_of_injective color hcolor
      have hgood : ((Finset.univ : Finset (Fin 7)) \ bad).Nonempty := by
        apply Finset.card_pos.mp
        have h := Finset.le_card_sdiff bad (Finset.univ : Finset (Fin 7))
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega
      obtain ⟨h, hh⟩ := hgood
      have hnotBad := (Finset.mem_sdiff.mp hh).2
      have hL : Disjoint (block h) L := by
        rw [Finset.disjoint_left]
        intro c hc hl
        exact hnotBad (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, c, Finset.mem_inter.mpr ⟨hc, hl⟩⟩)
      have hfull : Disjoint (block h) tailUsed := by
        rw [Finset.disjoint_left]
        intro c hc ht
        rcases Finset.mem_union.mp (hused ht) with hu | hl
        · exact Finset.disjoint_left.mp (heta h).2.2 hc hu
        · exact Finset.disjoint_left.mp hL hc hl
      refine ⟨eta h, (heta h).2.1, ?_, Or.inr (Or.inr ⟨(heta h).1, ?_⟩)⟩
      · intro t hAt ht
        exact Finset.disjoint_left.mp hfull
          (Finset.mem_union_right _ (Finset.mem_singleton_self _))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hAt, ht⟩)
      · exact hfull.mono_left Finset.subset_union_left
    · have hnonempty : ((X \ (Gamma ∪ Dnq)) \ L).Nonempty := by
        apply Finset.card_pos.mp
        have h := Finset.le_card_sdiff L (X \ (Gamma ∪ Dnq))
        omega
      obtain ⟨beta, hbeta⟩ := hnonempty
      obtain ⟨havailable, hL⟩ := Finset.mem_sdiff.mp hbeta
      obtain ⟨hx, hexcluded⟩ := Finset.mem_sdiff.mp havailable
      obtain ⟨hx, hU⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hmissing, hM0⟩ := Finset.mem_sdiff.mp hx
      have hGamma : beta ∉ Gamma := fun h =>
        hexcluded (Finset.mem_union_left _ h)
      have hDnq : beta ∉ Dnq := fun h =>
        hexcluded (Finset.mem_union_right _ h)
      refine ⟨beta, hmissing, hunusedTail beta hU hL, ?_⟩
      by_cases hzero : H.dividerCount = 0
      · refine Or.inr (Or.inl ⟨hzero, ?_, hGamma⟩)
        intro hDn
        have hnotMissingTn : beta ∉ TreeMissingColors phi Tn := by
          have hn : n.val ≠ 0 := by dsimp [n]; exact Nat.ne_of_gt C.positive
          have hd := hDn
          dsimp only [Dn, TashkinovStoredColors] at hd
          rw [if_neg hn] at hd
          have habsent := (Finset.mem_sdiff.mp hd).2
          have hcolor : ett.series.data.coloring n = phi :=
            ett.generatingColoring.symm
          rw [hcolor] at habsent
          exact habsent
        have hmissingA : beta ∈ TreeMissingColors phi A := by
          by_contra habsent
          exact hDnq (Finset.mem_sdiff.mpr ⟨hDn, habsent⟩)
        have hA : A = base.core := by
          have hq : q = 0 := by apply Fin.ext; simp [q, hzero]
          simp [A, HierarchyStarredStage, hq]
        obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissingA
        by_cases hvn : v ∈ TreeSequenceVertexSet Tn
        · exact hnotMissingTn (Finset.mem_biUnion.mpr ⟨v, hvn, hm⟩)
        · apply hM0
          exact Finset.mem_biUnion.mpr
            ⟨v, Finset.mem_sdiff.mpr ⟨hA ▸ hv, hvn⟩, hm⟩
      · exact Or.inl ⟨Nat.pos_of_ne_zero hzero, hDnq, hGamma⟩
  obtain ⟨beta, hmissing, hunused, halternative⟩ := hchoice
  by_cases hterminal : beta ∈ MissingColors G phi
      (T.vertex D.terminalVertexIndex)
  · have hvalid : ∀ i : Fin (ett.rounds + 1),
        IsProperEdgeColoring G (ett.series.data.coloring i) ∧
          IsOneEdgeUncolored (ett.series.data.coloring i) e0 := by
      intro i
      have hs := ett.series.certified i
      cases hs with
      | initial triple _ hcolor =>
        rw [hcolor]
        exact triple.2.2.2
      | SE i _ _ _ _ _ choice _ hcolor =>
        rw [hcolor]
        exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
      | PE i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hone =>
        exact ⟨hp, hone⟩
      | RE i hp hone _ _ _ hcolor =>
        rw [hcolor]
        exact ⟨hp, hone⟩
    let corr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
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
      replacementProper := fun i => (hvalid i).1
      replacementOneUncolored := fun i => (hvalid i).2
      replacementStable := by intro i; simp [StableColoring] }
    let P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
      coloring := phi
      corresponding := corr
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun j => ⟨rfl, fun eta heta => rfl⟩⟩
      minimumContext := ctx }
    obtain ⟨N, hN⟩ := P2752_T2_NormalizedDatum G k e0 input T phi ett base C ctx D
      beta hmissing hunused halternative P (fun _ => rfl)
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hterminal
    exact ⟨P, ⟨N⟩⟩
  · let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    let Q := TwoColorComponent G phi D.alpha beta
      (Sum.inl (T.vertex D.terminalVertexIndex))
    have hbetaPresent : beta ∉ MissingColors G phi
        (T.vertex D.terminalVertexIndex) := hterminal
    by_cases hhit : ∃ v ∈ TreeSequenceVertexSet Bplus,
        Sum.inl v ∈ Q
    · have hlenB : B.length = T.length - 2 := by
        have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
        change min (A.length + (ell - 2)) T.length = T.length - 2
        dsimp [ell]
        omega
      have hlenPlus : Bplus.length = T.length - 1 := by
        have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
        change min (A.length + (HierarchyFullTailLength C - 1)) T.length =
          T.length - 1
        change min (A.length + (ell - 1)) T.length = T.length - 1
        dsimp [ell]
        omega
      have hBT : TreeSequenceInitialSegment B T :=
        ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
      have hplusT : TreeSequenceInitialSegment Bplus T :=
        ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
      have hBBplus : TreeSequenceInitialSegment B Bplus := by
        have hle : B.length ≤ Bplus.length := by rw [hlenB, hlenPlus]; omega
        refine ⟨hle, ?_, ?_⟩
        · intro i
          exact (hplusT.2.1 (Fin.castLE (Nat.succ_le_succ hle) i)).symm.trans
            (hBT.2.1 i)
        · intro i
          exact (hplusT.2.2 (Fin.castLE hle i)).symm.trans (hBT.2.2 i)
      have hindex : D.earlierVertexIndex.val < B.length + 1 := by
        have hp := D.earlierVertexBeforePenultimate
        have hpen := D.penultimateVertexPosition
        have hp' : D.earlierVertexIndex.val + 1 < T.length := by
          omega
        rw [hlenB]
        omega
      have hindexPlus : D.earlierVertexIndex.val < Bplus.length + 1 := by
        rw [hlenPlus]
        have hp := D.earlierVertexBeforePenultimate
        have hpen := D.penultimateVertexPosition
        have hp' : D.earlierVertexIndex.val + 1 < T.length := by
          omega
        omega
      let jPlus : Fin (Bplus.length + 1) :=
        ⟨D.earlierVertexIndex.val, hindexPlus⟩
      have hvertexPlus : Bplus.vertex jPlus = T.vertex D.earlierVertexIndex := by
        have h := hplusT.2.1 jPlus
        calc
          Bplus.vertex jPlus = T.vertex (Fin.castLE
              (Nat.succ_le_succ hplusT.1) jPlus) := h.symm
          _ = T.vertex D.earlierVertexIndex := by
            apply congrArg T.vertex
            apply Fin.ext
            rfl
      have hbetaMissingPlus : beta ∈ TreeMissingColors phi Bplus := by
        obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
        exact Finset.mem_biUnion.mpr
          ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBBplus hv, hm⟩
      have halphaMissingPlus : D.alpha ∈ TreeMissingColors phi Bplus := by
        apply Finset.mem_biUnion.mpr
        refine ⟨T.vertex D.earlierVertexIndex, ?_, D.alphaMissingEarlier⟩
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨jPlus, hvertexPlus.symm⟩
      have hne : D.alpha ≠ beta := by
        intro he
        exact hterminal (he ▸ D.alphaMissingTerminal)
      have hterminalOutside : T.vertex D.terminalVertexIndex ∉
          TreeSequenceVertexSet Bplus := by
        intro hv
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and] at hv
        obtain ⟨i, hi⟩ := hv
        let iT : Fin (T.length + 1) :=
          Fin.castLE (Nat.succ_le_succ hplusT.1) i
        have hprefix := hplusT.2.1 i
        have heq : iT = D.terminalVertexIndex := by
          apply T.vertex_injective
          calc
            T.vertex iT = Bplus.vertex i := hprefix.symm
            _ = T.vertex D.terminalVertexIndex := hi
        have hval : i.val = T.length := by
          have hx := congrArg Fin.val heq
          simpa [iT, D.terminalVertexPosition] using hx
        have hlenPlus' : Bplus.length + 1 = T.length := by
          rw [hlenPlus]
          have hTpos := T.positive
          omega
        have hi' : i.val < T.length := by
          rw [← hlenPlus']
          exact i.isLt
        rw [hval] at hi'
        exact (Nat.lt_irrefl _ hi')
      have segTrans {S U W : TreeSequence G e0}
          (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
          TreeSequenceInitialSegment S W := by
        refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
        · intro i
          exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
        · intro i
          exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
      have commonPrefix {S U W : TreeSequence G e0}
          (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
          (hle : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
        refine ⟨hle, ?_, ?_⟩
        · intro i
          exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hle) i)).symm.trans (hSW.2.1 i)
        · intro i
          exact (hUW.2.2 (Fin.castLE hle i)).symm.trans (hSW.2.2 i)
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
      have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
          TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩) (H.stage ⟨a + d, by omega⟩) := by
        clear * - H a d hbound segTrans
        induction d with
        | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        | succ d ih =>
          exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
      have stageToT (j : Fin (H.dividerCount + 2)) :
          TreeSequenceInitialSegment (H.stage j) T := by
        have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
        have hi : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
            Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
          Fin.ext (by change j.val + (H.dividerCount + 1 - j.val) = H.dividerCount + 1; omega)
        simpa only [hi, H.terminalStage] using hs
      have lastPositive (hp : H.dividerCount ≠ 0) : A = H.stage q.castSucc := by
        let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
        have hi : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
        change HierarchyStarredStage H q = H.stage q.castSucc
        rw [hi]
        rfl
      have hAT : TreeSequenceInitialSegment A T := by
        by_cases hz : H.dividerCount = 0
        · have hq : q = 0 := Fin.ext (by simp [q, hz])
          have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
          exact segTrans (hA ▸ H.coreInsideFirst) (stageToT ⟨1, by omega⟩)
        · rw [lastPositive hz]
          exact stageToT q.castSucc
      have hAB : TreeSequenceInitialSegment A B :=
        commonPrefix hAT hBT (by have hp := D.tailAtLeastTwo; change 2 ≤ T.length - A.length at hp; omega)
      have hTnA : TreeSequenceInitialSegment Tn A := by
        by_cases hz : H.dividerCount = 0
        · have hq : q = 0 := Fin.ext (by simp [q, hz])
          have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
          rw [hA]
          by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
          · exact (Classical.choice (base.parallel hp).2.2).leftSegment
          · rw [base.nonparallel hp]
            exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · rw [lastPositive hz]
          have hs := stageSegment 0 H.dividerCount (by omega)
          have hi0 : (⟨0, by omega⟩ : Fin (H.dividerCount + 2)) = 0 := Fin.ext rfl
          have hiq : (⟨0 + H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
              q.castSucc := Fin.ext (by simp [q])
          rw [hi0, H.baseStage, hiq] at hs
          exact hs
      have halphaMissingB : D.alpha ∈ TreeMissingColors phi B := by
        let i : Fin (B.length + 1) := ⟨D.earlierVertexIndex.val, hindex⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨B.vertex i, by simp [TreeSequenceVertexSet], ?_⟩
        have hv : B.vertex i = T.vertex D.earlierVertexIndex := by
          rw [← hBT.2.1 i]
          congr 1
        rw [hv]
        exact D.alphaMissingEarlier
      obtain ⟨m, hm, pv, pe, hpv, hpe, hstart, hlast, houtside,
          hvcomp, hecomp, hcolors, hends, hfresh⟩ :=
        TwoColorComponentNearestSegment G phi Bplus D.alpha beta
          (T.vertex D.terminalVertexIndex) ctx.proper hne hterminalOutside hhit
      let R := if pv 0 = T.vertex D.penultimateVertexIndex then Bplus else B
      have hBR : TreeSequenceInitialSegment B R := by
        dsimp [R]
        split
        · exact hBBplus
        · exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      have hRplus : TreeSequenceInitialSegment R Bplus := by
        dsimp [R]
        split
        · exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · exact hBBplus
      have hRT := segTrans hRplus hplusT
      have hstartR : pv 0 ∈ TreeSequenceVertexSet R := by
        clear * - R pv D B Bplus T hstart hlenB hlenPlus hplusT hBBplus
        dsimp [R]
        split
        · exact hstart
        · rename_i hnot
          have hs := hstart
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, hi⟩ := hs
          have hiB : i.val ≤ B.length := by
            by_contra hno
            have hiv : i.val = Bplus.length := by omega
            have hv : Bplus.vertex i = T.vertex D.penultimateVertexIndex := by
              rw [← hplusT.2.1 i]
              congr 1
              apply Fin.ext
              have hpen := D.penultimateVertexPosition
              change i.val = D.penultimateVertexIndex.val
              clear * - hpen hiv hlenPlus
              omega
            exact hnot (hi.symm.trans hv)
          let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          refine ⟨j, ?_⟩
          rw [← hBBplus.2.1 j]
          exact (congrArg Bplus.vertex (Fin.ext rfl)).trans hi
      obtain ⟨Utree, hRU, hUlen, hentries, hRUstrict, hRUroute, hUlast, hnew⟩ :=
        TashkinovAlternatingSegmentAppend G phi R D.alpha beta
          (T.vertex D.terminalVertexIndex) m hm pv pe hpv hpe hstartR
          (fun i hi => houtside i (TreeSequenceInitialSegmentVertexSetSubset hRplus hi))
          hvcomp hecomp hcolors hends
          (fun i j => by rw [← hRplus.2.2 j]; exact hfresh i _)
          (by obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp halphaMissingB
              exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBR hv, hc⟩)
          (by obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmissing
              exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBR hv, hc⟩)
      have hBU := segTrans hBR hRU
      have hAU := segTrans hAB hBU
      have hTnR := segTrans hTnA (segTrans hAB hBR)
      have hTnU := segTrans hTnR hRU
      have hTnUstrict : Tn.length < Utree.length := lt_of_le_of_lt hTnR.1 hRUstrict
      have hUterminal : Utree.vertex (Fin.last Utree.length) = T.vertex D.terminalVertexIndex :=
        hUlast.trans hlast
      have hmod := Td G k e0 input T phi ett C.maximum C.positive ctx.lowerRung
        phi ctx.proper ctx.oneEdgeUncolored (by rw [← ett.generatingColoring]; simp [StableColoring])
      have stableClosed (S : TreeSequence G e0) (colors : Finset (Fin k))
          (psi : PartialEdgeColoring E k)
          (hppsi : IsProperEdgeColoring G psi) (hopsi : IsOneEdgeUncolored psi e0)
          (hcpsi : ColoredVertexSetClosed G psi (TreeSequenceVertexSet S))
          (hs : StableColoring S colors psi phi) :
          ColoredVertexSetClosed G phi (TreeSequenceVertexSet S) := by
        clear * - G e0 ctx phi S colors psi hppsi hopsi hcpsi hs
        intro f c x hf hx hfc hcm
        have hincident : TreeIncidentEdge S f := by
          obtain ⟨u, hu, v, hv, huv⟩ := by simpa [BoundaryEdges] using hf
          refine ⟨u, hu, ?_⟩
          change u ∈ G.ends f
          rw [huv]
          exact Sym2.mem_mk_left _ _
        have hcmPrev : c ∈ MissingColors G psi x := by
          rw [← hs.2 x hx]
          exact hcm
        have hcTree : c ∈ TreeMissingColors psi S := Finset.mem_biUnion.mpr ⟨x, hx, hcmPrev⟩
        have hfixed : phi f = psi f :=
          (sc1 G e0 S colors psi phi hppsi hopsi ctx.proper ctx.oneEdgeUncolored).mp hs
            f hincident (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hfc⟩)
        exact hcpsi hf hx (hfixed.symm.trans hfc) hcmPrev
      -- The splice must retain the exact terminal SE/RE connecting seed.
      have seededRoute (f : E) (seed : TreeSequence G e0)
          (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn))
          (hseed : TreeSequenceAdjoinEdge Tn f seed)
          (hclosure : TashkinovClosure phi seed
            (ett.series.data.tree (Fin.last (ett.rounds + 1)))) :
          TashkinovAugmentationSequence phi seed Utree := by
        have hstrict : Tn.length < R.length := by
          by_contra hno
          have hle := hTnR.1
          have heq : R = Tn := (equalTrees hTnR (by omega)).symm
          have hvinside : pv 0 ∈ TreeSequenceVertexSet Tn := heq ▸ hstartR
          let i : Fin m := ⟨0, by omega⟩
          have hvoutside : pv i.succ ∉ TreeSequenceVertexSet Tn := by
            intro hv
            exact houtside i (TreeSequenceInitialSegmentVertexSetSubset
              (segTrans hTnR hRplus) hv)
          have hbdy : pe i ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨pv 0, hvinside, pv i.succ, hvoutside, hends i⟩
          rcases hcolors i with hc | hc
          · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp halphaMissingB
            have hvn : v ∈ TreeSequenceVertexSet Tn :=
              heq ▸ TreeSequenceInitialSegmentVertexSetSubset hBR hv
            exact hclosed hbdy hvn hc hm
          · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
            have hvn : v ∈ TreeSequenceVertexSet Tn :=
              heq ▸ TreeSequenceInitialSegmentVertexSetSubset hBR hv
            exact hclosed hbdy hvn hc hm
        have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed _ hclosure.1
        have hseedR : TreeSequenceInitialSegment seed R :=
          commonPrefix hseedFinal (segTrans hRT ett.belowFinal) (by obtain ⟨hl, _⟩ := hseed; omega)
        exact (TashkinovAugmentationSequenceRestrict phi seed R _ hclosure.1
          hseedR (segTrans hRT ett.belowFinal)).trans hRUroute
      have heligible :
          (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn Utree) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ f seed, ett.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence phi seed Utree) := by
        have hs := ett.series.certified n
        have hcolorN : ett.series.data.coloring n = phi := ett.generatingColoring.symm
        have hnNext : n.succ = Fin.last (ett.rounds + 1) := Fin.ext rfl
        generalize hn : n = z at hs
        cases hs with
        | initial triple seedLength initialColoring initialStored initialEdges initialKind
            initialVertex initialOutside initialDelta initialGamma initialClosure =>
          have hv := congrArg Fin.val hn
          have hp := C.positive
          dsimp [n] at hv
          omega
        | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
            noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
            secondStableProper secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored currentEdges
            currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
            orderedExtension strictExtension =>
          have hi : i.succ = n := hn.symm
          have hclosure : TashkinovClosure phi Tn
              (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
            simpa only [hi, hcolorN, hnNext] using closedExtension
          refine Or.inl ⟨by simpa only [hi] using currentKind, ?_⟩
          exact (TashkinovAugmentationSequenceRestrict phi Tn R _ hclosure.1 hTnR
            (segTrans hRT ett.belowFinal)).trans hRUroute
        | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
            noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
            currentKind currentVertex currentOutside currentDelta currentGamma adjoined
            adjoinedExactly closedExtension orderedExtension strictExtension =>
          have hi : i.succ = n := hn.symm
          have htree : ett.series.data.tree i.succ.castSucc = Tn :=
            congrArg (fun j : Fin (ett.rounds + 1) => ett.series.data.tree j.castSucc) hi
          have hselected : choice.selected = phi := currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans ett.generatingColoring.symm)
          have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) :=
            stableClosed Tn _ _ previousProper previousOneUncolored
              (htree ▸ previousClosed) (by simpa only [htree, hselected] using choice.selectedStable)
          have hseed : TreeSequenceAdjoinEdge Tn choice.edge adjoined := htree ▸ adjoinedExactly
          have hclosure : TashkinovClosure phi adjoined
              (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
            simpa only [hi, hcolorN, hnNext] using closedExtension
          exact Or.inr ⟨Or.inl (by simpa only [hi] using currentKind), choice.edge, adjoined,
            by simpa only [hi] using currentEdges, hseed, seededRoute _ _ hclosed hseed hclosure⟩
        | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
            available currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
            orderedExtension strictExtension =>
          have hi : i.succ = n := hn.symm
          have htree : ett.series.data.tree i.succ.castSucc = Tn :=
            congrArg (fun j : Fin (ett.rounds + 1) => ett.series.data.tree j.castSucc) hi
          have hcolor : ett.series.data.coloring i.castSucc = phi := currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans ett.generatingColoring.symm)
          have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) := by
            have hc : ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
                (TreeSequenceVertexSet Tn) := by
              rw [← htree]
              exact previousClosed
            exact @Eq.mp _ _ (congrArg (fun psi => ColoredVertexSetClosed G psi
              (TreeSequenceVertexSet Tn)) hcolor) hc
          have hseed : TreeSequenceAdjoinEdge Tn available.edge adjoined := htree ▸ adjoinedExactly
          have hclosure : TashkinovClosure phi adjoined
              (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
            simpa only [hi, hcolorN, hnNext] using closedExtension
          exact Or.inr ⟨Or.inr (by simpa only [hi] using currentKind), available.edge, adjoined,
            by simpa only [hi] using currentEdges, hseed, seededRoute _ _ hclosed hseed hclosure⟩
      obtain ⟨corrU⟩ := hmod.2.2 Utree hTnU hTnUstrict heligible
      have hMPU := MaximumPropertyTransport G k e0 ett phi hmod Utree corrU C.maximum
      obtain ⟨baseU, hcoreU, hclosureU, hsupportU⟩ :=
        HierarchyBaseCorrespondingTransport G k e0 input T Utree phi ett corrU base
      have terminalData :
          corrU.replacementETT.series.data.tree (Fin.last corrU.replacementETT.rounds).castSucc = Tn ∧
          corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
            ett.series.data.kind n := by
        clear * - corrU ett Tn n
        rcases corrU with ⟨ri, rs, re, hr, hs, hg, ht, hstored, he, hk, hp, ho, hstable⟩
        cases re with
        | mk rounds positive series above strict below generating =>
          cases hr
          have hseries : series = rs := eq_of_heq hs
          cases hseries
          let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
          have hi : i.succ = Fin.last ett.rounds := Fin.ext (by
            dsimp [i]; have := ett.roundsPositive; omega)
          exact ⟨by simpa only [hi] using ht i, hk _⟩
      have ordinaryToA (j : Fin (H.dividerCount + 1)) :
          TreeSequenceInitialSegment (H.stage j.castSucc) A := by
        clear * - H j A hTnA lastPositive stageSegment
        by_cases hz : H.dividerCount = 0
        · have hj : j = 0 := Fin.ext (by
            have hlt := j.isLt
            change j.val = 0
            clear * - hlt hz
            omega)
          rw [hj]
          change TreeSequenceInitialSegment (H.stage 0) A
          rw [H.baseStage]
          exact hTnA
        · rw [lastPositive hz]
          have hs := stageSegment j.val (H.dividerCount - j.val) (by have := j.isLt; omega)
          convert hs using 1
          · exact congrArg H.stage (Fin.ext rfl)
          · apply congrArg H.stage
            apply Fin.ext
            change H.dividerCount = j.val + (H.dividerCount - j.val)
            have := j.isLt
            omega
      have hAUstrict : A.length < Utree.length := lt_of_le_of_lt (segTrans hAB hBR).1 hRUstrict
      let newStage : Fin (H.dividerCount + 2) → TreeSequence G e0 := fun j =>
        if j.val = H.dividerCount + 1 then Utree else H.stage j
      have stageOld (j : Fin (H.dividerCount + 1)) : newStage j.castSucc = H.stage j.castSucc := by
        simp only [newStage]
        rw [if_neg (by have := j.isLt; change j.val ≠ H.dividerCount + 1; omega)]
      have stageLast : newStage (Fin.last (H.dividerCount + 1)) = Utree := by simp [newStage]
      have stageAt (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
          newStage j = H.stage j := by
        simp only [newStage, if_neg (by omega : j.val ≠ H.dividerCount + 1)]
      have divBound (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
        have hl : (H.stage i.succ.castSucc).length = (H.dividerPosition i).val := by
          have he := congrArg TreeSequence.length (H.dividerStage i)
          exact he
        have hs := (segTrans (ordinaryToA i.succ) hAB).1
        omega
      let K : TashkinovHierarchy corrU.replacementETT baseU := {
        dividerCount := H.dividerCount
        stage := newStage
        baseStage := by
          rw [show newStage 0 = H.stage 0 by simp [newStage], H.baseStage]
          exact terminalData.1.symm
        terminalStage := stageLast
        nested := by
          intro j
          rw [stageOld j]
          by_cases hj : j.val = H.dividerCount
          · have he : j = q := Fin.ext (by simpa [q] using hj)
            subst j
            rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, stageLast]
            exact segTrans (ordinaryToA q) hAU
          · rw [stageAt j.succ (by have := j.isLt; change j.val + 1 ≤ _; omega)]
            exact H.nested j
        strict := by
          intro j
          rw [stageOld j]
          by_cases hj : j.val = H.dividerCount
          · have he : j = q := Fin.ext (by simpa [q] using hj)
            subst j
            rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, stageLast]
            exact lt_of_le_of_lt (ordinaryToA q).1 hAUstrict
          · rw [stageAt j.succ (by have := j.isLt; change j.val + 1 ≤ _; omega)]
            exact H.strict j
        dividerPosition := fun i => ⟨(H.dividerPosition i).val, by
          have hb := divBound i
          have hbu := hBU.1
          omega⟩
        dividerPositive := H.dividerPositive
        dividerIncreasing := H.dividerIncreasing
        dividerStage := by
          intro i
          clear * - H i stageAt divBound hBU hBT equalTrees
          rw [stageAt ⟨i.val + 1, by omega⟩
            (by change i.val + 1 ≤ H.dividerCount; have := i.isLt; omega), H.dividerStage i]
          have hpref : TreeSequencePrefix Utree (H.dividerPosition i).val (H.dividerPositive i)
              (by have := divBound i; have := hBU.1; omega) =
              TreeSequencePrefix T (H.dividerPosition i).val (H.dividerPositive i)
                (Nat.le_of_lt_succ (H.dividerPosition i).isLt) := by
            apply equalTrees
            · refine ⟨le_rfl, ?_, ?_⟩
              · intro x
                have hu := hBU.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
                have ht := hBT.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
                exact ht.trans hu.symm
              · intro x
                have hu := hBU.2.2 (Fin.castLE (divBound i) x)
                have ht := hBT.2.2 (Fin.castLE (divBound i) x)
                exact ht.trans hu.symm
            · rfl
          exact hpref.symm
        coreInsideFirst := by
          rw [hcoreU]
          by_cases hz : H.dividerCount = 0
          · have hq : q = 0 := Fin.ext (by simp [q, hz])
            have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
            rw [show newStage ⟨1, by omega⟩ = Utree by simp [newStage, hz]]
            exact hA ▸ hAU
          · rw [stageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hz)]
            exact H.coreInsideFirst }
      have stageEq (j : Fin (H.dividerCount + 1)) : K.stage j.castSucc = H.stage j.castSucc := stageOld j
      have starredEq (j : Fin (H.dividerCount + 1)) :
          HierarchyStarredStage K j = HierarchyStarredStage H j := by
        refine Fin.cases ?_ (fun i => ?_) j
        · exact hcoreU
        · exact stageEq i.succ
      have storedEq (j : Fin (H.dividerCount + 1)) :
          HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
        unfold HierarchyStoredColorsAt
        dsimp only
        rw [P2752_T2_TerminalStoredColors ett corrU, starredEq]
      have missingEq (j : Fin (H.dividerCount + 1)) :
          HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
        refine Fin.cases ?_ (fun i => ?_) j
        · exact congrArg (TreeMissingColors phi) terminalData.1
        · exact congrArg (TreeMissingColors phi) (stageEq i.succ)
      have internalSegmentEq (i : Fin H.dividerCount) (eta : Fin k) :
          HierarchySegmentColors K i.castSucc eta = HierarchySegmentColors H i.castSucc eta := by
        let S := H.stage i.succ.castSucc
        have hSB := segTrans (ordinaryToA i.succ) hAB
        have hcutT := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta S.length hSB.1
        have hcutU := HierarchyFirstMissingPositionPrefixCutoff phi B Utree hBU eta S.length hSB.1
        unfold HierarchySegmentColors
        have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        dsimp only
        rw [hi, stageEq i.succ, starredEq i.castSucc, ← hcutU, hcutT]
      have betaOutsideGamma : beta ∉ Gamma := by
        rcases halternative with h | h | h
        · exact h.2.2
        · exact h.2.2
        · intro hg
          exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 hg h.1
      have firstBound (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + 1))
          (hc : c ∈ MissingColors G phi (S.vertex i)) :
          (HierarchyFirstMissingPosition phi S c).val ≤ i.val := by
        clear * - S c i hc phi
        let W := (Finset.univ : Finset (Fin (S.length + 1))).filter fun j =>
          c ∈ MissingColors G phi (S.vertex j)
        have hi : i ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        have hw : W.Nonempty := ⟨i, hi⟩
        change (if h : W.Nonempty then W.min' h else Fin.last S.length).val ≤ i.val
        rw [dif_pos hw]
        exact Finset.min'_le W i hi
      have firstWitness (c : Fin k) (hc : (HierarchyFirstMissingPosition phi T c).val < T.length) :
          c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
        clear * - phi T c hc
        let W := (Finset.univ : Finset (Fin (T.length + 1))).filter fun j =>
          c ∈ MissingColors G phi (T.vertex j)
        by_cases hw : W.Nonempty
        · have he : HierarchyFirstMissingPosition phi T c = W.min' hw := by
            simp only [HierarchyFirstMissingPosition, W, dif_pos hw]
          rw [he]
          exact (Finset.mem_filter.mp (Finset.min'_mem W hw)).2
        · have he : HierarchyFirstMissingPosition phi T c = Fin.last T.length := by
            simp only [HierarchyFirstMissingPosition, W, dif_neg hw]
          rw [he] at hc
          exact (Nat.lt_irrefl _ hc).elim
      have goodShort
          (control : ∀ eta, eta ∈ Dnq → D.alpha ∈ C.good.gamma q eta →
            (HierarchyFirstMissingPosition phi T eta).val ≤ B.length) : GoodHierarchy K := by
        clear * - G phi K C H q A B T Utree R hRU hRT hnew hBR hBT hBU control
          storedEq missingEq starredEq stageEq internalSegmentEq terminalData hcoreU hclosureU
          firstWitness firstBound betaOutsideGamma Dnq beta D hlenB
        have terminalAvoid (eta : Fin k) (heta : eta ∈ Dnq) :
            Disjoint (C.good.gamma q eta) (HierarchySegmentColors K q eta) := by
          apply Finset.disjoint_left.mpr
          intro c hc hu
          unfold HierarchySegmentColors at hu
          dsimp only at hu
          rw [show q.succ = Fin.last (K.dividerCount + 1) from Fin.ext rfl,
            K.terminalStage, starredEq q] at hu
          obtain ⟨_, r, hrA, hrfirst, hrcolor⟩ := Finset.mem_filter.mp hu
          change A.length ≤ r.val at hrA
          by_cases hr : r.val < R.length
          · let rR : Fin R.length := ⟨r.val, hr⟩
            let rT : Fin T.length := Fin.castLE hRT.1 rR
            have hedge : phi (T.edge rT) = some c := by
              rw [hRT.2.2 rR, ← hRU.2.2 rR]
              simpa only [show Fin.castLE hRU.1 rR = r from Fin.ext rfl] using hrcolor
            have hcutU := HierarchyFirstMissingPositionPrefixCutoff phi R Utree hRU eta R.length le_rfl
            have hcutT := HierarchyFirstMissingPositionPrefixCutoff phi R T hRT eta R.length le_rfl
            have hsmall : r.val < min (HierarchyFirstMissingPosition phi T eta).val R.length := by
              rw [← hcutT, hcutU]
              omega
            have hseg : c ∈ HierarchySegmentColors H q eta := by
              unfold HierarchySegmentColors
              dsimp only
              rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, H.terminalStage]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rT, hrA,
                by have := rT.isLt; change r.val < min _ _; omega, hedge⟩
            exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hc)).2 hseg
          · rcases (hnew r (by omega)).2.2.2.1 with ha | hb
            · have hca : c = D.alpha := Option.some.inj (hrcolor.symm.trans ha)
              subst c
              have hearly := control eta heta hc
              have hBlt : B.length < T.length := by rw [hlenB]; have := T.positive; omega
              have hm := firstWitness eta (lt_of_le_of_lt hearly hBlt)
              let iB : Fin (B.length + 1) :=
                ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
              have hmissingB : eta ∈ MissingColors G phi (B.vertex iB) := by
                rw [← hBT.2.1 iB]
                have hi : Fin.castLE (Nat.succ_le_succ hBT.1) iB =
                    HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
                rw [hi]
                exact hm
              have hmissingU : eta ∈ MissingColors G phi
                  (Utree.vertex (Fin.castLE (Nat.succ_le_succ hBU.1) iB)) := by
                rw [hBU.2.1 iB]
                exact hmissingB
              have hfirstU := firstBound Utree eta _ hmissingU
              change (HierarchyFirstMissingPosition phi Utree eta).val ≤
                (HierarchyFirstMissingPosition phi T eta).val at hfirstU
              have hBRlen := hBR.1
              omega
            · have hcb : c = beta := Option.some.inj (hrcolor.symm.trans hb)
              subst c
              exact betaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)
        exact {
          gamma := C.good.gamma
          twoColors := by intro j eta heta; exact C.good.twoColors j eta ((storedEq j) ▸ heta)
          avoidance := by
            intro j eta heta c hc
            have hetaOld : eta ∈ HierarchyStoredColorsAt H j := (storedEq j) ▸ heta
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · rw [missingEq j]
              exact (Finset.mem_sdiff.mp (C.good.avoidance j eta hetaOld hc)).1
            · intro hseg
              by_cases hj : j.val < H.dividerCount
              · let i : Fin H.dividerCount := ⟨j.val, hj⟩
                have hij : i.castSucc = j := Fin.ext rfl
                rw [← hij, internalSegmentEq i eta, hij] at hseg
                exact (Finset.mem_sdiff.mp (C.good.avoidance j eta hetaOld hc)).2 hseg
              · have he : j = q := Fin.ext (by
                  change j.val = H.dividerCount
                  have hjb : j.val < H.dividerCount + 1 := j.isLt
                  omega)
                subst j
                exact Finset.disjoint_left.mp (terminalAvoid eta hetaOld) hc hseg
          disjointPairs := by
            intro j eta theta heta htheta hne
            exact C.good.disjointPairs j eta theta ((storedEq j) ▸ heta) ((storedEq j) ▸ htheta) hne
          uniqueRefresh := by
            intro i
            change ∃! eta, eta ∈ HierarchyStoredColorsAt K i.succ ∧
              C.good.gamma i.succ eta ⊆
                ((TreeSequenceVertexSet (K.stage i.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
                    fun v => MissingColors G phi v) ∧
              ∀ theta ∈ HierarchyStoredColorsAt K i.succ, theta ≠ eta →
                C.good.gamma i.succ theta = C.good.gamma i.castSucc theta
            rw [storedEq i.succ, stageEq i.succ, starredEq i.castSucc]
            exact C.good.uniqueRefresh i
          parallelBase := by
            dsimp only
            intro hp
            have hpo : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
              terminalData.2.symm.trans hp
            rw [hcoreU, hclosureU, terminalData.1, storedEq 0]
            exact C.good.parallelBase hpo
          minusClosed := by
            intro i
            rw [stageEq i.succ, storedEq i.succ]
            exact C.good.minusClosed i }
      have pathShort : HierarchyPathNumber K < HierarchyPathNumber H := by
        clear * - G K H q A ell T Utree R B Bplus D hnew hBR hRU hUlen hRUstrict
          hAT hlenB hlenPlus hplusT starredEq pv hm m
        have hell : 2 ≤ ell := D.tailAtLeastTwo
        have hsum : A.length + ell = T.length := by dsimp [ell]; have := hAT.1; omega
        let candidates := (Finset.Icc 1 (Utree.length - A.length)).filter fun i =>
          ∀ r : Fin Utree.length, A.length + i ≤ r.val →
            G.ends (Utree.edge r) = s(Utree.vertex r.castSucc, Utree.vertex r.succ)
        have hcand : ell - 1 ∈ candidates := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
          · have hbr := hBR.1
            omega
          · intro r hr
            by_cases hp : pv 0 = T.vertex D.penultimateVertexIndex
            · have hR : R = Bplus := if_pos hp
              have hRlen : R.length = T.length - 1 := hR ▸ hlenPlus
              have hge : R.length ≤ r.val := by omega
              rw [(hnew r hge).2.2.2.2]
              split
              · rename_i he
                have hv : Utree.vertex r.castSucc = pv 0 := by
                  have h := hRU.2.1 (Fin.last R.length)
                  have hi : Fin.castLE (Nat.succ_le_succ hRU.1) (Fin.last R.length) = r.castSucc :=
                    Fin.ext (by change R.length = r.val; omega)
                  rw [hi, hR, ← hplusT.2.1 (Fin.last Bplus.length)] at h
                  have hj : Fin.castLE (Nat.succ_le_succ hplusT.1) (Fin.last Bplus.length) =
                      D.penultimateVertexIndex := Fin.ext (by
                    change Bplus.length = D.penultimateVertexIndex.val
                    have := D.penultimateVertexPosition
                    omega)
                  rw [hj] at h
                  exact h.trans hp.symm
                rw [hv]
              · rfl
            · have hR : R = B := if_neg hp
              have hRlen : R.length = T.length - 2 := hR ▸ hlenB
              have hge : R.length ≤ r.val := by omega
              rw [(hnew r hge).2.2.2.2, if_neg (by omega : r.val ≠ R.length)]
        have hnonempty : candidates.Nonempty := ⟨ell - 1, hcand⟩
        have hpath : HierarchyPathNumber K = candidates.min' hnonempty := by
          unfold HierarchyPathNumber
          dsimp only
          rw [starredEq q]
          change (if h : candidates.Nonempty then candidates.min' h else _) = _
          rw [dif_pos hnonempty]
        rw [hpath, D.pathNumberFull]
        have hle := Finset.min'_le candidates (ell - 1) hcand
        change candidates.min' hnonempty < ell
        omega
      have shorteningContradiction
          (control : ∀ eta, eta ∈ Dnq → D.alpha ∈ C.good.gamma q eta →
            (HierarchyFirstMissingPosition phi T eta).val ≤ B.length) : False := by
        have hnotElementary : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet Utree) := by
          let iB : Fin (B.length + 1) := ⟨D.earlierVertexIndex.val, hindex⟩
          have hvB : B.vertex iB = T.vertex D.earlierVertexIndex := by
            rw [← hBT.2.1 iB]
            congr 1
          have hvU : T.vertex D.earlierVertexIndex ∈ TreeSequenceVertexSet Utree :=
            TreeSequenceInitialSegmentVertexSetSubset hBU (hvB ▸ (by simp [TreeSequenceVertexSet]))
          have htU : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet Utree :=
            hUterminal ▸ (by simp [TreeSequenceVertexSet])
          have hdistinct : T.vertex D.earlierVertexIndex ≠ T.vertex D.terminalVertexIndex := by
            intro he
            have hi := congrArg Fin.val (T.vertex_injective he)
            have hterm := D.terminalVertexPosition
            have hearly := D.earlierVertexBeforePenultimate
            have hpen := D.penultimateVertexPosition
            omega
          intro he
          exact Finset.disjoint_left.mp (he hvU htU hdistinct)
            D.alphaMissingEarlier D.alphaMissingTerminal
        let Cnew : HierarchyCounterexample baseU := {
          positive := by rw [corrU.rungAgreement]; exact C.positive
          hierarchy := K
          good := goodShort control
          maximum := hMPU
          notElementary := hnotElementary }
        exact ctx.lexicographicMinimality Cnew corrU.rungAgreement rfl (Or.inl pathShort)
      by_cases haOutside : D.alpha ∉ Gamma
      · exact (shorteningContradiction (by
          intro eta heta ha
          exact (haOutside (Finset.mem_biUnion.mpr ⟨eta, heta, ha⟩)).elim)).elim
      · have haGamma : D.alpha ∈ Gamma := not_not.mp haOutside
        by_cases haUsed : D.alpha ∈ tailUsed
        · have alphaNotLast : phi (T.edge D.lastEdgeIndex) ≠ some D.alpha := by
            intro hc
            have hnotPresent : D.alpha ∉ PresentColors G phi (T.vertex D.terminalVertexIndex) :=
              (Finset.mem_sdiff.mp D.alphaMissingTerminal).2
            apply hnotPresent
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨T.edge D.lastEdgeIndex, ?_, hc⟩
            obtain ⟨i, he⟩ := T.attaches D.lastEdgeIndex
            have hi : D.lastEdgeIndex.succ = D.terminalVertexIndex := Fin.ext (by
              change D.lastEdgeIndex.val + 1 = D.terminalVertexIndex.val
              have := D.lastEdgePosition
              have := D.terminalVertexPosition
              omega)
            change T.vertex D.terminalVertexIndex ∈ G.ends (T.edge D.lastEdgeIndex)
            rw [he, hi]
            exact Sym2.mem_mk_left _ _
          obtain ⟨t, htA, htcolor⟩ := (Finset.mem_filter.mp haUsed).2
          have htB : t.val ≤ B.length := by
            by_contra hn
            have htlast : t = D.lastEdgeIndex := Fin.ext (by
              have := t.isLt
              have := D.lastEdgePosition
              rw [hlenB] at hn
              omega)
            exact alphaNotLast (htlast ▸ htcolor)
          apply False.elim
          apply shorteningContradiction
          intro eta heta hgamma
          have hfirst : (HierarchyFirstMissingPosition phi T eta).val ≤ t.val := by
            by_contra hn
            have hseg : D.alpha ∈ HierarchySegmentColors H q eta := by
              unfold HierarchySegmentColors
              dsimp only
              rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, H.terminalStage]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA,
                by have := t.isLt; omega, htcolor⟩
            exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).2 hseg
          exact hfirst.trans htB
        -- An unused reserved color requires a genuinely recolored certificate.
        · clear * - G k e0 input T phi ett base C ctx D H q n Tn A ell B Bplus Q
            Dnq Gamma tailUsed beta hmissing hunused halternative hne hbetaPresent
            hlenB hlenPlus hBT hplusT hBBplus halphaMissingB halphaMissingPlus
            hbetaMissingPlus hterminalOutside hAT hTnA lastPositive firstBound firstWitness haGamma haUsed
          have hprefixElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
            HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
              ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
              ctx.lexicographicMinimality ctx.largeMissingSet
          have prefixFirst (S : TreeSequence G e0) (hST : TreeSequenceInitialSegment S T)
              (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
              (HierarchyFirstMissingPosition phi T c).val ≤ S.length := by
            clear * - S hST c hc firstBound phi T
            obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
            obtain ⟨i, hi⟩ := hv
            have hmissing : c ∈ MissingColors G phi
                (T.vertex (Fin.castLE (Nat.succ_le_succ hST.1) i)) := by
              rw [hST.2.1 i, hi]
              exact hm
            have hbound := firstBound T c _ hmissing
            change (HierarchyFirstMissingPosition phi T c).val ≤ i.val at hbound
            exact hbound.trans (Nat.le_of_lt_succ i.isLt)
          have haStage : D.alpha ∈ HierarchyStageMissingColors H q := by
            obtain ⟨eta, heta, hga⟩ := Finset.mem_biUnion.mp haGamma
            exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hga)).1
          have hcase :
              (0 < H.dividerCount ∧ D.alpha ∈ TreeMissingColors phi (H.stage q.castSucc)) ∨
              (H.dividerCount = 0 ∧ D.alpha ∈ TreeMissingColors phi Tn) := by
            by_cases hz : H.dividerCount = 0
            · have hq : q = 0 := Fin.ext (by simp [q, hz])
              exact Or.inr ⟨hz, by simpa only [hq, HierarchyStageMissingColors, Fin.cases_zero] using haStage⟩
            · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
              have hq : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
              refine Or.inl ⟨Nat.pos_of_ne_zero hz, ?_⟩
              simpa only [hq, HierarchyStageMissingColors, Fin.cases_succ] using haStage
          have haMissingA : D.alpha ∈ TreeMissingColors phi A := by
            rcases hcase with h | h
            · rw [lastPositive (Nat.ne_of_gt h.1)]
              exact h.2
            · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp h.2
              exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hm⟩
          have haFirstA := prefixFirst A hAT D.alpha haMissingA
          have haFirstB := prefixFirst B hBT D.alpha halphaMissingB
          have hbFirstB := prefixFirst B hBT beta hmissing
          let ia := HierarchyFirstMissingPosition phi T D.alpha
          let ib := HierarchyFirstMissingPosition phi T beta
          let va := T.vertex ia
          let vb := T.vertex ib
          let yp := T.vertex D.terminalVertexIndex
          have hBlt : B.length < T.length := by rw [hlenB]; have := T.positive; omega
          have hma : D.alpha ∈ MissingColors G phi va :=
            firstWitness _ (lt_of_le_of_lt haFirstB hBlt)
          have hmb : beta ∈ MissingColors G phi vb :=
            firstWitness _ (lt_of_le_of_lt hbFirstB hBlt)
          have firstInB (c : Fin k) (hc : (HierarchyFirstMissingPosition phi T c).val ≤ B.length) :
              T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet Bplus := by
            let i : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition phi T c).val, by omega⟩
            have hv : T.vertex (HierarchyFirstMissingPosition phi T c) = B.vertex i := by
              exact hBT.2.1 i
            apply TreeSequenceInitialSegmentVertexSetSubset hBBplus
            rw [hv]
            simp [TreeSequenceVertexSet]
          have hva := firstInB D.alpha haFirstB
          have hvb := firstInB beta hbFirstB
          have hsame := ChangeLemma G k e0 input T phi ett base C ctx.proper ctx.oneEdgeUncolored
            ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality hprefixElementary ctx.largeMissingSet
            D.alpha beta hne ⟨halphaMissingPlus, hbetaMissingPlus⟩ (by
              dsimp only
              intro hn
              change D.alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A at hn
              have hbAbsent : beta ∉ TreeMissingColors phi A := hn.resolve_left (by
                intro hna; exact hna haMissingA)
              have hbAfter : A.length < ib.val := by
                by_contra hno
                have hle : ib.val ≤ A.length := by omega
                let i : Fin (A.length + 1) := ⟨ib.val, by omega⟩
                apply hbAbsent
                refine Finset.mem_biUnion.mpr ⟨A.vertex i, by simp [TreeSequenceVertexSet], ?_⟩
                rw [← hAT.2.1 i]
                have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ib := Fin.ext rfl
                rw [hi]
                exact hmb
              refine ⟨⟨ia, ib, rfl, rfl, lt_of_le_of_lt haFirstA hbAfter⟩, ?_⟩
              intro hcolor
              obtain ⟨t, htA, _, htc⟩ := (Finset.mem_filter.mp hcolor).2
              exact haUsed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA, htc⟩))
          have hsameComponent : TwoColorComponent G phi D.alpha beta (Sum.inl va) =
              TwoColorComponent G phi D.alpha beta (Sum.inl vb) := by
            rcases hcase with h | h
            · exact hsame.1 ⟨h.1, Or.inl h.2⟩
            · exact hsame.2.1 ⟨h.1, Or.inl h.2⟩
          let graph := TwoColorIncidenceGraph G phi D.alpha beta
          have absent (v : V) (c : Fin k) (hc : c ∈ MissingColors G phi v)
              (f : E) (hf : Incident G v f) : phi f ≠ some c := by
            intro hfc
            exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, f, hf, hfc⟩)
          have leaf (v : V) (hm : D.alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v) :
              (graph.neighborSet (Sum.inl v)).Subsingleton := by
            clear * - G phi D beta graph hm v ctx absent
            intro x hx y hy
            cases x with
            | inl x => exact (show False by simpa [graph, TwoColorIncidenceGraph] using hx).elim
            | inr f =>
              cases y with
              | inl y => exact (show False by simpa [graph, TwoColorIncidenceGraph] using hy).elim
              | inr g =>
                have hxf : Incident G v f ∧ (phi f = some D.alpha ∨ phi f = some beta) := hx
                have hyg : Incident G v g ∧ (phi g = some D.alpha ∨ phi g = some beta) := hy
                by_cases hfg : f = g
                · exact congrArg Sum.inr hfg
                · exfalso
                  rcases hm with hm | hm
                  · have hf := hxf.2.resolve_left (absent v D.alpha hm f hxf.1)
                    have hg := hyg.2.resolve_left (absent v D.alpha hm g hyg.1)
                    exact ctx.proper hfg ⟨v, hxf.1, hyg.1⟩ hf hg
                  · have hf := hxf.2.resolve_right (absent v beta hm f hxf.1)
                    have hg := hyg.2.resolve_right (absent v beta hm g hyg.1)
                    exact ctx.proper hfg ⟨v, hxf.1, hyg.1⟩ hf hg
          have disjointFirst : Disjoint Q (TwoColorComponent G phi D.alpha beta (Sum.inl va)) := by
            rcases TwoColorComponentsDisjoint G phi D.alpha beta (Sum.inl yp) (Sum.inl va) with he | hd
            · exfalso
              have haQ : Sum.inl va ∈ Q := by
                change Sum.inl va ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp)
                rw [he]
                rfl
              have hbQ : Sum.inl vb ∈ Q := by
                change Sum.inl vb ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp)
                rw [he, hsameComponent]
                rfl
              have hyQ : Sum.inl yp ∈ Q := rfl
              have hay : va ≠ yp := by
                intro heq
                apply hterminalOutside
                change yp ∈ TreeSequenceVertexSet Bplus
                rw [← heq]
                exact hva
              have hby : vb ≠ yp := by
                intro heq
                apply hterminalOutside
                change yp ∈ TreeSequenceVertexSet Bplus
                rw [← heq]
                exact hvb
              have hab : va ≠ vb := by
                intro heq
                have hmbA : beta ∈ MissingColors G phi va := heq ▸ hmb
                have hempty : graph.neighborSet (Sum.inl va) = ∅ := by
                  apply Set.eq_empty_iff_forall_notMem.mpr
                  intro x hx
                  cases x with
                  | inl x => simpa [graph, TwoColorIncidenceGraph] using hx
                  | inr f =>
                    have hf : Incident G va f ∧ (phi f = some D.alpha ∨ phi f = some beta) := hx
                    exact hf.2.elim (absent va D.alpha hma f hf.1) (absent va beta hmbA f hf.1)
                have hreach : graph.Reachable (Sum.inl va) (Sum.inl yp) :=
                  SimpleGraph.ConnectedComponent.eq.mp haQ
                exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
                  (by intro h; exact hay (Sum.inl.inj h)) hempty hreach
              obtain ⟨u, v, p, hp, hsupp⟩ :=
                TwoColorComponentSpanningPath G phi D.alpha beta ctx.proper (Sum.inl yp)
              have endpoints (x : Sum V E) (hx : x ∈ Q) (hleaf : (graph.neighborSet x).Subsingleton) :
                  x = u ∨ x = v := by
                have hxP : x ∈ p.support := by
                  change x ∈ {x | x ∈ p.support}
                  rw [hsupp]
                  exact hx
                by_cases hxu : x = u
                · exact Or.inl hxu
                · by_cases hxv : x = v
                  · exact Or.inr hxv
                  · exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet hxu hxv hleaf hxP).elim
              have hea := endpoints _ haQ (leaf va (Or.inl hma))
              have heb := endpoints _ hbQ (leaf vb (Or.inr hmb))
              have hey := endpoints _ hyQ (leaf yp (Or.inl D.alphaMissingTerminal))
              have hab' : (Sum.inl va : Sum V E) ≠ Sum.inl vb := fun h => hab (Sum.inl.inj h)
              have hay' : (Sum.inl va : Sum V E) ≠ Sum.inl yp := fun h => hay (Sum.inl.inj h)
              have hby' : (Sum.inl vb : Sum V E) ≠ Sum.inl yp := fun h => hby (Sum.inl.inj h)
              rcases hea with hea | hea <;> rcases heb with heb | heb <;> rcases hey with hey | hey
              all_goals first
                | exact hab' (hea.trans heb.symm)
                | exact hay' (hea.trans hey.symm)
                | exact hby' (heb.trans hey.symm)
            · exact hd
          let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
          have behavior := TwoColorComponentSwapMissingBehavior G phi D.alpha beta hne ctx.proper (Sum.inl yp)
          have haOutsideQ : Sum.inl va ∉ Q := fun ha =>
            Set.disjoint_left.mp disjointFirst ha (show Sum.inl va ∈
              TwoColorComponent G phi D.alpha beta (Sum.inl va) from rfl)
          have hbOutsideQ : Sum.inl vb ∉ Q := by
            intro hb
            apply Set.disjoint_left.mp disjointFirst hb
            rw [hsameComponent]
            rfl
          have missingPenultimate : ∀ v, v ∈ TreeSequenceVertexSet Bplus →
              MissingColors G sigma v = MissingColors G phi v := by
            intro v hv
            by_cases hvQ : Sum.inl v ∈ Q
            · have hna : D.alpha ∉ MissingColors G phi v := by
                intro hm
                have he : v = va := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hprefixElementary hv hva hne) hm hma
                exact haOutsideQ (he ▸ hvQ)
              have hnb : beta ∉ MissingColors G phi v := by
                intro hm
                have he : v = vb := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hprefixElementary hv hvb hne) hm hmb
                exact hbOutsideQ (he ▸ hvQ)
              have edgeInQ (f : E) (hf : Incident G v f)
                  (hc : phi f = some D.alpha ∨ phi f = some beta) : Sum.inr f ∈ Q := by
                have hadj : graph.Adj (Sum.inr f) (Sum.inl v) := ⟨hf, hc⟩
                exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvQ
              have hnewA : D.alpha ∉ MissingColors G sigma v := by
                have hpresent : beta ∈ PresentColors G phi v := by simpa [MissingColors] using hnb
                obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp hpresent).2
                have hfQ := edgeInQ f hf (Or.inr hc)
                have hfA : phi f ≠ some D.alpha := fun h => hne (Option.some.inj (h.symm.trans hc))
                have hnew : sigma f = some D.alpha := by
                  change (if Sum.inr f ∈ Q then
                    if phi f = some D.alpha then some beta else
                      if phi f = some beta then some D.alpha else phi f
                    else phi f) = _
                  rw [if_pos hfQ, if_neg hfA, if_pos hc]
                intro hm
                exact (Finset.mem_sdiff.mp hm).2
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hnew⟩)
              have hnewB : beta ∉ MissingColors G sigma v := by
                have hpresent : D.alpha ∈ PresentColors G phi v := by simpa [MissingColors] using hna
                obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp hpresent).2
                have hfQ := edgeInQ f hf (Or.inl hc)
                have hnew : sigma f = some beta := by
                  change (if Sum.inr f ∈ Q then
                    if phi f = some D.alpha then some beta else
                      if phi f = some beta then some D.alpha else phi f
                    else phi f) = _
                  rw [if_pos hfQ, if_pos hc]
                intro hm
                exact (Finset.mem_sdiff.mp hm).2
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hnew⟩)
              apply Finset.ext
              intro c
              by_cases hca : c = D.alpha
              · subst c
                exact ⟨fun h => (hnewA h).elim, fun h => (hna h).elim⟩
              · by_cases hcb : c = beta
                · subst c
                  exact ⟨fun h => (hnewB h).elim, fun h => (hnb h).elim⟩
                · exact behavior.2.2.2 v c hca hcb
            · exact behavior.1 v hvQ
          have storedFirst : ∀ eta, eta ∈ Dnq →
              HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta := by
            intro eta heta
            have hneA : eta ≠ D.alpha := by
              intro he
              exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 haGamma (he ▸ heta)
            by_cases hneB : eta = beta
            · subst eta
              have hfirstPrefix : HierarchyFirstMissingPosition sigma Bplus beta =
                  HierarchyFirstMissingPosition phi Bplus beta := by
                have hfilters :
                    ((Finset.univ : Finset (Fin (Bplus.length + 1))).filter fun i =>
                      beta ∈ MissingColors G sigma (Bplus.vertex i)) =
                    ((Finset.univ : Finset (Fin (Bplus.length + 1))).filter fun i =>
                      beta ∈ MissingColors G phi (Bplus.vertex i)) := by
                  apply Finset.filter_congr
                  intro i _
                  rw [missingPenultimate (Bplus.vertex i) (by simp [TreeSequenceVertexSet])]
                unfold HierarchyFirstMissingPosition
                rw [hfilters]
              have hcutS := HierarchyFirstMissingPositionPrefixCutoff sigma Bplus T hplusT beta Bplus.length le_rfl
              have hcutP := HierarchyFirstMissingPositionPrefixCutoff phi Bplus T hplusT beta Bplus.length le_rfl
              rw [hfirstPrefix] at hcutS
              have hbLt : ib.val < Bplus.length := by
                have hlength : B.length < Bplus.length := by
                  rw [hlenB, hlenPlus]
                  have hp : 2 ≤ T.length := le_trans D.tailAtLeastTwo (Nat.sub_le _ _)
                  clear * - hp
                  omega
                exact lt_of_le_of_lt hbFirstB hlength
              apply Fin.ext
              change (HierarchyFirstMissingPosition sigma T beta).val = ib.val
              change min (HierarchyFirstMissingPosition phi Bplus beta).val Bplus.length =
                min ib.val Bplus.length at hcutP
              clear * - hcutS hcutP hbLt
              omega
            · have hfilters :
                  ((Finset.univ : Finset (Fin (T.length + 1))).filter fun i =>
                    eta ∈ MissingColors G sigma (T.vertex i)) =
                  ((Finset.univ : Finset (Fin (T.length + 1))).filter fun i =>
                    eta ∈ MissingColors G phi (T.vertex i)) := by
                apply Finset.filter_congr
                intro i _
                exact behavior.2.2.2 _ eta hneA hneB
              unfold HierarchyFirstMissingPosition
              rw [hfilters]
          have tailFixed : ∀ t : Fin T.length, A.length ≤ t.val →
              sigma (T.edge t) = phi (T.edge t) := by
            intro t ht
            have hna : phi (T.edge t) ≠ some D.alpha := fun hc =>
              haUsed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hc⟩)
            have hnb := hunused t ht
            unfold sigma TwoColorComponentSwap
            split <;> simp only [if_neg hna, if_neg hnb]
          have pathQ : TwoColorPathComponent G phi D.alpha beta (Sum.inl yp) := by
            exact ⟨hne, Sum.inl yp, show Sum.inl yp ∈ Q from rfl,
              leaf yp (Or.inl D.alphaMissingTerminal)⟩
          obtain ⟨weak, modSigma, _, _, corrT, maximumT, baseT, KT, goodT, sameT⟩ :=
            StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx D.alpha beta hne
              ⟨halphaMissingPlus, hbetaMissingPlus⟩ (Sum.inl yp) pathQ sigma rfl
              (by rcases hcase with h | h
                  · exact Or.inl h
                  · exact Or.inr ⟨h.1, Or.inl h.2⟩)
              disjointFirst tailFixed missingPenultimate storedFirst
          have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t) := by
            change HierarchyWeaklyStable H q sigma at weak
            by_cases hz : H.dividerCount = 0
            · have hq : q = 0 := Fin.ext (by simp [q, hz])
              have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
              rw [hA]
              apply P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base sigma
                ctx.oneEdgeUncolored modSigma.2.1
              rw [hq] at weak
              exact weak
            · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
              have hq : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
              have hinv : TreeColoringInvariant (H.stage q.castSucc) phi sigma := by
                rw [hq] at weak ⊢
                exact weak.2
              rw [lastPositive hz]
              intro t
              by_cases ht : t.val = 0
              · have he : t = ⟨0, (H.stage q.castSucc).positive⟩ := Fin.ext ht
                rw [he, (H.stage q.castSucc).first_edge, modSigma.2.1.1, ctx.oneEdgeUncolored.1]
              · exact hinv.1 t (by omega)
          have fixedT : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t) := by
            intro t
            by_cases ht : t.val < A.length
            · let tA : Fin A.length := ⟨t.val, ht⟩
              have he : Fin.castLE hAT.1 tA = t := Fin.ext rfl
              rw [← he, hAT.2.2 tA]
              exact fixedA tA
            · exact tailFixed t (by omega)
          have hterminalNew : beta ∈ MissingColors G sigma yp :=
            behavior.2.1 yp (show Sum.inl yp ∈ Q from rfl) D.alphaMissingTerminal
          have notElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
            obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
            have hvPlus := TreeSequenceInitialSegmentVertexSetSubset hBBplus hv
            have hmissingNew : beta ∈ MissingColors G sigma v := by rw [missingPenultimate v hvPlus]; exact hm
            have hvT := TreeSequenceInitialSegmentVertexSetSubset hBT hv
            have hyT : yp ∈ TreeSequenceVertexSet T := by simp [yp, TreeSequenceVertexSet]
            have hne : v ≠ yp := by
              intro he
              apply hterminalOutside
              change yp ∈ TreeSequenceVertexSet Bplus
              rw [← he]
              exact hvPlus
            intro he
            exact Finset.disjoint_left.mp (he hvT hyT hne) hmissingNew hterminalNew
          let CT : HierarchyCounterexample baseT := {
            positive := by rw [corrT.rungAgreement]; exact C.positive
            hierarchy := KT
            good := goodT
            maximum := maximumT
            notElementary := notElementary }
          obtain ⟨contextT⟩ := P2752_T2_MinimumContextTransport G k e0 input T phi sigma
            ett base C ctx corrT baseT CT sameT
          let P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
            coloring := sigma
            corresponding := corrT
            maximum := maximumT
            replacementBase := baseT
            counterexample := CT
            sameGood := sameT
            minimumContext := contextT }
          obtain ⟨N, hN⟩ := P2752_T2_NormalizedDatum G k e0 input T phi ett base C ctx D
            beta hmissing hunused halternative P fixedT
            ⟨(fun t _ => by rw [← hplusT.2.2 t]; exact fixedT _), missingPenultimate⟩ hterminalNew
          exact ⟨P, ⟨N⟩⟩
    · have houtside : ∀ v : V, Sum.inl v ∈ Q →
          v ∉ TreeSequenceVertexSet Bplus := by
        intro v hv hvB
        exact hhit ⟨v, hvB, hv⟩
      obtain ⟨_, _, P, _, N, hN⟩ :=
        HierarchySituationTwoOutsidePenultimateReconstruction
          G k e0 input T phi ett base C ctx D beta hmissing hunused
          halternative hbetaPresent houtside
      exact ⟨P, ⟨N⟩⟩
