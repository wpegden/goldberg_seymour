import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoCaseTwoExclusions
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.NineN
import Tablet.TashkinovHierarchy
import Tablet.TashkinovStoredColorsCardinality
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: HierarchySituationTwoSubcaseTwoOneNonexceptional]
theorem HierarchySituationTwoSubcaseTwoOneNonexceptional {V E : Type*}
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
    (hnonexceptional :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ¬ ∃ eta, eta ∈ HierarchyStoredColorsAt H q ∧
        eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧
        D.theta ∈ C.good.gamma q eta) :
    False := by
-- BODY
  set_option maxHeartbeats 4000000 in
    classical
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := HierarchyFullTailLength C
    let B := HierarchyFullTailPrefix C (ell - 2)
    let Bplus := HierarchyFullTailPrefix C (ell - 1)
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Dn := TashkinovStoredColors ett.series.data n
    have htail : 2 ≤ ell := D.tailAtLeastTwo
    have hell : ell = T.length - A.length := rfl
    have hsum : A.length + ell = T.length := by omega
    have hBlen : B.length = T.length - 2 := by
      change min (A.length + (ell - 2)) T.length = T.length - 2
      omega
    have hBpluslen : Bplus.length = T.length - 1 := by
      change min (A.length + (ell - 1)) T.length = T.length - 1
      omega
    have hBT : TreeSequenceInitialSegment B T :=
      ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
    have hBplusT : TreeSequenceInitialSegment Bplus T :=
      ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
    have hBBplus : TreeSequenceInitialSegment B Bplus :=
      ⟨by omega, (by intro i; rfl), (by intro i; rfl)⟩
    have hprefixElementary : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet Bplus) :=
      HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
        ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
        ctx.lexicographicMinimality ctx.largeMissingSet
    have halpha := HierarchySituationTwoCaseTwoExclusions
      G k e0 input T phi ett base C ctx D
    change D.alpha ∉ TreeMissingColors phi B ∧ D.alpha ∉ Dn ∧
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some D.alpha at halpha
    obtain ⟨R, hroute, hminusRoute, hstarRoute,
      corrMinus, hminusMP, baseMinus, hminusCore, hminusClosure,
      hminusSupport, HMinus, hminusCount, hminusStages, hminusPositions,
      corrStar, hstarMP, baseStar, hstarCore, hstarClosure,
      hstarSupport, HStar, hstarCount, hstarStages, hstarPositions⟩ :=
      HierarchySituationTwoReorderedTreesCertified
        G k e0 input T phi ett base C ctx D.toHierarchySituationTwoTailData
    obtain ⟨hminusLen, hBminus, hminusEdge⟩ := R.minusFinal
    obtain ⟨hstarLen, hminusStar, hstarEdge⟩ := R.starFinal
    change R.minus.length = B.length + 1 at hminusLen
    have hminusLength : R.minus.length = T.length - 1 := by omega
    have hstarLength : R.star.length = T.length := by omega
    let baseExtraMissing :=
      (TreeSequenceVertexSet base.core \
        TreeSequenceVertexSet (ett.series.data.tree n.castSucc)).biUnion
          fun v => MissingColors G phi v
    let prefixUsed : Finset (Fin k) := Finset.univ.filter fun c =>
      ∃ r : Fin T.length, A.length ≤ r.val ∧
        r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
    let available := (TreeMissingColors phi B \ baseExtraMissing) \ prefixUsed
    have havailable : 2 * ett.rounds + 11 ≤ available.card :=
      (NineN G k e0 input T phi ett C.positive base H C.good
        hprefixElementary ctx.largeMissingSet (ell - 2)
        (by change ell - 2 < ell; omega)).1
    -- Only the two exact final edges are added to the used-color exclusion.
    let finalColors : Finset (Fin k) :=
      (Finset.univ.filter fun c =>
        phi (T.edge R.penultimateEdgeIndex) = some c) ∪
      (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
    have singleColorCard (f : E) :
        (Finset.univ.filter fun c => phi f = some c).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans
        (Finset.mem_filter.mp hb).2)
    have hfinalCard : finalColors.card ≤ 2 := by
      have hu := Finset.card_union_le
        (Finset.univ.filter fun c => phi (T.edge R.penultimateEdgeIndex) = some c)
        (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
      have hp := singleColorCard (T.edge R.penultimateEdgeIndex)
      have hl := singleColorCard (T.edge D.lastEdgeIndex)
      dsimp [finalColors]
      omega
    have hDnCard : Dn.card ≤ ett.rounds := by
      simpa [Dn, n] using TashkinovStoredColorsCardinality
        G k ett.rounds e0 input ett.series n
    have hremaining : ett.rounds + 9 ≤
        ((available \ finalColors) \ Dn).card := by
      have hfirst := Finset.card_le_card_sdiff_add_card
        (s := available) (t := finalColors)
      have hsecond := Finset.card_le_card_sdiff_add_card
        (s := available \ finalColors) (t := Dn)
      omega
    have hnonempty : ((available \ finalColors) \ Dn).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨beta, hbeta⟩ := hnonempty
    obtain ⟨hbetaAvailableFinal, hbetaDn⟩ := Finset.mem_sdiff.mp hbeta
    obtain ⟨hbetaAvailable, hbetaFinal⟩ := Finset.mem_sdiff.mp hbetaAvailableFinal
    obtain ⟨hbetaMissingExtra, hbetaPrefixUnused⟩ := Finset.mem_sdiff.mp hbetaAvailable
    obtain ⟨hbetaMissing, hbetaExtra⟩ := Finset.mem_sdiff.mp hbetaMissingExtra
    have hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta := by
      intro t ht hcolor
      by_cases hbefore : t.val < A.length + (ell - 2)
      · exact hbetaPrefixUnused (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, t, ht, hbefore, hcolor⟩)
      · have hp := R.penultimateEdgePosition
        have hl := D.lastEdgePosition
        have htlt := t.isLt
        have hindices : t = R.penultimateEdgeIndex ∨ t = D.lastEdgeIndex := by
          by_cases heq : t.val = R.penultimateEdgeIndex.val
          · exact Or.inl (Fin.ext heq)
          · right
            apply Fin.ext
            omega
        apply hbetaFinal
        rcases hindices with rfl | rfl
        · exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor⟩)
    have hcolorsDistinct : beta ≠ D.alpha := by
      intro heq
      exact halpha.1 (heq ▸ hbetaMissing)
    have firstMissingLe (S : TreeSequence G e0) (c : Fin k)
        (i : Fin (S.length + 1))
        (hc : c ∈ MissingColors G phi (S.vertex i)) :
        HierarchyFirstMissingPosition phi S c ≤ i := by
      let candidates : Finset (Fin (S.length + 1)) :=
        Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
      have hi : i ∈ candidates :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hn : candidates.Nonempty := ⟨i, hi⟩
      have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
        simp [HierarchyFirstMissingPosition, candidates, hn]
      rw [heq]
      exact Finset.min'_le _ _ hi
    have firstMissingMem (S : TreeSequence G e0) (c : Fin k)
        (hc : c ∈ TreeMissingColors phi S) :
        c ∈ MissingColors G phi
          (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      have hv' : ∃ i, i ∈ Finset.univ ∧ S.vertex i = v := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
      obtain ⟨i, _, hvi⟩ := hv'
      let candidates : Finset (Fin (S.length + 1)) :=
        Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
      have hi : i ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hvi.symm ▸ hcv⟩
      have hn : candidates.Nonempty := ⟨i, hi⟩
      have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
        simp [HierarchyFirstMissingPosition, candidates, hn]
      rw [heq]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
        S.vertex i ∈ TreeSequenceVertexSet S := by
      simpa only [TreeSequenceVertexSet] using
        ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨i, Finset.mem_univ _, rfl⟩)
    have missingMono {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) :
        TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
      intro c hc
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      have hv' : ∃ i, i ∈ Finset.univ ∧ S.vertex i = v := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
      obtain ⟨i, _, hvi⟩ := hv'
      have hvU : v ∈ TreeSequenceVertexSet U := by
        simpa only [TreeSequenceVertexSet] using
          ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
            ⟨Fin.castLE (Nat.succ_le_succ hSU.1) i, Finset.mem_univ _,
              (hSU.2.1 i).trans hvi⟩)
      exact Finset.mem_biUnion.mpr
        ⟨v, hvU, hcv⟩
    have hbetaT : beta ∈ TreeMissingColors phi T := missingMono hBT hbetaMissing
    have halphaT : D.alpha ∈ TreeMissingColors phi T :=
      Finset.mem_biUnion.mpr
        ⟨_, vertexMem T D.penultimateVertexIndex, D.alphaMissingPenultimate⟩
    have hbetaFirstBound : (HierarchyFirstMissingPosition phi T beta).val ≤ B.length := by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hbetaMissing
      have hv' : ∃ i, i ∈ Finset.univ ∧ B.vertex i = v := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
      obtain ⟨i, _, hvi⟩ := hv'
      have hc : beta ∈ MissingColors G phi
          (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) i)) := by
        rw [hBT.2.1 i, hvi]
        exact hcv
      have hle := firstMissingLe T beta _ hc
      change (HierarchyFirstMissingPosition phi T beta).val ≤ i.val at hle
      have hi := i.isLt
      omega
    have halphaFirst : HierarchyFirstMissingPosition phi T D.alpha =
        D.penultimateVertexIndex := by
      have hle := firstMissingLe T D.alpha D.penultimateVertexIndex
        D.alphaMissingPenultimate
      have hm := firstMissingMem T D.alpha halphaT
      have hp := D.penultimateVertexPosition
      apply Fin.ext
      change (HierarchyFirstMissingPosition phi T D.alpha).val ≤
        D.penultimateVertexIndex.val at hle
      by_contra hne
      have hbound : (HierarchyFirstMissingPosition phi T D.alpha).val ≤ B.length := by
        omega
      let ib : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi T D.alpha).val, by omega⟩
      have heq : Fin.castLE (Nat.succ_le_succ hBT.1) ib =
          HierarchyFirstMissingPosition phi T D.alpha := Fin.ext rfl
      have hmB : D.alpha ∈ MissingColors G phi (B.vertex ib) := by
        rw [← hBT.2.1 ib, heq]
        exact hm
      exact halpha.1 (Finset.mem_biUnion.mpr ⟨_, vertexMem B ib, hmB⟩)
    have hbetaPrefix : beta ∈ TreeMissingColors phi Bplus :=
      missingMono hBBplus hbetaMissing
    have halphaPrefix : D.alpha ∈ TreeMissingColors phi Bplus := by
      let i : Fin (Bplus.length + 1) := Fin.last Bplus.length
      have heq : Fin.castLE (Nat.succ_le_succ hBplusT.1) i =
          D.penultimateVertexIndex := by
        apply Fin.ext
        change Bplus.length = D.penultimateVertexIndex.val
        have hp := D.penultimateVertexPosition
        omega
      apply Finset.mem_biUnion.mpr
      refine ⟨_, vertexMem Bplus i, ?_⟩
      rw [← hBplusT.2.1 i, heq]
      exact D.alphaMissingPenultimate
    have horderedUnused :
        (beta ∉ TreeMissingColors phi A ∨ D.alpha ∉ TreeMissingColors phi A) →
          TreeVertexOrder T
            (T.vertex (HierarchyFirstMissingPosition phi T beta))
            (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
          beta ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧
              t.val < (HierarchyFirstMissingPosition phi T D.alpha).val ∧
                phi (T.edge t) = some c) := by
      intro _
      refine ⟨?_, ?_⟩
      · refine ⟨_, _, rfl, rfl, ?_⟩
        rw [halphaFirst]
        have hp := D.penultimateVertexPosition
        change (HierarchyFirstMissingPosition phi T beta).val <
          D.penultimateVertexIndex.val
        omega
      · intro hm
        obtain ⟨_, t, ht, _, hcolor⟩ := Finset.mem_filter.mp hm
        exact hbetaUnused t ht hcolor
    have hDnDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k)) Dn := by
      rw [Finset.disjoint_left]
      intro c hc hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hbetaDn hd
      · exact halpha.2.1 hd
    have hDnqDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
        (HierarchyStoredColorsAt H q) := by
      apply hDnDisjoint.mono_right
      exact Finset.sdiff_subset
    have hchange := ChangeLemma G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality hprefixElementary ctx.largeMissingSet
      beta D.alpha hcolorsDistinct ⟨hbetaPrefix, halphaPrefix⟩ horderedUnused
    have hcomponentPenultimate :
        TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
          TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
      have hc : TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
          TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T D.alpha))) := by
        by_cases hq : 0 < H.dividerCount
        · exact hchange.1 ⟨hq, Or.inr hDnqDisjoint⟩
        · have hqzero : H.dividerCount = 0 := by omega
          exact hchange.2.1 ⟨hqzero, Or.inr hDnDisjoint⟩
      simpa [halphaFirst] using hc
    have firstMissingMemBelow (S : TreeSequence G e0) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition phi S c).val < S.length) :
        c ∈ MissingColors G phi
          (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
      let candidates : Finset (Fin (S.length + 1)) :=
        Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
      by_cases hn : candidates.Nonempty
      · have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
          simp [HierarchyFirstMissingPosition, candidates, hn]
        rw [heq]
        exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      · have heq : HierarchyFirstMissingPosition phi S c = Fin.last S.length := by
          simp [HierarchyFirstMissingPosition, candidates, hn]
        rw [heq] at hlt
        simp only [Fin.val_last] at hlt
        omega
    -- A strict cutoff inside the common prefix also holds in the old display.
    have firstLowerInOld (U : TreeSequence G e0)
        (hBU : TreeSequenceInitialSegment B U) (eta : Fin k) (r : ℕ)
        (hrB : r ≤ B.length)
        (hrU : r < (HierarchyFirstMissingPosition phi U eta).val) :
        r < (HierarchyFirstMissingPosition phi T eta).val := by
      by_contra hnot
      have hpB : (HierarchyFirstMissingPosition phi T eta).val ≤ B.length := by omega
      have hpT : (HierarchyFirstMissingPosition phi T eta).val < T.length := by omega
      have hm := firstMissingMemBelow T eta hpT
      let i : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
      have hiT : Fin.castLE (Nat.succ_le_succ hBT.1) i =
          HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
      have hmU : eta ∈ MissingColors G phi
          (U.vertex (Fin.castLE (Nat.succ_le_succ hBU.1) i)) := by
        rw [hBU.2.1 i, ← hBT.2.1 i, hiT]
        exact hm
      have hle := firstMissingLe U eta _ hmU
      change (HierarchyFirstMissingPosition phi U eta).val ≤
        (HierarchyFirstMissingPosition phi T eta).val at hle
      omega
    have oldSegmentMember (eta c : Fin k) (r : Fin T.length)
        (hlo : A.length ≤ r.val)
        (hhi : r.val < (HierarchyFirstMissingPosition phi T eta).val)
        (hcolor : phi (T.edge r) = some c) :
        c ∈ HierarchySegmentColors H q eta := by
      have hq : q.succ = Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [q]
      unfold HierarchySegmentColors
      change c ∈ Finset.univ.filter (fun c =>
        ∃ r : Fin (H.stage q.succ).length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition phi T eta).val
            (H.stage q.succ).length ∧ phi ((H.stage q.succ).edge r) = some c)
      rw [hq, H.terminalStage]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, hlo, ?_, hcolor⟩
      exact lt_min hhi r.isLt
    have terminalAvoidance (U : TreeSequence G e0)
        (hBU : TreeSequenceInitialSegment B U)
        (hlen : U.length ≤ B.length + 2)
        (hfirstEdge : ∀ r : Fin U.length, r.val = B.length →
          U.edge r = T.edge D.lastEdgeIndex)
        (hsecondEdge : ∀ r : Fin U.length, r.val = B.length + 1 →
          U.edge r = T.edge R.penultimateEdgeIndex) :
        ∀ eta ∈ HierarchyStoredColorsAt H q,
          Disjoint (C.good.gamma q eta)
            (Finset.univ.filter fun c => ∃ r : Fin U.length,
              A.length ≤ r.val ∧
                r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                  phi (U.edge r) = some c) := by
      intro eta heta
      rw [Finset.disjoint_left]
      intro c hc hused
      obtain ⟨_, r, hlo, hhi, hcolor⟩ := Finset.mem_filter.mp hused
      have hrU : r.val < (HierarchyFirstMissingPosition phi U eta).val :=
        lt_of_lt_of_le hhi (Nat.min_le_left _ _)
      have hnotOld : c ∉ HierarchySegmentColors H q eta :=
        (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hc)).2
      by_cases hrB : r.val < B.length
      · let rb : Fin B.length := ⟨r.val, hrB⟩
        let rt : Fin T.length := Fin.castLE hBT.1 rb
        have hru : Fin.castLE hBU.1 rb = r := Fin.ext rfl
        have hedge : U.edge r = T.edge rt := by
          rw [← hru, hBU.2.2 rb, hBT.2.2 rb]
        have hcolorOld : phi (T.edge rt) = some c := by
          rw [← hedge]
          exact hcolor
        have hfirst := firstLowerInOld U hBU eta r.val (by omega) hrU
        exact hnotOld (oldSegmentMember eta c rt hlo hfirst hcolorOld)
      · have hrlt := r.isLt
        have hpositions : r.val = B.length ∨ r.val = B.length + 1 := by omega
        rcases hpositions with hfirst | hsecond
        · have hcolorTheta : c = D.theta := by
            rw [hfirstEdge r hfirst] at hcolor
            exact Option.some.inj (hcolor.symm.trans D.thetaOnLastEdge)
          have hpOld := firstLowerInOld U hBU eta B.length le_rfl (by omega)
          have hl := D.lastEdgePosition
          have hp := D.penultimateVertexPosition
          have hpBound : (HierarchyFirstMissingPosition phi T eta).val ≤
              D.lastEdgeIndex.val := by
            by_contra hnot
            apply hnotOld
            apply oldSegmentMember eta c D.lastEdgeIndex
            · omega
            · omega
            · rw [hcolorTheta]
              exact D.thetaOnLastEdge
          have hfirstPenultimate : HierarchyFirstMissingPosition phi T eta =
              D.penultimateVertexIndex := by
            apply Fin.ext
            omega
          have hm := firstMissingMemBelow T eta (by omega)
          rw [hfirstPenultimate] at hm
          exact hnonexceptional ⟨eta, heta, hm, hcolorTheta ▸ hc⟩
        · have hpOld := firstLowerInOld U hBU eta B.length le_rfl (by omega)
          have hp := R.penultimateEdgePosition
          apply hnotOld
          apply oldSegmentMember eta c R.penultimateEdgeIndex
          · omega
          · omega
          · rw [← hsecondEdge r hsecond]
            exact hcolor
    have hminusFirstEdge (r : Fin R.minus.length) (hr : r.val = B.length) :
        R.minus.edge r = T.edge D.lastEdgeIndex := by
      have hi : r = Fin.cast hminusLen.symm (Fin.last B.length) := by
        apply Fin.ext
        exact hr
      rw [hi]
      exact hminusEdge
    have hminusTerminalAvoidance := terminalAvoidance R.minus hBminus (by omega)
      hminusFirstEdge (by
        intro r hr
        have hi := r.isLt
        omega)
    have hBstar : TreeSequenceInitialSegment B R.star := by
      refine ⟨le_trans hBminus.1 hminusStar.1, ?_, ?_⟩
      · intro i
        exact (hminusStar.2.1
          (Fin.castLE (Nat.succ_le_succ hBminus.1) i)).trans (hBminus.2.1 i)
      · intro i
        exact (hminusStar.2.2 (Fin.castLE hBminus.1 i)).trans (hBminus.2.2 i)
    have hstarFirstEdge (r : Fin R.star.length) (hr : r.val = B.length) :
        R.star.edge r = T.edge D.lastEdgeIndex := by
      let rm : Fin R.minus.length := ⟨r.val, by omega⟩
      have hi : Fin.castLE hminusStar.1 rm = r := Fin.ext rfl
      rw [← hi, hminusStar.2.2 rm]
      exact hminusFirstEdge rm hr
    have hstarSecondEdge (r : Fin R.star.length) (hr : r.val = B.length + 1) :
        R.star.edge r = T.edge R.penultimateEdgeIndex := by
      have hi : r = Fin.cast hstarLen.symm (Fin.last R.minus.length) := by
        apply Fin.ext
        change r.val = R.minus.length
        omega
      rw [hi]
      exact hstarEdge
    have hstarTerminalAvoidance := terminalAvoidance R.star hBstar (by omega)
      hstarFirstEdge hstarSecondEdge
    have terminalData (U : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U) :
        corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc =
            ett.series.data.tree n.castSucc ∧
          corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind n ∧
          TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) = Dn := by
      rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
        rungAgreement, seriesPresentation, finalGeneratingColoring,
        ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
        extensionKindsAgree, replacementProper, replacementOneUncolored,
        replacementStable⟩
      cases replacementETT with
      | mk rounds roundsPositive replacementData above strict below generating =>
        cases rungAgreement
        have seriesSame : replacementData = replacementSeries :=
          eq_of_heq seriesPresentation
        cases seriesSame
        let i : Fin ett.rounds := ⟨ett.rounds - 1, by have hp := C.positive; omega⟩
        have hi : i.succ = n := by
          apply Fin.ext
          simp only [Fin.val_succ]
          change ett.rounds - 1 + 1 = ett.rounds
          have hp := C.positive
          omega
        have htree : replacementSeries.data.tree n.castSucc =
            ett.series.data.tree n.castSucc := by
          rw [← hi]
          exact ladderTreesAgree i
        refine ⟨htree, extensionKindsAgree n, ?_⟩
        change TashkinovStoredColors replacementSeries.data n = Dn
        dsimp [Dn]
        unfold TashkinovStoredColors
        have hn : n.val ≠ 0 := by simpa [n] using Nat.ne_of_gt C.positive
        simp only [if_neg hn]
        simp_rw [storedColorsAgree]
        rw [← finalGeneratingColoring, htree, ← ett.generatingColoring]
    have hApositive (hq : 0 < H.dividerCount) : A = H.stage q.castSucc := by
      obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
      · have hv := congrArg Fin.val hz
        simp [q] at hv
        omega
      · dsimp [A]
        rw [hi]
        rfl
    have stageLengthMono : Monotone (fun j => (H.stage j).length) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j
      exact (H.nested j).1
    have copyGood (U : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
        (baseU : HierarchyBase corr.replacementETT phi)
        (hcore : baseU.core = base.core) (hclosure : baseU.closure = base.closure)
        (K : TashkinovHierarchy corr.replacementETT baseU)
        (hcount : K.dividerCount = H.dividerCount)
        (hstages : ∀ j : Fin (K.dividerCount + 1),
          K.stage j.castSucc =
            H.stage (Fin.cast (congrArg (fun d => d + 1) hcount) j).castSucc)
        (hBU : TreeSequenceInitialSegment B U)
        (havoid : ∀ eta ∈ HierarchyStoredColorsAt H q,
          Disjoint (C.good.gamma q eta)
            (Finset.univ.filter fun c => ∃ r : Fin U.length,
              A.length ≤ r.val ∧
                r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                  phi (U.edge r) = some c)) :
        ∃ goodU : GoodHierarchy K,
          ∀ j eta, goodU.gamma j eta =
            C.good.gamma (Fin.cast (congrArg (fun d => d + 1) hcount) j) eta := by
      let index (j : Fin (K.dividerCount + 1)) : Fin (H.dividerCount + 1) :=
        Fin.cast (congrArg (fun d => d + 1) hcount) j
      let gammaU := fun j eta => C.good.gamma (index j) eta
      have hdata := terminalData U corr
      have stageEq (j : Fin (K.dividerCount + 1)) :
          K.stage j.castSucc = H.stage (index j).castSucc := hstages j
      have starredEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStarredStage K j = HierarchyStarredStage H (index j) := by
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · have hi : index 0 = 0 := Fin.ext rfl
          rw [hi]
          exact hcore
        · have hi : index i.succ = (Fin.cast hcount i).succ := Fin.ext rfl
          rw [hi]
          simp only [HierarchyStarredStage, Fin.cases_succ]
          have hs := stageEq i.succ
          rw [hi] at hs
          exact hs
      have storedEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (index j) := by
        unfold HierarchyStoredColorsAt
        dsimp only
        rw [hdata.2.2, starredEq j]
      have missingEq (j : Fin (K.dividerCount + 1)) :
          HierarchyStageMissingColors K j = HierarchyStageMissingColors H (index j) := by
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · have hi : index 0 = 0 := Fin.ext rfl
          rw [hi]
          simpa only [HierarchyStageMissingColors, Fin.cases_zero] using
            congrArg (TreeMissingColors phi) hdata.1
        · have hi : index i.succ = (Fin.cast hcount i).succ := Fin.ext rfl
          rw [hi]
          simp only [HierarchyStageMissingColors, Fin.cases_succ]
          have hs := stageEq i.succ
          rw [hi] at hs
          exact congrArg (TreeMissingColors phi) hs
      have segmentEqInternal (i : Fin K.dividerCount) (eta : Fin k) :
          HierarchySegmentColors K i.castSucc eta =
            HierarchySegmentColors H (index i.castSucc) eta := by
        let io : Fin H.dividerCount := Fin.cast hcount i
        have hnext : (index i.castSucc).succ = (index i.succ).castSucc := Fin.ext rfl
        have hinext : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        have hL : (H.stage (index i.succ).castSucc).length ≤ B.length := by
          have hpos : 0 < H.dividerCount := Nat.zero_lt_of_lt io.isLt
          have hle : (index i.succ).castSucc ≤ q.castSucc := by
            change io.val + 1 ≤ H.dividerCount
            omega
          have hlen := stageLengthMono hle
          change (H.stage (index i.succ).castSucc).length ≤
            (H.stage q.castSucc).length at hlen
          rw [← hApositive hpos] at hlen
          omega
        have hcU := HierarchyFirstMissingPositionPrefixCutoff phi B U hBU eta
          (H.stage (index i.succ).castSucc).length hL
        have hcT := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta
          (H.stage (index i.succ).castSucc).length hL
        have hcut := hcU.symm.trans hcT
        unfold HierarchySegmentColors
        dsimp only
        rw [hinext, stageEq i.succ, hnext, starredEq i.castSucc, hcut]
      have indexLast : index (Fin.last K.dividerCount) = q := by
        apply Fin.ext
        simp [index, q, hcount]
      have terminalSegmentEq (eta : Fin k) :
          HierarchySegmentColors K (Fin.last K.dividerCount) eta =
            Finset.univ.filter (fun c => ∃ r : Fin U.length,
              A.length ≤ r.val ∧
                r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                  phi (U.edge r) = some c) := by
        unfold HierarchySegmentColors
        dsimp only
        have hi : (Fin.last K.dividerCount).succ =
            Fin.last (K.dividerCount + 1) := Fin.ext rfl
        rw [hi, K.terminalStage, starredEq, indexLast]
      let goodU : GoodHierarchy K := {
        gamma := gammaU
        twoColors := by
          intro j eta heta
          apply C.good.twoColors (index j) eta
          rwa [← storedEq j]
        avoidance := by
          intro j eta heta c hc
          have hetaOld : eta ∈ HierarchyStoredColorsAt H (index j) := by
            rwa [← storedEq j]
          have hcOld : c ∈ C.good.gamma (index j) eta := hc
          have hold := Finset.mem_sdiff.mp (C.good.avoidance (index j) eta hetaOld hcOld)
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · rw [missingEq j]
            exact hold.1
          intro hseg
          by_cases hj : j.val < K.dividerCount
          · let i : Fin K.dividerCount := ⟨j.val, hj⟩
            have hi : i.castSucc = j := Fin.ext rfl
            rw [← hi, segmentEqInternal i eta] at hseg
            exact hold.2 hseg
          · have hi : j = Fin.last K.dividerCount := by apply Fin.ext; simp; omega
            subst j
            rw [terminalSegmentEq] at hseg
            rw [indexLast] at hetaOld hcOld
            exact Finset.disjoint_left.mp (havoid eta hetaOld) hcOld hseg
        disjointPairs := by
          intro j eta theta heta htheta hne
          apply C.good.disjointPairs (index j) eta theta
          · rwa [← storedEq j]
          · rwa [← storedEq j]
          · exact hne
        uniqueRefresh := by
          intro i
          let io : Fin H.dividerCount := Fin.cast hcount i
          have hn : io.succ = index i.succ := Fin.ext rfl
          have hp : io.castSucc = index i.castSucc := Fin.ext rfl
          obtain ⟨eta, heta, hunique⟩ := C.good.uniqueRefresh io
          refine ⟨eta, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · rw [storedEq, ← hn]
              exact heta.1
            · rw [stageEq, starredEq]
              simpa [gammaU, ← hn, ← hp] using heta.2.1
            · intro theta htheta hne
              rw [storedEq, ← hn] at htheta
              simpa [gammaU, ← hn, ← hp] using heta.2.2 theta htheta hne
          · intro theta htheta
            apply hunique theta
            refine ⟨?_, ?_, ?_⟩
            · rw [storedEq, ← hn] at htheta
              exact htheta.1
            · have hlocal := htheta.2.1
              rw [stageEq, starredEq] at hlocal
              simpa [gammaU, ← hn, ← hp] using hlocal
            · intro z hz hne
              have hzNew : z ∈ HierarchyStoredColorsAt K i.succ := by
                rwa [storedEq, ← hn]
              simpa [gammaU, ← hn, ← hp] using htheta.2.2 z hzNew hne
        parallelBase := by
          have hzero : (HierarchyStoredColorsAt K 0).biUnion (gammaU 0) =
              (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
            have hi : index 0 = 0 := Fin.ext rfl
            rw [storedEq, hi]
            simp only [gammaU, hi]
          dsimp only
          intro hpe
          have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
            rwa [← hdata.2.1]
          have hold := C.good.parallelBase hpeOld
          rw [hcore, hclosure, hzero, hdata.1]
          exact hold
        minusClosed := by
          intro i
          let io : Fin H.dividerCount := Fin.cast hcount i
          have hn : io.succ = index i.succ := Fin.ext rfl
          have hp : io.castSucc = index i.castSucc := Fin.ext rfl
          have hold := C.good.minusClosed io
          rw [hn, hp] at hold
          rw [stageEq, storedEq]
          simpa [gammaU] using hold }
      exact ⟨goodU, by intro j eta; rfl⟩
    obtain ⟨goodMinus, hgammaMinus⟩ := copyGood R.minus corrMinus baseMinus
      hminusCore hminusClosure HMinus hminusCount hminusStages hBminus
      hminusTerminalAvoidance
    obtain ⟨goodStar, hgammaStar⟩ := copyGood R.star corrStar baseStar
      hstarCore hstarClosure HStar hstarCount hstarStages hBstar
      hstarTerminalAvoidance
    have starredTransfer {inputU : PartialEdgeColoring E k}
        {U : TreeSequence G e0}
        {ettU : ExtendedTashkinovTree G k e0 inputU U phi}
        {baseU : HierarchyBase ettU phi}
        (K : TashkinovHierarchy ettU baseU)
        (hcore : baseU.core = base.core) (hc : K.dividerCount = H.dividerCount)
        (hs : ∀ j : Fin (K.dividerCount + 1), K.stage j.castSucc =
          H.stage (Fin.cast (congrArg (fun d => d + 1) hc) j).castSucc)
        (j : Fin (K.dividerCount + 1)) :
        HierarchyStarredStage K j =
          HierarchyStarredStage H (Fin.cast (congrArg (fun d => d + 1) hc) j) := by
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · have hi : Fin.cast (congrArg (fun d => d + 1) hc) 0 =
            (0 : Fin (H.dividerCount + 1)) := Fin.ext rfl
        rw [hi]
        exact hcore
      · have hi : Fin.cast (congrArg (fun d => d + 1) hc) i.succ =
            (Fin.cast hc i).succ := Fin.ext rfl
        rw [hi]
        simp only [HierarchyStarredStage, Fin.cases_succ]
        have h := hs i.succ
        rw [hi] at h
        exact h
    have hminusLastIndex : Fin.cast (congrArg (fun d => d + 1) hminusCount)
        (Fin.last HMinus.dividerCount) = q := by
      apply Fin.ext
      simp [q, hminusCount, H]
    have hstarLastIndex : Fin.cast (congrArg (fun d => d + 1) hstarCount)
        (Fin.last HStar.dividerCount) = q := by
      apply Fin.ext
      simp [q, hstarCount, H]
    have hminusStarred : HierarchyStarredStage HMinus
        (Fin.last HMinus.dividerCount) = A := by
      simpa only [hminusLastIndex] using starredTransfer HMinus hminusCore
        hminusCount hminusStages (Fin.last HMinus.dividerCount)
    have hstarStarred : HierarchyStarredStage HStar
        (Fin.last HStar.dividerCount) = A := by
      simpa only [hstarLastIndex] using starredTransfer HStar hstarCore
        hstarCount hstarStages (Fin.last HStar.dividerCount)
    have pathLeFull {inputU : PartialEdgeColoring E k}
        {U : TreeSequence G e0}
        {ettU : ExtendedTashkinovTree G k e0 inputU U phi}
        {baseU : HierarchyBase ettU phi} (K : TashkinovHierarchy ettU baseU) :
        HierarchyPathNumber K ≤ U.length -
          (HierarchyStarredStage K (Fin.last K.dividerCount)).length := by
      unfold HierarchyPathNumber
      dsimp only
      split
      · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ _)).1).2
      · exact le_rfl
    let ibeta : Fin (B.length + 1) :=
      ⟨(HierarchyFirstMissingPosition phi T beta).val, by omega⟩
    have hibeta : Fin.castLE (Nat.succ_le_succ hBT.1) ibeta =
        HierarchyFirstMissingPosition phi T beta := Fin.ext rfl
    have hbetaAtB : beta ∈ MissingColors G phi (B.vertex ibeta) := by
      rw [← hBT.2.1 ibeta, hibeta]
      exact firstMissingMem T beta hbetaT
    have hbetaPresentTerminal : beta ∉ MissingColors G phi
        (T.vertex D.terminalVertexIndex) := by
      intro hm
      let im : Fin (R.minus.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hBminus.1) ibeta
      have hbetaMinus : beta ∈ MissingColors G phi (R.minus.vertex im) := by
        rw [hBminus.2.1 ibeta]
        exact hbetaAtB
      have hne : R.minus.vertex im ≠ R.minus.vertex (Fin.last R.minus.length) := by
        intro heq
        have hv := congrArg Fin.val (R.minus.vertex_injective heq)
        change ibeta.val = R.minus.length at hv
        have hi := ibeta.isLt
        omega
      have hnot : ¬ ColoredVertexSetElementary G phi
          (TreeSequenceVertexSet R.minus) := by
        intro helem
        have hd := helem (vertexMem R.minus im)
          (vertexMem R.minus (Fin.last R.minus.length)) hne
        apply Finset.disjoint_left.mp hd hbetaMinus
        rw [R.minusTerminalVertex]
        exact hm
      let CMinus : HierarchyCounterexample baseMinus := {
        positive := by simpa [corrMinus.rungAgreement] using C.positive
        hierarchy := HMinus
        good := goodMinus
        maximum := hminusMP
        notElementary := hnot }
      apply ctx.lexicographicMinimality CMinus corrMinus.rungAgreement hminusCount
      apply Or.inl
      change HierarchyPathNumber HMinus < HierarchyPathNumber H
      rw [D.pathNumberFull]
      have hp := pathLeFull HMinus
      rw [hminusStarred] at hp
      omega
    let CStar : HierarchyCounterexample baseStar := {
      positive := by simpa [corrStar.rungAgreement] using C.positive
      hierarchy := HStar
      good := goodStar
      maximum := hstarMP
      notElementary := by rw [R.starVertexSet]; exact C.notElementary }
    have hstarPath : HierarchyPathNumber HStar = HierarchyPathNumber H := by
      have hle := pathLeFull HStar
      rw [hstarStarred, hstarLength] at hle
      have hnot : ¬ HierarchyPathNumber HStar < HierarchyPathNumber H := by
        intro hlt
        apply ctx.lexicographicMinimality CStar corrStar.rungAgreement hstarCount
        exact Or.inl hlt
      have hfull := D.pathNumberFull
      change HierarchyPathNumber H = ell at hfull
      omega
    have hstarLastStage : HStar.stage ⟨HStar.dividerCount, by omega⟩ =
        H.stage ⟨H.dividerCount, by omega⟩ := by
      have h := hstarStages (Fin.last HStar.dividerCount)
      rw [hstarLastIndex] at h
      exact h
    have hstarMeasure : HierarchyCounterexampleMeasure CStar =
        HierarchyCounterexampleMeasure C := by
      change (HierarchyPathNumber HStar,
          R.star.length - (HStar.stage ⟨HStar.dividerCount, by omega⟩).length) =
        (HierarchyPathNumber H,
          T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
      rw [hstarPath, hstarLength, hstarLastStage]
    let ctxStar : HierarchyMinimumCounterexampleContext G k e0
        corrStar.replacementInput R.star phi corrStar.replacementETT baseStar CStar := {
      proper := ctx.proper
      oneEdgeUncolored := ctx.oneEdgeUncolored
      lowerRung := by
        intro input' T' generating' lower hpos hlt hmax
        apply ctx.lowerRung lower hpos
        · simpa [corrStar.rungAgreement] using hlt
        · exact hmax
      fewerDividers := by
        intro input' T' generating' other hr hmax base' K goodK hdiv
        apply ctx.fewerDividers other (hr.trans corrStar.rungAgreement) hmax base' K goodK
        change K.dividerCount < HStar.dividerCount at hdiv
        rwa [hstarCount] at hdiv
      lexicographicMinimality := by
        intro input' T' generating' other base' C' hr hc
        rw [hstarMeasure]
        exact ctx.lexicographicMinimality C' (hr.trans corrStar.rungAgreement)
          (hc.trans hstarCount)
      largeMissingSet := by
        dsimp only
        rw [(terminalData R.star corrStar).1, corrStar.rungAgreement]
        exact ctx.largeMissingSet }
    have hprefixStarElementary : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyFullTailPrefix CStar
          (HierarchyFullTailLength CStar - 1))) :=
      HierarchyCounterexamplePenultimateElementary
        G k e0 corrStar.replacementInput R.star phi corrStar.replacementETT baseStar CStar
        ctxStar.proper ctxStar.oneEdgeUncolored ctxStar.lowerRung ctxStar.fewerDividers
        ctxStar.lexicographicMinimality ctxStar.largeMissingSet
    have prefixOfSegment {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) :
        TreeSequencePrefix U S.length S.positive hSU.1 = S := by
      cases S with
      | mk ls ps vs es vis eis fs ats =>
        cases U with
        | mk lu pu vu eu viu eiu fu atu =>
          rw [TreeSequence.mk.injEq]
          refine ⟨rfl, ?_, ?_⟩
          · apply heq_of_eq
            funext i
            exact hSU.2.1 i
          · apply heq_of_eq
            funext i
            exact hSU.2.2 i
    have prefixLengthEq (S : TreeSequence G e0) (i j : ℕ)
        (hi : 1 ≤ i) (hj : 1 ≤ j) (hiS : i ≤ S.length) (hjS : j ≤ S.length)
        (hij : i = j) : TreeSequencePrefix S i hi hiS = TreeSequencePrefix S j hj hjS := by
      cases hij
      rfl
    have hstarPrefix : HierarchyFullTailPrefix CStar
        (HierarchyFullTailLength CStar - 1) = R.minus := by
      have hlen : min (A.length + (R.star.length - A.length - 1))
          R.star.length = R.minus.length := by omega
      unfold HierarchyFullTailPrefix HierarchyFullTailLength
      dsimp only [CStar]
      refine (prefixLengthEq R.star _ R.minus.length _ R.minus.positive _ hminusStar.1
        ?_).trans (prefixOfSegment hminusStar)
      rw [hstarStarred]
      exact hlen
    have hminusElementary : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet R.minus) := by
      change ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyFullTailPrefix CStar
          (HierarchyFullTailLength CStar - 1))) at hprefixStarElementary
      rwa [hstarPrefix] at hprefixStarElementary
    let iaStar : Fin (R.star.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length)
    have hiaStar : iaStar.val = R.minus.length := rfl
    have halphaStarVertex : R.star.vertex iaStar = T.vertex D.terminalVertexIndex :=
      (hminusStar.2.1 (Fin.last R.minus.length)).trans R.minusTerminalVertex
    have halphaMinus : D.alpha ∈ TreeMissingColors phi R.minus :=
      Finset.mem_biUnion.mpr ⟨_, vertexMem R.minus (Fin.last R.minus.length),
        R.minusTerminalVertex.symm ▸ D.alphaMissingTerminal⟩
    have halphaStar : D.alpha ∈ TreeMissingColors phi R.star :=
      missingMono hminusStar halphaMinus
    have halphaFirstStar : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar := by
      have hm : D.alpha ∈ MissingColors G phi (R.star.vertex iaStar) := by
        rw [halphaStarVertex]
        exact D.alphaMissingTerminal
      have hle := firstMissingLe R.star D.alpha iaStar hm
      have hmFirst := firstMissingMem R.star D.alpha halphaStar
      apply Fin.ext
      change (HierarchyFirstMissingPosition phi R.star D.alpha).val ≤ iaStar.val at hle
      by_contra hne
      have hbound : (HierarchyFirstMissingPosition phi R.star D.alpha).val ≤ B.length := by
        omega
      let i : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi R.star D.alpha).val, by omega⟩
      have hi : Fin.castLE (Nat.succ_le_succ hBstar.1) i =
          HierarchyFirstMissingPosition phi R.star D.alpha := Fin.ext rfl
      have hmB : D.alpha ∈ MissingColors G phi (B.vertex i) := by
        rw [← hBstar.2.1 i, hi]
        exact hmFirst
      exact halpha.1 (Finset.mem_biUnion.mpr ⟨_, vertexMem B i, hmB⟩)
    have hbetaStarBound : (HierarchyFirstMissingPosition phi R.star beta).val ≤ B.length := by
      have hm : beta ∈ MissingColors G phi
          (R.star.vertex (Fin.castLE (Nat.succ_le_succ hBstar.1) ibeta)) := by
        rw [hBstar.2.1 ibeta]
        exact hbetaAtB
      have hle := firstMissingLe R.star beta _ hm
      change (HierarchyFirstMissingPosition phi R.star beta).val ≤ ibeta.val at hle
      have hi := ibeta.isLt
      omega
    have hbetaStarVertex :
        R.star.vertex (HierarchyFirstMissingPosition phi R.star beta) =
          T.vertex (HierarchyFirstMissingPosition phi T beta) := by
      have hcStar := HierarchyFirstMissingPositionPrefixCutoff
        phi B R.star hBstar beta B.length le_rfl
      have hcOld := HierarchyFirstMissingPositionPrefixCutoff
        phi B T hBT beta B.length le_rfl
      have heq : (HierarchyFirstMissingPosition phi R.star beta).val =
          (HierarchyFirstMissingPosition phi T beta).val := by omega
      have hi : Fin.castLE (Nat.succ_le_succ hBstar.1) ibeta =
          HierarchyFirstMissingPosition phi R.star beta := Fin.ext heq.symm
      rw [← hi, hBstar.2.1 ibeta, ← hBT.2.1 ibeta, hibeta]
    have hbetaMinus : beta ∈ TreeMissingColors phi R.minus := missingMono hBminus hbetaMissing
    have hmissingStar :
        beta ∈ TreeMissingColors phi (HierarchyFullTailPrefix CStar
          (HierarchyFullTailLength CStar - 1)) ∧
        D.alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix CStar
          (HierarchyFullTailLength CStar - 1)) := by
      rw [hstarPrefix]
      exact ⟨hbetaMinus, halphaMinus⟩
    have horderedStar :
        (beta ∉ TreeMissingColors phi (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)) ∨
          D.alpha ∉ TreeMissingColors phi (HierarchyStarredStage HStar (Fin.last HStar.dividerCount))) →
        TreeVertexOrder R.star
          (R.star.vertex (HierarchyFirstMissingPosition phi R.star beta))
          (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha)) ∧
        beta ∉ (Finset.univ.filter fun c => ∃ t : Fin R.star.length,
          (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition phi R.star D.alpha).val ∧
              phi (R.star.edge t) = some c) := by
      intro _
      refine ⟨?_, ?_⟩
      · refine ⟨_, _, rfl, rfl, ?_⟩
        rw [halphaFirstStar]
        change (HierarchyFirstMissingPosition phi R.star beta).val < iaStar.val
        omega
      · intro hm
        obtain ⟨_, t, ht, hhi, hcolor⟩ := Finset.mem_filter.mp hm
        rw [hstarStarred] at ht
        rw [halphaFirstStar] at hhi
        by_cases hbefore : t.val < B.length
        · let tb : Fin B.length := ⟨t.val, hbefore⟩
          let toriginal : Fin T.length := Fin.castLE hBT.1 tb
          have hi : Fin.castLE hBstar.1 tb = t := Fin.ext rfl
          have hedge : R.star.edge t = T.edge toriginal := by
            rw [← hi, hBstar.2.2 tb, hBT.2.2 tb]
          rw [hedge] at hcolor
          exact hbetaUnused toriginal ht hcolor
        · have heq : t.val = B.length := by omega
          rw [hstarFirstEdge t heq] at hcolor
          apply hbetaUnused D.lastEdgeIndex _ hcolor
          have hl := D.lastEdgePosition
          omega
    have hstarDnDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
        (TashkinovStoredColors corrStar.replacementETT.series.data
          (Fin.last corrStar.replacementETT.rounds)) := by
      rw [(terminalData R.star corrStar).2.2]
      exact hDnDisjoint
    have hstarDnqDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
        (HierarchyStoredColorsAt HStar (Fin.last HStar.dividerCount)) :=
      hstarDnDisjoint.mono_right Finset.sdiff_subset
    have hchangeStar := ChangeLemma G k e0 corrStar.replacementInput R.star phi
      corrStar.replacementETT baseStar CStar ctxStar.proper ctxStar.oneEdgeUncolored
      ctxStar.lowerRung ctxStar.fewerDividers ctxStar.lexicographicMinimality
      hprefixStarElementary ctxStar.largeMissingSet beta D.alpha hcolorsDistinct
      hmissingStar horderedStar
    have hcomponentTerminal :
        TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
          TwoColorComponent G phi beta D.alpha
            (Sum.inl (T.vertex D.terminalVertexIndex)) := by
      have hc : TwoColorComponent G phi beta D.alpha
            (Sum.inl (R.star.vertex (HierarchyFirstMissingPosition phi R.star beta))) =
          TwoColorComponent G phi beta D.alpha
            (Sum.inl (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha))) := by
        by_cases hq : 0 < HStar.dividerCount
        · exact hchangeStar.1 ⟨hq, Or.inr hstarDnqDisjoint⟩
        · have hz : HStar.dividerCount = 0 := by omega
          exact hchangeStar.2.1 ⟨hz, Or.inr hstarDnDisjoint⟩
      simpa only [hbetaStarVertex, halphaFirstStar, halphaStarVertex] using hc
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let yp := T.vertex D.penultimateVertexIndex
    let yt := T.vertex D.terminalVertexIndex
    have hbp : vb ≠ yp := by
      intro heq
      have hv := congrArg Fin.val (T.vertex_injective heq)
      have hp := D.penultimateVertexPosition
      omega
    have hbt : vb ≠ yt := by
      intro heq
      have hv := congrArg Fin.val (T.vertex_injective heq)
      have hp := D.terminalVertexPosition
      omega
    have hpt : yp ≠ yt := by
      intro heq
      have hv := congrArg Fin.val (T.vertex_injective heq)
      have hp := D.penultimateVertexPosition
      have ht := D.terminalVertexPosition
      omega
    let graph := TwoColorIncidenceGraph G phi beta D.alpha
    obtain ⟨a, b, p, hp, hsupport⟩ :=
      TwoColorComponentSpanningPath G phi beta D.alpha ctx.proper (Sum.inl vb)
    have endpoint (w : V)
        (hw : Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb))
        (hd : @SimpleGraph.degree _ graph (Sum.inl w) (Fintype.ofFinite _) ≤ 1) :
        Sum.inl w = a ∨ Sum.inl w = b := by
      have hleaf : (graph.neighborSet (Sum.inl w)).Subsingleton := by
        letI : Fintype (graph.neighborSet (Sum.inl w)) := Fintype.ofFinite _
        have hc : Fintype.card (graph.neighborSet (Sum.inl w)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact hd
        intro x hx y hy
        exact congrArg Subtype.val
          (Fintype.card_le_one_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩)
      have hwpath : Sum.inl w ∈ p.support := by
        change Sum.inl w ∈ {x | x ∈ p.support}
        rw [hsupport]
        exact hw
      by_contra hend
      push_neg at hend
      exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
        hend.1 hend.2 hleaf) hwpath
    have hgraphSwap : TwoColorIncidenceGraph G phi D.alpha beta = graph := by
      ext x y
      cases x <;> cases y <;> simp [graph, TwoColorIncidenceGraph, or_comm]
    have hdegreeAlpha (w : V) (hm : D.alpha ∈ MissingColors G phi w) :
        @SimpleGraph.degree _ graph (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
      rw [← hgraphSwap]
      exact MissingColorIncidenceEndpoint G phi D.alpha beta hcolorsDistinct.symm ctx.proper w hm
    have hendsBeta : Sum.inl vb = a ∨ Sum.inl vb = b := by
      apply endpoint vb
      · change graph.connectedComponentMk (Sum.inl vb) = graph.connectedComponentMk (Sum.inl vb)
        rfl
      · exact MissingColorIncidenceEndpoint G phi beta D.alpha hcolorsDistinct ctx.proper vb
          (firstMissingMem T beta hbetaT)
    have hendsPenultimate : Sum.inl yp = a ∨ Sum.inl yp = b := by
      apply endpoint yp
      · rw [hcomponentPenultimate]
        change graph.connectedComponentMk (Sum.inl yp) = graph.connectedComponentMk (Sum.inl yp)
        rfl
      · exact hdegreeAlpha yp D.alphaMissingPenultimate
    have hendsTerminal : Sum.inl yt = a ∨ Sum.inl yt = b := by
      apply endpoint yt
      · rw [hcomponentTerminal]
        change graph.connectedComponentMk (Sum.inl yt) = graph.connectedComponentMk (Sum.inl yt)
        rfl
      · exact hdegreeAlpha yt D.alphaMissingTerminal
    have hbp' : Sum.inl vb ≠ (Sum.inl yp : Sum V E) := fun h => hbp (Sum.inl.inj h)
    have hbt' : Sum.inl vb ≠ (Sum.inl yt : Sum V E) := fun h => hbt (Sum.inl.inj h)
    have hpt' : Sum.inl yp ≠ (Sum.inl yt : Sum V E) := fun h => hpt (Sum.inl.inj h)
    rcases hendsBeta with hba | hbb <;>
      rcases hendsPenultimate with hpa | hpb <;>
      rcases hendsTerminal with hta | htb
    all_goals first
      | exact hbp' (hba.trans hpa.symm)
      | exact hbp' (hbb.trans hpb.symm)
      | exact hbt' (hba.trans hta.symm)
      | exact hbt' (hbb.trans htb.symm)
      | exact hpt' (hpa.trans hta.symm)
      | exact hpt' (hpb.trans htb.symm)
