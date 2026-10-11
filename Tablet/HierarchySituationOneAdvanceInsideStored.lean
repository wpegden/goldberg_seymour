import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TreeSequencePrefix
import Tablet.P2813_T1_TerminalRoute
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceSuffix
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

-- [TABLET NODE: HierarchySituationOneAdvanceInsideStored]
theorem HierarchySituationOneAdvanceInsideStored {V E : Type*}
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
    (hinside :
      let H := P.counterexample.hierarchy
      alpha ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount)) :
    i + 1 ∈ HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx := by
-- BODY
  classical
  have hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C := by
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
    clear * - G psi a b hne hproper B helem u v w hu hv huv hwu hwv hau hbv hw hsame
    let J := TwoColorIncidenceGraph G psi a b
    have leaf (x : V) (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
        (J.neighborSet (Sum.inl x)).Subsingleton := by
      have hd : @SimpleGraph.degree _ J (Sum.inl x) (Fintype.ofFinite _) ≤ 1 := by
        rcases hx with hx | hx
        · exact MissingColorIncidenceEndpoint G psi a b hne hproper x hx
        · have hJ : TwoColorIncidenceGraph G psi b a = J := by
            ext z z'
            cases z <;> cases z' <;> simp [J, TwoColorIncidenceGraph, or_comm]
          rw [← hJ]
          exact MissingColorIncidenceEndpoint G psi b a hne.symm hproper x hx
      letI : Fintype (J.neighborSet (Sum.inl x)) := Fintype.ofFinite _
      have hc : Fintype.card (J.neighborSet (Sum.inl x)) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact hd
      intro z hz z' hz'
      exact congrArg Subtype.val
        (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z', hz'⟩)
    have hnot : Sum.inl w ∉ TwoColorComponent G psi a b (Sum.inl u) := by
      intro hwC
      obtain ⟨s, t, p, hp, hsupport⟩ :=
        TwoColorComponentSpanningPath G psi a b hproper (Sum.inl u)
      have endpoint (x : V)
          (hxC : Sum.inl x ∈ TwoColorComponent G psi a b (Sum.inl u))
          (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
          Sum.inl x = s ∨ Sum.inl x = t := by
        by_contra hh
        push_neg at hh
        have hxP : Sum.inl x ∈ p.support := by
          change Sum.inl x ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact hxC
        exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
          hh.1 hh.2 (leaf x hx)) hxP
      have huE := endpoint u (by rfl) (Or.inl hau)
      have hvE := endpoint v (by rw [hsame]; rfl) (Or.inr hbv)
      have hwE := endpoint w hwC hw
      rcases huE with huE | huE <;> rcases hvE with hvE | hvE <;>
        rcases hwE with hwE | hwE
      all_goals first
        | exact huv (Sum.inl.inj (huE.trans hvE.symm))
        | exact hwu (Sum.inl.inj (hwE.trans huE.symm))
        | exact hwv (Sum.inl.inj (hwE.trans hvE.symm))
    have hdis : Disjoint (TwoColorComponent G psi a b (Sum.inl w))
        (TwoColorComponent G psi a b (Sum.inl u)) := by
      rcases TwoColorComponentsDisjoint G psi a b (Sum.inl w) (Sum.inl u) with hh | hh
      · exact (hnot (by rw [← hh]; rfl)).elim
      · exact hh
    refine ⟨hdis, ⟨hne, Sum.inl w, by rfl, leaf w hw⟩, ?_⟩
    let Q := TwoColorComponent G psi a b (Sum.inl w)
    let tau := TwoColorComponentSwap G psi a b (Sum.inl w)
    have huQ : Sum.inl u ∉ Q := by
      intro hh
      exact Set.disjoint_left.mp hdis hh (by rfl)
    have hvQ : Sum.inl v ∉ Q := by
      intro hh
      exact Set.disjoint_left.mp hdis hh (by rw [hsame]; rfl)
    obtain ⟨outside, -, -, unaffected⟩ :=
      TwoColorComponentSwapMissingBehavior G psi a b hne hproper (Sum.inl w)
    have edgeIn {x : V} {e : E} (hx : Sum.inl x ∈ Q)
        (hi : Incident G x e) (hc : psi e = some a ∨ psi e = some b) :
        Sum.inr e ∈ Q := by
      change J.connectedComponentMk (Sum.inl x) = J.connectedComponentMk (Sum.inl w) at hx
      change J.connectedComponentMk (Sum.inr e) = J.connectedComponentMk (Sum.inl w)
      have ha : J.Adj (Sum.inr e) (Sum.inl x) := ⟨hi, hc⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans hx
    intro x hx
    by_cases hxQ : Sum.inl x ∈ Q
    · have haNot : a ∉ MissingColors G psi x := by
        intro ha
        by_cases hxu : x = u
        · exact huQ (hxu ▸ hxQ)
        · exact Finset.disjoint_left.mp (helem hx hu hxu) ha hau
      have hbNot : b ∉ MissingColors G psi x := by
        intro hb
        by_cases hxv : x = v
        · exact hvQ (hxv ▸ hxQ)
        · exact Finset.disjoint_left.mp (helem hx hv hxv) hb hbv
      have present (c : Fin k) (hc : c ∉ MissingColors G psi x) :
          ∃ e, Incident G x e ∧ psi e = some c := by
        simpa [MissingColors, PresentColors] using hc
      obtain ⟨ea, hia, hca⟩ := present a haNot
      obtain ⟨eb, hib, hcb⟩ := present b hbNot
      have haNew : a ∉ MissingColors G tau x := by
        have heQ := edgeIn hxQ hib (Or.inr hcb)
        have hcol : tau eb = some a := by
          simp [tau, TwoColorComponentSwap, show Sum.inr eb ∈
            TwoColorComponent G psi a b (Sum.inl w) from heQ, hcb, hne.symm]
        exact fun hm => (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eb, hib, hcol⟩)
      have hbNew : b ∉ MissingColors G tau x := by
        have heQ := edgeIn hxQ hia (Or.inl hca)
        have hcol : tau ea = some b := by
          simp [tau, TwoColorComponentSwap, show Sum.inr ea ∈
            TwoColorComponent G psi a b (Sum.inl w) from heQ, hca]
        exact fun hm => (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ea, hia, hcol⟩)
      ext c
      by_cases hca : c = a
      · subst c
        exact iff_of_false haNew haNot
      · by_cases hcb : c = b
        · subst c
          exact iff_of_false hbNew hbNot
        · exact unaffected x c hca hcb
    · exact outside x hxQ

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
      change i < (T.length - A.length) - 1 at hiUpper
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
    have firstFixed (psi tau : PartialEdgeColoring E k)
        (hmissing : ∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G tau v = MissingColors G psi v) (c : Fin k) :
        HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c := by
      clear * - G T B psi tau hmissing c firstLe firstMem hBT vertexMem
      have early (j : Fin (T.length + 1)) (hj : j.val < T.length) :
          MissingColors G tau (T.vertex j) = MissingColors G psi (T.vertex j) := by
        let x : Fin (B.length + 1) := ⟨j.val, by dsimp [B, TreeSequencePrefix]; omega⟩
        have hx : Fin.castLE (Nat.succ_le_succ hBT.1) x = j := Fin.ext rfl
        rw [← hx, hBT.2.1 x]
        exact hmissing _ (vertexMem B x)
      apply Fin.ext
      apply Nat.le_antisymm
      · by_contra hn
        have hlt : (HierarchyFirstMissingPosition psi T c).val < T.length := by
          have := (HierarchyFirstMissingPosition tau T c).isLt
          omega
        have hm := firstMem psi c hlt
        rw [← early _ hlt] at hm
        have := firstLe tau c _ hm
        omega
      · by_contra hn
        have hlt : (HierarchyFirstMissingPosition tau T c).val < T.length := by
          have := (HierarchyFirstMissingPosition psi T c).isLt
          omega
        have hm := firstMem tau c hlt
        rw [early _ hlt] at hm
        have := firstLe psi c _ hm
        omega
    have stageSwitch (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (X : TreeSequence G e0) (hAX : TreeSequenceInitialSegment A X)
        (hAXlt : A.length < X.length) (hXB : TreeSequenceInitialSegment X B)
        (a b eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount))
        (haGamma : a ∈ R.counterexample.good.gamma
          (Fin.last R.counterexample.hierarchy.dividerCount) eta)
        (hetaCut : (HierarchyFirstMissingPosition R.coloring T eta).val ≤ X.length)
        (jb : Fin (B.length + 1)) (hjb : A.length < jb.val)
        (hjbX : jb.val ≤ X.length)
        (hb : b ∈ MissingColors G R.coloring (B.vertex jb))
        (hw : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
          b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)))
        (haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
          R.coloring (T.edge t) ≠ some a)
        (hbException : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
          R.coloring (T.edge t) = some b →
            TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
              (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
            b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
              (Fin.last R.corresponding.replacementETT.rounds)) :
        ∃ S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
          (∀ v ∈ TreeSequenceVertexSet B,
            MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
          (∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
            S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
          (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
            b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
          (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
            a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) := by
      clear * - G T A B R X hAX hAXlt hXB a b eta heta haGamma hetaCut jb hjb hjbX hb hw
        haUnused hbException trans common starEq hAT hAB hBT elementary vertexMem firstLe
        firstMem firstAt firstFixed componentData fullB
      let H := R.counterexample.hierarchy
      let q := Fin.last H.dividerCount
      let n := Fin.last R.corresponding.replacementETT.rounds
      let Tn := R.corresponding.replacementETT.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors R.corresponding.replacementETT.series.data n
      have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
          (i : Fin (H.dividerCount + 2)), i.val ≤ j →
          TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
        intro j
        induction j with
        | zero =>
            intro hj i hi
            have he : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
            subst i
            exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        | succ j ih =>
            intro hj i hi
            by_cases heq : i.val = j + 1
            · have he : i = ⟨j + 1, hj⟩ := Fin.ext heq
              subst i
              exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
            · exact trans (ih (by omega) i (by omega)) (H.nested ⟨j, by omega⟩)
      have lastPositive (hq : H.dividerCount ≠ 0) :
          HierarchyStarredStage H q = H.stage ⟨H.dividerCount, by omega⟩ := by
        unfold HierarchyStarredStage
        obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
        · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
        · rw [hi]
          simp only [Fin.cases_succ]
          congr 1
          exact Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
      have hTnCore : TreeSequenceInitialSegment Tn R.replacementBase.core := by
        by_cases hpe : R.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.PE
        · exact (R.replacementBase.parallel hpe).2.2.some.leftSegment
        · rw [R.replacementBase.nonparallel hpe]
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      have coreA : TreeSequenceInitialSegment R.replacementBase.core A := by
        rw [← starEq R]
        by_cases hq : H.dividerCount = 0
        · have he : HierarchyStarredStage H q = R.replacementBase.core := by
            simp [HierarchyStarredStage, q, hq, Fin.last]
          rw [he]
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · rw [lastPositive hq]
          exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
            (by change 1 ≤ H.dividerCount; omega))
      have hTnA := trans hTnCore coreA
      have stageCase :
          (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring
            (H.stage ⟨H.dividerCount, by omega⟩)) ∨
          (H.dividerCount = 0 ∧ a ∈ TreeMissingColors R.coloring Tn) := by
        have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta heta haGamma)).1
        by_cases hq : H.dividerCount = 0
        · right
          refine ⟨hq, ?_⟩
          simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
        · left
          refine ⟨by omega, ?_⟩
          unfold HierarchyStageMissingColors at hm
          dsimp only at hm
          obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
          · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
          · rw [hi] at hm
            simp only [Fin.cases_succ] at hm
            have he : i.succ.castSucc = (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) :=
              Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
            simpa only [he] using hm
      have haA : a ∈ TreeMissingColors R.coloring A := by
        rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
        · rw [← starEq R, lastPositive (by omega)]
          exact hm
        · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hm
          exact Finset.mem_biUnion.mpr ⟨v,
            TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
      have hbOutside : b ∉ TreeMissingColors R.coloring A := by
        rintro hm
        obtain ⟨v, hvA, hmv⟩ := Finset.mem_biUnion.mp hm
        obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hvA
        have hne : v ≠ B.vertex jb := by
          intro he
          have hh := T.vertex_injective ((hAT.2.1 j).trans
            (hj.trans (he.trans (hBT.2.1 jb).symm)))
          have hh := congrArg Fin.val hh
          have := j.isLt
          change j.val = jb.val at hh
          omega
        exact Finset.disjoint_left.mp (elementary R
          (TreeSequenceInitialSegmentVertexSetSubset hAB hvA) (vertexMem B jb) hne) hmv hb
      have hne : a ≠ b := by rintro rfl; exact hbOutside haA
      have hbB : b ∈ TreeMissingColors R.coloring B :=
        Finset.mem_biUnion.mpr ⟨B.vertex jb, vertexMem B jb, hb⟩
      have haB : a ∈ TreeMissingColors R.coloring B := by
        obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
        exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hc⟩
      have iaLe : (HierarchyFirstMissingPosition R.coloring T a).val ≤ A.length := by
        obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
        obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
        have hcT : a ∈ MissingColors G R.coloring
            (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j)) := by
          rw [hAT.2.1 j, hj]; exact hc
        have hh := firstLe R.coloring a _ hcT
        change (HierarchyFirstMissingPosition R.coloring T a).val ≤ j.val at hh
        have := j.isLt
        omega
      have ibEq := firstAt R b jb hb
      have haFirst := firstMem R.coloring a (by
        have := hAB.1
        have hblen : B.length = T.length - 1 := rfl
        omega)
      let ja : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T a).val,
        by have := hAB.1; omega⟩
      have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) ja =
          HierarchyFirstMissingPosition R.coloring T a := Fin.ext rfl
      have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb =
          HierarchyFirstMissingPosition R.coloring T b := Fin.ext ibEq.symm
      have haFirstB : a ∈ MissingColors G R.coloring (B.vertex ja) := by
        rw [← hBT.2.1 ja, jaEq]; exact haFirst
      have hordered : TreeVertexOrder T
          (T.vertex (HierarchyFirstMissingPosition R.coloring T a))
          (T.vertex (HierarchyFirstMissingPosition R.coloring T b)) :=
        ⟨_, _, rfl, rfl, by omega⟩
      have hunused : a ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
          A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition R.coloring T b).val ∧
            R.coloring (T.edge t) = some c) := by
        intro hh
        obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
        exact haUnused t hlo (by omega) hc
      have hprefixR : ColoredVertexSetElementary G R.coloring
          (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - 1))) := by
        rw [fullB R]
        exact elementary R
      have hmissingR : a ∈ TreeMissingColors R.coloring
          (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)) ∧
          b ∈ TreeMissingColors R.coloring
          (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)) := by
        rw [fullB R]
        exact ⟨haB, hbB⟩
      have change := ChangeLemma G k e0 R.corresponding.replacementInput T R.coloring
        R.corresponding.replacementETT R.replacementBase R.counterexample
        R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
        R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
        hprefixR
        R.minimumContext.largeMissingSet a b hne
        hmissingR
        (by
          dsimp only
          rw [starEq R]
          intro _
          exact ⟨hordered, hunused⟩)
      have hsame : TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)) =
          TwoColorComponent G R.coloring a b (Sum.inl (B.vertex jb)) := by
        have hh : TwoColorComponent G R.coloring a b
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a))) =
            TwoColorComponent G R.coloring a b
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T b))) := by
          rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
          · exact change.1 ⟨hq, Or.inl hm⟩
          · exact change.2.1 ⟨hq, Or.inl hm⟩
        rw [← jaEq, ← jbEq, hBT.2.1 ja, hBT.2.1 jb] at hh
        exact hh
      obtain ⟨hdis, hpath, hmissing⟩ := componentData R.coloring a b hne
        R.minimumContext.proper (TreeSequenceVertexSet B) (elementary R)
        (B.vertex ja) (B.vertex jb) (T.vertex (Fin.last T.length))
        (vertexMem B ja) (vertexMem B jb)
        (by intro hh; have := congrArg Fin.val (B.vertex_injective hh); dsimp [ja] at this; omega)
        (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 ja).symm)
            have hh := congrArg Fin.val hh
            change T.length = ja.val at hh
            have := ja.isLt
            have hblen : B.length = T.length - 1 := rfl
            omega)
        (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jb).symm)
            have hh := congrArg Fin.val hh
            change T.length = jb.val at hh
            have := jb.isLt
            have hblen : B.length = T.length - 1 := rfl
            omega)
        haFirstB hb hw hsame
      let sigma := TwoColorComponentSwap G R.coloring a b (Sum.inl (T.vertex (Fin.last T.length)))
      have hsproper : IsProperEdgeColoring G sigma :=
        TwoColorComponentSwapProper G R.coloring a b hne R.minimumContext.proper _
      have hsone : IsOneEdgeUncolored sigma e0 := by
        refine ⟨?_, ?_⟩
        · simp [sigma, TwoColorComponentSwap, R.minimumContext.oneEdgeUncolored.1]
        · intro e he
          obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 e he
          by_cases hm : Sum.inr e ∈ TwoColorComponent G R.coloring a b
              (Sum.inl (T.vertex (Fin.last T.length)))
          · by_cases hca : c = a
            · subst c; exact ⟨b, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩
            · by_cases hcb : c = b
              · subst c; exact ⟨a, by simp [sigma, TwoColorComponentSwap, hm, hc, hne.symm]⟩
              · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc, hca, hcb]⟩
          · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩
      have hcase :
          (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage ⟨H.dividerCount, by omega⟩)) ∨
          (H.dividerCount = 0 ∧ (a ∈ TreeMissingColors R.coloring Tn ∨
            (a ∈ TreeMissingColors R.coloring (HierarchyStarredStage H q) ∧ a ∉ Dn ∧ b ∉ Dn))) := by
        rcases stageCase with h | ⟨hq, hm⟩
        · exact Or.inl h
        · exact Or.inr ⟨hq, Or.inl hm⟩
      have hdisFirst : Disjoint (TwoColorComponent G R.coloring a b
          (Sum.inl (T.vertex (Fin.last T.length))))
          (TwoColorComponent G R.coloring a b
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a)))) := by
        rw [← jaEq, hBT.2.1 ja]
        exact hdis
      have changed := StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T R.coloring
        R.corresponding.replacementETT R.replacementBase R.counterexample
        R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
        R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
        hprefixR
        R.minimumContext.largeMissingSet a b hne
        hmissingR
        _ hpath sigma rfl hcase hdisFirst
      have hweak : HierarchyWeaklyStable H q sigma := changed.1
      have baseStable : if R.corresponding.replacementETT.series.data.kind n =
          some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
        else StableColoring Tn Dn R.coloring sigma := by
        have extract (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
            (if R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE then
              CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
            else StableColoring Tn Dn R.coloring sigma) :=
          Fin.cases (fun h => h) (fun _ h => h.1) j
        exact extract q hweak
      have stable : StableColoring Tn Dn R.coloring sigma := by
        by_cases hp : R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE
        · exact (if_pos hp ▸ baseStable).1
        · simpa only [hp, if_false] using baseStable
      have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = R.coloring (A.edge t) := by
        have fixed (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
            ∀ t : Fin (HierarchyStarredStage H j).length,
              sigma ((HierarchyStarredStage H j).edge t) = R.coloring ((HierarchyStarredStage H j).edge t) := by
          refine Fin.cases ?_ (fun i => ?_) j
          · intro _
            exact P2813_T1_BaseDisplayedEdges G k e0 R.corresponding.replacementInput T R.coloring
              R.corresponding.replacementETT R.replacementBase sigma
              R.minimumContext.oneEdgeUncolored hsone baseStable
          · intro hh t
            change sigma ((H.stage i.succ.castSucc).edge t) =
              R.coloring ((H.stage i.succ.castSucc).edge t)
            by_cases ht : t.val = 0
            · have he : (H.stage i.succ.castSucc).edge t = e0 := by
                rw [show t = ⟨0, (H.stage i.succ.castSucc).positive⟩ from Fin.ext ht]
                exact (H.stage i.succ.castSucc).first_edge
              rw [he, hsone.1, R.minimumContext.oneEdgeUncolored.1]
            · exact hh.2.1 t (by omega)
        rw [← starEq R]
        exact fixed q hweak
      have fixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
          sigma (T.edge t) = R.coloring (T.edge t) := by
        intro t hlo hhi
        by_cases hbcol : R.coloring (T.edge t) = some b
        · obtain ⟨hi, hc⟩ := hbException t hlo hhi hbcol
          exact stable.1 _ hi ⟨b, Finset.mem_union_right _ hc, hbcol⟩
        · have haNo := haUnused t hlo hhi
          simp [sigma, TwoColorComponentSwap, haNo, hbcol]
      have hXT := trans hXB hBT
      let XM := TreeSequencePrefix X (X.length - 1) (by have := A.positive; omega) (by omega)
      have hXMX : TreeSequenceInitialSegment XM X :=
        ⟨by dsimp [XM, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
      have prefixFixed (t : Fin X.length) (ht : Tn.length ≤ t.val) :
          sigma (X.edge t) = R.coloring (X.edge t) := by
        by_cases hlow : t.val < A.length
        · let j : Fin A.length := ⟨t.val, hlow⟩
          have he : Fin.castLE hAX.1 j = t := Fin.ext rfl
          rw [← he, hAX.2.2 j]
          exact fixedA j
        · rw [← hXT.2.2 t]
          exact fixedPrefix (Fin.castLE hXT.1 t) (by change A.length ≤ t.val; omega) t.isLt
      have routes :
          ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence sigma Tn X) ∨
          ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
            R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ f seed, R.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X)) ∧
          TashkinovAugmentationSequence R.coloring X T := by
        rcases P2813_T1_TerminalRoute G k e0 R.corresponding.replacementInput T R.coloring
            R.corresponding.replacementETT with ⟨hp, hseq⟩ |
            ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
        · have hsourceX := trans hTnA hAX
          have hpre := TashkinovAugmentationSequenceRestrict R.coloring Tn X T hseq hsourceX hXT
          refine ⟨Or.inl ⟨hp, ?_⟩,
            TashkinovAugmentationSequenceSuffix R.coloring Tn X T hseq hsourceX hXT⟩
          exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma Tn XM X
            hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega) prefixFixed
            (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
              (trans hXMX hXB) hv))
        · have hseedX := common
            (TashkinovAugmentationSequenceInitialSegment R.coloring seed T hseq) hXT
            (by have hl := hseed.1; have := hTnA.1; change seed.length = Tn.length + 1 at hl; omega)
          have hpre := TashkinovAugmentationSequenceRestrict R.coloring seed X T hseq hseedX hXT
          refine ⟨Or.inr ⟨hp, f, seed, hedges, hseed, ?_⟩,
            TashkinovAugmentationSequenceSuffix R.coloring seed X T hseq hseedX hXT⟩
          exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma seed XM X
            hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega)
            (fun t ht => prefixFixed t (by have hl := hseed.1; change seed.length = Tn.length + 1 at hl; omega))
            (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
              (trans hXMX hXB) hv))
      have hsplit : a ∈ TreeMissingColors sigma X ∧ b ∈ TreeMissingColors sigma X := by
        have subset (j : Fin (B.length + 1)) (hj : j.val ≤ X.length) :
            B.vertex j ∈ TreeSequenceVertexSet X := by
          let x : Fin (X.length + 1) := ⟨j.val, by omega⟩
          have hx : Fin.castLE (Nat.succ_le_succ hXB.1) x = j := Fin.ext rfl
          rw [← hx, hXB.2.1 x]
          exact vertexMem X x
        refine ⟨Finset.mem_biUnion.mpr ⟨B.vertex ja, subset ja (by dsimp [ja]; omega), ?_⟩,
          Finset.mem_biUnion.mpr ⟨B.vertex jb, subset jb hjbX, ?_⟩⟩
        · rw [hmissing _ (vertexMem B ja)]; exact haFirstB
        · rw [hmissing _ (vertexMem B jb)]; exact hb
      have gammaCut : ∀ eta', eta' ∈ HierarchyStoredColorsAt H q →
          (a ∈ R.counterexample.good.gamma q eta' ∨ b ∈ R.counterexample.good.gamma q eta') →
            (HierarchyFirstMissingPosition R.coloring T eta').val ≤ X.length := by
        intro eta' heta' hh
        rcases hh with hh | hh
        · have he : eta' = eta := by
            by_contra hn
            exact Finset.disjoint_left.mp
              (R.counterexample.good.disjointPairs q eta' eta heta' heta hn) hh haGamma
          simpa only [he] using hetaCut
        · have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta' heta' hh)).1
          have hmb : b ∈ TreeMissingColors R.coloring A := by
            rcases stageCase with ⟨hq, _⟩ | ⟨hq, _⟩
            · have hhq : H.dividerCount ≠ 0 := by omega
              unfold HierarchyStageMissingColors at hm
              dsimp only at hm
              obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
              · exact (hhq (by simpa [q] using congrArg Fin.val hz)).elim
              · rw [hi] at hm
                simp only [Fin.cases_succ] at hm
                have he : HierarchyStarredStage H q = H.stage i.succ.castSucc := by
                  change Fin.cases (motive := fun _ => TreeSequence G e0)
                    R.replacementBase.core (fun i => H.stage i.succ.castSucc) q = _
                  rw [hi]
                  rfl
                rw [← starEq R, he]
                exact hm
            · have hmT : b ∈ TreeMissingColors R.coloring Tn := by
                simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
              obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmT
              exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
          exact (hbOutside hmb).elim
      obtain ⟨_, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
        StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T R.coloring
          R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
          a b hne (by rw [fullB R]; exact ⟨haB, hbB⟩)
          _ hpath sigma rfl hcase hdisFirst X (by dsimp only; rw [starEq R]; exact hAX)
          (by dsimp only; rw [starEq R]; exact hAXlt) (by rw [fullB R]; exact hXB)
          (by dsimp only; rw [starEq R]; exact fixedPrefix) routes.1 routes.2 hsplit
          (by rw [fullB R]; exact hmissing)
          (fun c _ => firstFixed R.coloring sigma hmissing c) gammaCut
      have terminal := TwoColorComponentSwapMissingBehavior G R.coloring a b hne
        R.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))
      have hterminalA : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
          b ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
        terminal.2.1 _ (by rfl)
      have hterminalB : b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
          a ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
        terminal.2.2.1 _ (by rfl)
      have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
        intro he
        rcases hw with hw | hw
        · have hbNew : b ∈ MissingColors G sigma (B.vertex jb) := by
            rw [hmissing _ (vertexMem B jb)]; exact hb
          exact Finset.disjoint_left.mp (he
            (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jb))
            (vertexMem T (Fin.last T.length)) (by
              intro hh
              have hh := T.vertex_injective ((hBT.2.1 jb).trans hh)
              have hh := congrArg Fin.val hh
              change jb.val = T.length at hh
              have := jb.isLt
              have hblen : B.length = T.length - 1 := rfl
              omega))
            hbNew (hterminalA hw)
        · have haNew : a ∈ MissingColors G sigma (B.vertex ja) := by
            rw [hmissing _ (vertexMem B ja)]; exact haFirstB
          exact Finset.disjoint_left.mp (he
            (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B ja))
            (vertexMem T (Fin.last T.length)) (by
              intro hh
              have hh := T.vertex_injective ((hBT.2.1 ja).trans hh)
              have hh := congrArg Fin.val hh; dsimp [ja] at hh; omega))
            haNew (hterminalB hw)
      let CS : HierarchyCounterexample bs := {
        positive := by rw [corr.rungAgreement]; exact R.counterexample.positive
        hierarchy := K
        good := goodK
        maximum := hmaximum
        notElementary := hnotElementary }
      obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
        R sigma corr bs CS hsameGood
      refine ⟨S, ?_, ?_, ?_, ?_⟩ <;> rw [hS]
      · exact hmissing
      · exact fixedPrefix
      · exact hterminalA
      · exact hterminalB
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
    have advance (m : ℕ) (hmLower : 1 ≤ m)
        (hmUpper : m < HierarchyFullTailLength C - 1)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k)
        (ha : alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C m).vertex (Fin.last (HierarchyFullTailPrefix C m).length)))
        (haLast : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
        (hAlphaStored : alpha ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)) :
        m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      have hm : 1 ≤ m := hmLower
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
      obtain ⟨gamma, hgamma, hgap⟩ := gammaChoice P alpha hAlphaStored (T.edge tnext)
      obtain ⟨P1, hmissing1, hfixed1, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
        gamma alpha alpha hAlphaStored hgamma
        (by rw [firstAt P alpha jm haM]; dsimp [jm, X, TreeSequencePrefix]; omega)
        jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
        haM (Or.inr haLast) (avoidM P alpha gamma hAlphaStored hgamma haM hgap)
        (excM P alpha haM)
      have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1 haLast
      have haM1 : alpha ∈ MissingColors G P1.coloring (B.vertex jm) := by
        rw [hmissing1 _ (vertexMem B jm)]; exact haM
      have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
        rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
      obtain ⟨hAlphaStored1, heqGamma⟩ := gammaTransport P P1 alpha hAlphaStored
      have hgamma1 : gamma ∈ P1.counterexample.good.gamma
          (Fin.last P1.counterexample.hierarchy.dividerCount) alpha := by
        rw [← heqGamma]; exact hgamma
      have hgap1 : P1.coloring (T.edge tnext) ≠ some gamma := by
        rw [hfixed1 tnext (by dsimp [tnext]; omega)
          (by dsimp [tnext, X, TreeSequencePrefix]; omega)]
        exact hgap
      obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
        gamma theta alpha hAlphaStored1 hgamma1
        (by rw [firstAt P1 alpha jm haM1]; dsimp [jm, X, TreeSequencePrefix]; omega)
        jnext (by dsimp [jnext]; omega) (by rfl)
        htheta1 (Or.inl hgLast) (avoidM P1 alpha gamma hAlphaStored1 hgamma1 haM1 hgap1)
        (excNext P1 theta htheta1)
      exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
        (hterminal2 hgLast)

    exact advance i hiLower hiUpper P alpha hcommon.1 hcommon.2 hinside
