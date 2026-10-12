import Tablet.ChangeLemma
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
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
import Tablet.HierarchySituationThreeColorChoice
import Tablet.HierarchySituationThreeClaimJMinusOneEmpty
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.Td
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeInterchangeable
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentTashkinovSplice
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc1
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.P2813_T1_TerminalRoute
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: HierarchySituationThreeComponentIntersectionShortening]
theorem HierarchySituationThreeComponentIntersectionShortening
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
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) /\
        alpha ∈ TreeMissingColors P.coloring B /\
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          exists eta : Fin k, eta ∈ D /\
            alpha ∈ P.counterexample.good.gamma q eta /\
            (HierarchyFirstMissingPosition P.coloring T eta).val <=
              B.length))
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          exists r : Fin T.length,
            A.length <= r.val /\ r.val < A.length + j /\
              P.coloring (T.edge r) = some c
      beta ≠ alpha /\
        beta ∈ TreeMissingColors P.coloring B /\
        beta ∉ Gamma /\ beta ∉ tailUsedThroughJ /\
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D /\
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ))
    (hintersection :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      ∃ u ∈ TreeSequenceVertexSet X,
        Sum.inl u ∈ TwoColorComponent G P.coloring alpha beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    False := by
-- BODY
  classical
  open scoped Sym2 in
    let H := P.counterexample.hierarchy
    let R := P.corresponding.replacementETT
    let mu := P.coloring
    let n := Fin.last R.rounds
    let Tn := R.series.data.tree n.castSucc
    let q := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    generalize hjdef : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper halpha hbeta hintersection
    let ell := HierarchyFullTailLength C
    let B := HierarchyFullTailPrefix C (j - 2)
    let X := HierarchyFullTailPrefix C (j - 1)
    let y := T.vertex (Fin.last T.length)
    have reflSeg (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
      ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    have trans {S U W : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U)
        (hUW : TreeSequenceInitialSegment U W) :
        TreeSequenceInitialSegment S W := by as_aux_lemma =>
      clear * - hSU hUW
      refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
      · intro i
        exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
      · intro i
        exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
    have common {S U W : TreeSequence G e0}
        (hSW : TreeSequenceInitialSegment S W)
        (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
        TreeSequenceInitialSegment S U := by as_aux_lemma =>
      clear * - hSW hUW hlen
      refine ⟨hlen, ?_, ?_⟩
      · intro i
        exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
      · intro i
        exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
    have sameLast : ∀ {a b : ℕ}
        (s : Fin (a + 2) → TreeSequence G e0)
        (t : Fin (b + 2) → TreeSequence G e0)
        (u v : TreeSequence G e0), a = b → HEq s t → u = v →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.succ.castSucc) (Fin.last a) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.succ.castSucc) (Fin.last b) := by
      intro a b s t u v hab hst huv
      cases hab
      cases eq_of_heq hst
      cases huv
      rfl
    have hAold : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A :=
      sameLast _ _ _ _ P.sameGood.1.2.1 P.sameGood.1.2.2.1 P.sameGood.1.1
    have hpOld : HierarchyPathNumber H = j := by as_aux_lemma =>
      rw [← hjdef]
      unfold HierarchyPathNumber
      dsimp only
      rw [hAold]
    have hell : ell = T.length - A.length := by
      dsimp [ell, HierarchyFullTailLength]
      rw [hAold]
    have hjlow : 2 ≤ j := hpathLower
    have hjhigh : j < ell := hpathUpper
    have chain : ∀ (b : ℕ) (hb : b < H.dividerCount + 2)
        (a : Fin (H.dividerCount + 2)), a.val ≤ b →
        TreeSequenceInitialSegment (H.stage a) (H.stage ⟨b, hb⟩) := by as_aux_lemma =>
      clear * - H reflSeg trans
      intro b
      induction b with
      | zero =>
        intro hb a ha
        have he : a = 0 := Fin.ext (Nat.eq_zero_of_le_zero ha)
        subst a
        exact reflSeg _
      | succ b ih =>
        intro hb a ha
        by_cases he : a.val = b + 1
        · have heq : a = ⟨b + 1, hb⟩ := Fin.ext he
          subst a
          exact reflSeg _
        · exact trans (ih (by omega) a (by omega)) (H.nested ⟨b, by omega⟩)
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    have hAT : TreeSequenceInitialSegment A T := by
      simpa only [q, Fin.succ_last, H.terminalStage] using starNext q
    have lastZero (hz : H.dividerCount = 0) : A = P.replacementBase.core := by
      simp [A, q, HierarchyStarredStage, hz, Fin.last]
    have lastPositive (hz : H.dividerCount ≠ 0) :
        A = H.stage ⟨H.dividerCount, by omega⟩ := by
      unfold A HierarchyStarredStage
      obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
      · have hv := congrArg Fin.val hzero
        simp only [q, Fin.val_last, Fin.val_zero] at hv
        contradiction
      · rw [hi]
        simp only [Fin.cases_succ]
        congr 1
        apply Fin.ext
        simpa [q] using (congrArg Fin.val hi).symm
    have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
      by_cases hz : H.dividerCount = 0
      · rw [lastZero hz]
        exact reflSeg _
      · rw [lastPositive hz]
        exact trans H.coreInsideFirst (chain H.dividerCount (by omega)
          ⟨1, by omega⟩ (by change 1 ≤ H.dividerCount; omega))
    have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
      by_cases hpe : R.series.data.kind n = some TashkinovExtensionKind.PE
      · exact (P.replacementBase.parallel hpe).2.2.some.leftSegment
      · rw [P.replacementBase.nonparallel hpe]
        exact reflSeg _
    have hTnA := trans hTnCore coreA
    have prefixT (r : ℕ) : TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have prefixLen (r : ℕ) (hr : r ≤ ell) :
        (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
      clear * - hAold hell hAT hr
      change min ((HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length + r) T.length = _
      rw [hAold]
      apply Nat.min_eq_left
      have hlen := hAT.1
      omega
    have hBLen : B.length = A.length + (j - 2) := prefixLen _ (by omega)
    have hXLen : X.length = A.length + (j - 1) := prefixLen _ (by omega)
    have hBT := prefixT (j - 2)
    have hXT := prefixT (j - 1)
    have hAB : TreeSequenceInitialSegment A B := common hAT hBT (by omega)
    have hBX : TreeSequenceInitialSegment B X := common hBT hXT (by omega)
    have hAX := trans hAB hBX
    have hTnB := trans hTnA hAB
    have hTnX := trans hTnB hBX
    have hBXLen : X.length = B.length + 1 := by omega
    have hXshort : X.length < T.length := by omega
    have hyX : y ∉ TreeSequenceVertexSet X := by as_aux_lemma =>
      clear * - hXT hXshort
      intro hy
      obtain ⟨i, hi⟩ : ∃ i, X.vertex i = y := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hy
      have hv := T.vertex_injective ((hXT.2.1 i).trans hi)
      have hh := congrArg Fin.val hv
      change i.val = T.length at hh
      have hiBound := i.isLt
      change i.val < X.length + 1 at hiBound
      omega
    have hyB : y ∉ TreeSequenceVertexSet B :=
      fun hy => hyX (TreeSequenceInitialSegmentVertexSetSubset hBX hy)
    rcases halpha with ⟨hay, haB, haChoice⟩
    rcases hbeta with ⟨hba, hbB, hbGamma, hbUnused, hbChoice⟩
    have hab : alpha ≠ beta := Ne.symm hba
    have missingMono {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) :
        TreeMissingColors mu S ⊆ TreeMissingColors mu U := by
      intro c hc
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hm⟩
    have haX : alpha ∈ TreeMissingColors mu X := missingMono hBX haB
    have hbX : beta ∈ TreeMissingColors mu X := missingMono hBX hbB
    have equalSeg {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) :
        S = U := by as_aux_lemma =>
      clear * - hSU hlen
      cases S with
      | mk sl sp sv se svi sei sf sa =>
        cases U with
        | mk ul up uv ue uvi uei uf ua =>
          dsimp only at hlen
          subst ul
          have hv : uv = sv := funext hSU.2.1
          have he : ue = se := funext hSU.2.2
          subst uv
          subst ue
          rfl
    have firstLe (W : TreeSequence G e0) (c : Fin k)
        (i : Fin (W.length + 1)) (hi : c ∈ MissingColors G mu (W.vertex i)) :
        (HierarchyFirstMissingPosition mu W c).val ≤ i.val := by as_aux_lemma =>
      clear * - W c i hi mu
      let candidates := Finset.univ.filter fun t : Fin (W.length + 1) =>
        c ∈ MissingColors G mu (W.vertex t)
      have hm : i ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hn : candidates.Nonempty := ⟨i, hm⟩
      unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact Finset.min'_le candidates i hm
    have firstMem (W : TreeSequence G e0) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition mu W c).val < W.length) :
        c ∈ MissingColors G mu (W.vertex (HierarchyFirstMissingPosition mu W c)) := by as_aux_lemma =>
      clear * - W c hlt mu
      let candidates := Finset.univ.filter fun t : Fin (W.length + 1) =>
        c ∈ MissingColors G mu (W.vertex t)
      by_cases hn : candidates.Nonempty
      · unfold HierarchyFirstMissingPosition
        rw [dif_pos hn]
        exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      · have hh : (HierarchyFirstMissingPosition mu W c).val = W.length := by
          unfold HierarchyFirstMissingPosition
          rw [dif_neg hn]
          rfl
        omega
    have firstBound {W Z : TreeSequence G e0}
        (hWT : TreeSequenceInitialSegment W Z) (c : Fin k)
        (hc : c ∈ TreeMissingColors mu W) :
        (HierarchyFirstMissingPosition mu Z c).val ≤ W.length := by
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨i, hi⟩ : ∃ i, W.vertex i = v := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
      have hmT : c ∈ MissingColors G mu
          (Z.vertex (Fin.castLE (Nat.succ_le_succ hWT.1) i)) := by
        rw [hWT.2.1, hi]
        exact hm
      exact (firstLe Z c _ hmT).trans (Nat.le_of_lt_succ i.isLt)
    have stableClosed (W : TreeSequence G e0) (D : Finset (Fin k))
        (rho sigma : PartialEdgeColoring E k)
        (hp : IsProperEdgeColoring G rho) (ho : IsOneEdgeUncolored rho e0)
        (hps : IsProperEdgeColoring G sigma) (hos : IsOneEdgeUncolored sigma e0)
        (hst : StableColoring W D rho sigma)
        (hcl : ColoredVertexSetClosed G rho (TreeSequenceVertexSet W)) :
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet W) := by as_aux_lemma =>
      clear * - W D rho sigma hp ho hps hos hst hcl
      intro f c v hf hv hfc hmissing
      have hm : c ∈ MissingColors G rho v := by
        rw [← hst.2 v hv]
        exact hmissing
      have hinc : TreeIncidentEdge W f := by
        have hfData : ∃ u ∈ TreeSequenceVertexSet W,
            ∃ w ∉ TreeSequenceVertexSet W, G.ends f = s(u, w) := by
          simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hf
        obtain ⟨u, hu, w, hw, he⟩ := hfData
        refine ⟨u, hu, ?_⟩
        change u ∈ G.ends f
        rw [he]
        exact Sym2.mem_mk_left _ _
      have heq := (sc1 G e0 W D rho sigma hp ho hps hos).mp hst f hinc
        (Or.inr ⟨c, Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨v, hv, hm⟩), hfc⟩)
      exact hcl hf hv (heq.symm.trans hfc) hm
    have nonparallelClosed
        (hk : R.series.data.kind n ≠ some TashkinovExtensionKind.PE) :
        ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn) := by as_aux_lemma =>
      clear * - R n Tn mu hk stableClosed
      have step := R.series.certified n
      generalize hn : n = z at step
      cases step with
      | initial =>
        have hv := congrArg Fin.val hn
        simp only [n, Fin.val_last, Fin.val_zero] at hv
        have := R.roundsPositive
        omega
      | SE i hp ho hc hnc hnr choice halt hcol hstored hedges hkind
          hvertex houtside hdelta hgamma seed hadjoin hclosure hordered hstrict =>
        have hin : i.succ = n := hn.symm
        have hm : mu = choice.selected := by
          have hg : mu = R.series.data.coloring n := R.generatingColoring
          rw [← hin, hcol] at hg
          exact hg
        rw [hm]
        have htree : Tn = R.series.data.tree i.succ.castSucc := by rw [hin]
        rw [htree]
        exact @stableClosed _ _ _ _ hp ho choice.selectedProper
          choice.selectedOneUncolored choice.selectedStable @hc
      | PE i hp ho hc hnc hnr choice halt gamma hgamma second hps hos hst
          exit hcol hproper hone hstored hedges hkind hvertex houtside hdelta
          hgammaEq hclosure hordered hstrict =>
        exfalso
        exact hk (hn.symm ▸ hkind)
      | RE i hp ho hc hnc available hcol hstored hedges hkind hvertex
          houtside hdelta hgamma seed hadjoin hclosure hordered hstrict =>
        have hin : i.succ = n := hn.symm
        have hm : mu = R.series.data.coloring i.castSucc := by
          have hg : mu = R.series.data.coloring n := R.generatingColoring
          rw [← hin, hcol] at hg
          exact hg
        rw [hm, show Tn = R.series.data.tree i.succ.castSucc by rw [hin]]
        exact @hc
    have hmod : ModColoring R mu := by as_aux_lemma =>
      clear * - P R mu
      apply Td G k e0 P.corresponding.replacementInput T mu R P.maximum
        P.counterexample.positive P.minimumContext.lowerRung mu
        P.minimumContext.proper P.minimumContext.oneEdgeUncolored
      rw [← R.generatingColoring]
      exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    -- At the nonparallel zero-divider boundary, the prescribed seed must survive.
    have exceptional : H.dividerCount = 0 → j = 2 →
        R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
        ¬ ∃ u ∈ TreeSequenceVertexSet B,
          Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y) := by
      intro hz hj hk hmeet
      have hABeq : A = B := equalSeg hAB (by omega)
      have hATneq : A = Tn := (lastZero hz).trans (P.replacementBase.nonparallel hk)
      have hBTneq : B = Tn := hABeq.symm.trans hATneq
      have haA : alpha ∈ TreeMissingColors mu A := by rw [hABeq]; exact haB
      have hbA : beta ∈ TreeMissingColors mu A := by rw [hABeq]; exact hbB
      have haclosed : TreeColorSetClosed G mu A {alpha} := by
        intro c hc
        have he : c = alpha := Finset.mem_singleton.mp hc
        subst c
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro f hf
        simp only [BoundaryColorEdges, Finset.mem_filter] at hf
        obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp haA
        have hclosed : ColoredVertexSetClosed G mu (TreeSequenceVertexSet A) := by
          rw [hATneq]
          exact nonparallelClosed hk
        exact hclosed hf.1 hv hf.2 hm
      have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet
          (HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - 1))) :=
        HierarchyCounterexamplePenultimateElementary
        G k e0 P.corresponding.replacementInput T mu R P.replacementBase
        P.counterexample P.minimumContext.proper P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
      have missingPen :
          let Z := HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - 1)
          alpha ∈ TreeMissingColors mu Z ∧ beta ∈ TreeMissingColors mu Z := by
        let Z := HierarchyFullTailPrefix P.counterexample
          (HierarchyFullTailLength P.counterexample - 1)
        have hZT : TreeSequenceInitialSegment Z T :=
          ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
        have hZLen : Z.length = T.length - 1 := by
          change min (A.length + ((T.length - A.length) - 1)) T.length = T.length - 1
          omega
        have hBZ : TreeSequenceInitialSegment B Z := common hBT hZT (by omega)
        exact ⟨missingMono hBZ haB, missingMono hBZ hbB⟩
      have change := ChangeLemma G k e0 P.corresponding.replacementInput T mu R
        P.replacementBase P.counterexample P.minimumContext.proper
        P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
        P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality
        helem P.minimumContext.largeMissingSet alpha beta hab missingPen
        (by
          dsimp only
          exact fun h => False.elim (h.elim (fun ha => ha haA) (fun hb => hb hbA)))
      obtain ⟨hsame, hinter⟩ := change.2.2 ⟨haA, haclosed⟩
      let va := T.vertex (HierarchyFirstMissingPosition mu T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition mu T beta)
      have vaB : va ∈ TreeSequenceVertexSet B := by
        let ia : Fin (B.length + 1) :=
          ⟨(HierarchyFirstMissingPosition mu T alpha).val,
            Nat.lt_succ_of_le (firstBound hBT alpha haB)⟩
        have hi : Fin.castLE (Nat.succ_le_succ hBT.1) ia =
            HierarchyFirstMissingPosition mu T alpha := Fin.ext rfl
        rw [show va = B.vertex ia by rw [← hBT.2.1 ia, hi]]
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨ia, rfl⟩
      have vbB : vb ∈ TreeSequenceVertexSet B := by
        let ib : Fin (B.length + 1) :=
          ⟨(HierarchyFirstMissingPosition mu T beta).val,
            Nat.lt_succ_of_le (firstBound hBT beta hbB)⟩
        have hi : Fin.castLE (Nat.succ_le_succ hBT.1) ib =
            HierarchyFirstMissingPosition mu T beta := Fin.ext rfl
        rw [show vb = B.vertex ib by rw [← hBT.2.1 ib, hi]]
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨ib, rfl⟩
      have hva : alpha ∈ MissingColors G mu va :=
        firstMem T alpha (lt_of_le_of_lt (firstBound hBT alpha haB)
          (lt_of_lt_of_le (by omega : B.length < X.length) hXT.1))
      have hvb : beta ∈ MissingColors G mu vb :=
        firstMem T beta (lt_of_le_of_lt (firstBound hBT beta hbB)
          (lt_of_lt_of_le (by omega : B.length < X.length) hXT.1))
      have elemA : ColoredVertexSetElementary G mu (TreeSequenceVertexSet A) := by
        intro v hv w hw hne
        have hZT : TreeSequenceInitialSegment
            (HierarchyFullTailPrefix P.counterexample
              (HierarchyFullTailLength P.counterexample - 1)) T :=
          ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
        have hAZ : TreeSequenceInitialSegment A
            (HierarchyFullTailPrefix P.counterexample
              (HierarchyFullTailLength P.counterexample - 1)) :=
          common hAT hZT (by
            change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
            omega)
        exact helem (TreeSequenceInitialSegmentVertexSetSubset hAZ hv)
          (TreeSequenceInitialSegmentVertexSetSubset hAZ hw) hne
      have vaA : va ∈ TreeSequenceVertexSet A := by rw [hABeq]; exact vaB
      have vbA : vb ∈ TreeSequenceVertexSet A := by rw [hABeq]; exact vbB
      obtain ⟨hdis, hyPath, hswap⟩ := P2905_T2_ElementaryTerminalComponent
        G mu alpha beta hab P.minimumContext.proper (TreeSequenceVertexSet A)
        elemA va vb y vaA vbA (fun he => hyB (he ▸ vaB))
        (fun he => hyB (he ▸ vbB)) hva hvb (Or.inl hay) hsame
      have vaPath : TwoColorPathComponent G mu alpha beta (Sum.inl va) := by
        let J := TwoColorIncidenceGraph G mu alpha beta
        letI : Fintype (J.neighborSet (Sum.inl va)) := Fintype.ofFinite _
        have hd := MissingColorIncidenceEndpoint G mu alpha beta hab
          P.minimumContext.proper va hva
        have hc : Fintype.card (J.neighborSet (Sum.inl va)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact hd
        refine ⟨hab, Sum.inl va, by rfl, ?_⟩
        intro z hz w hw
        exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨w, hw⟩)
      have hmeetA : ∃ u ∈ TreeSequenceVertexSet A,
          Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y) := by
        rw [hABeq]
        exact hmeet
      have heq := hinter (Sum.inl y) (Sum.inl va) hyPath vaPath hmeetA
        ⟨va, vaA, by rfl⟩
      exact Set.disjoint_left.mp hdis (heq.symm ▸ (show
        Sum.inl va ∈ TwoColorComponent G mu alpha beta (Sum.inl va) by rfl)) (by rfl)
    -- Choose the shorter base unless the component first meets its new last vertex.
    have splice : ∃ (S U : TreeSequence G e0),
        TreeSequenceInitialSegment B S ∧ TreeSequenceInitialSegment S X ∧
        TreeSequenceInitialSegment S U ∧ S.length < U.length ∧
        TashkinovAugmentationSequence mu S U ∧
        U.vertex (Fin.last U.length) = y ∧
        (∀ r : Fin U.length, S.length ≤ r.val →
          mu (U.edge r) = some alpha ∨ mu (U.edge r) = some beta) ∧
        (∀ r : Fin U.length, X.length ≤ r.val →
          G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)) ∧
        (H.dividerCount = 0 → j = 2 →
          R.series.data.kind n ≠ some TashkinovExtensionKind.PE → S = X) := by as_aux_lemma =>
      by_cases hmeet : ∃ u ∈ TreeSequenceVertexSet B,
          Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)
      · obtain ⟨u, U, hu, huQ, hBU, hlen, haug, hlast, hnew⟩ :=
          TwoColorComponentTashkinovSplice G mu B alpha beta y
            P.minimumContext.proper hab haB hbB hyB hmeet
        refine ⟨B, U, reflSeg _, hBX, hBU, hlen, haug, hlast,
          fun r hr => (hnew r hr).2.2.2.1, ?_, ?_⟩
        · intro r hr
          have hn := (hnew r (by omega)).2.2.2.2
          rw [if_neg (by omega)] at hn
          exact hn
        · intro hz hj hk
          exact False.elim (exceptional hz hj hk hmeet)
      · obtain ⟨u, U, hu, huQ, hXU, hlen, haug, hlast, hnew⟩ :=
          TwoColorComponentTashkinovSplice G mu X alpha beta y
            P.minimumContext.proper hab haX hbX hyX hintersection
        have huLast : u = X.vertex (Fin.last X.length) := by as_aux_lemma =>
          clear * - hmeet hBX hBXLen hu huQ
          obtain ⟨i, hi⟩ : ∃ i, X.vertex i = u := by
            simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hu
          by_cases hh : i.val ≤ B.length
          · have hb : u ∈ TreeSequenceVertexSet B := by
              let ib : Fin (B.length + 1) := ⟨i.val, by omega⟩
              have hc : Fin.castLE (Nat.succ_le_succ hBX.1) ib = i := Fin.ext rfl
              rw [← hi, ← hc, hBX.2.1 ib]
              simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨ib, rfl⟩
            exact False.elim (hmeet ⟨u, hb, huQ⟩)
          · have he : i = Fin.last X.length := Fin.ext (by
              change i.val = X.length
              have := i.isLt
              omega)
            exact hi.symm.trans (congrArg X.vertex he)
        refine ⟨X, U, hBX, reflSeg _, hXU, hlen, haug, hlast,
          fun r hr => (hnew r hr).2.2.2.1, ?_, fun _ _ _ => rfl⟩
        intro r hr
        have hn := (hnew r hr).2.2.2.2
        by_cases he : r.val = X.length
        · rw [if_pos he, huLast] at hn
          have hv : U.vertex r.castSucc = X.vertex (Fin.last X.length) := by
            have hi : Fin.castLE (Nat.succ_le_succ hXU.1) (Fin.last X.length) =
                r.castSucc := Fin.ext he.symm
            rw [← hi, hXU.2.1]
          rw [hv]
          exact hn
        · rw [if_neg he] at hn
          exact hn
    obtain ⟨S, U, hBS, hSX, hSU, hSUstrict, hSUaug, hUlast, hUcolors,
      hUpath, hScorner⟩ := splice
    have hST := trans hSX hXT
    have hAS := trans hAB hBS
    have hAU := trans hAS hSU
    have hBU := trans hBS hSU
    have hAUstrict : A.length < U.length := lt_of_le_of_lt hAS.1 hSUstrict
    have hTnS := trans hTnB hBS
    have hTnU := trans hTnS hSU
    have hTnUstrict : Tn.length < U.length := lt_of_le_of_lt hTnS.1 hSUstrict
    -- Retain the actual last-series route before certifying the new terminal tree.
    have hroute :
        (R.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu Tn U) ∨
        ((R.series.data.kind n = some TashkinovExtensionKind.SE ∨
            R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            R.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence mu seed U) := by as_aux_lemma =>
      rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu R
        with ⟨hpe, haug⟩ | ⟨hkind, f, seed, hedges, hadjoin, hinc, hcolor, haug⟩
      · exact Or.inl ⟨hpe,
          (TashkinovAugmentationSequenceRestrict mu Tn S T haug hTnS hST).trans hSUaug⟩
      · have hnonpe : R.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
          rcases hkind with h | h <;> rw [h] <;> decide
        have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T haug
        have hseedLen : seed.length = Tn.length + 1 := hadjoin.1
        have hseedS : TreeSequenceInitialSegment seed S := by
          apply common hseedT hST
          by_cases hz : H.dividerCount = 0
          · have hAeq : A = Tn := (lastZero hz).trans (P.replacementBase.nonparallel hnonpe)
            have hAlem : A.length = Tn.length := congrArg TreeSequence.length hAeq
            by_cases hj : j = 2
            · have hseq := hScorner hz hj hnonpe
              rw [hseq]
              omega
            · have hbs := hBS.1
              omega
          · obtain ⟨r, hr, he⟩ := HierarchyNonparallelFirstEdge H f hkind hedges
            change r.val = Tn.length at hr
            have hfirstA : TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩) A := by
              rw [lastPositive hz]
              exact chain H.dividerCount (by omega) ⟨1, by omega⟩
                (by change 1 ≤ H.dividerCount; omega)
            have hf := r.isLt
            have hfa := hfirstA.1
            have has := hAS.1
            omega
        exact Or.inr ⟨hkind, f, seed, hedges, hadjoin,
          (TashkinovAugmentationSequenceRestrict mu seed S T haug hseedS hST).trans hSUaug⟩
    obtain ⟨corr⟩ := hmod.2.2 U hTnU hTnUstrict hroute
    have hMP := MaximumPropertyTransport G k e0 R mu hmod U corr P.maximum
    obtain ⟨baseU, hcore, hclosure, hsupport⟩ := HierarchyBaseCorrespondingTransport
      G k e0 P.corresponding.replacementInput T U mu R corr P.replacementBase
    rcases corr with ⟨newInput, newSeries, newETT, hround, hseries, hgen,
      htrees, hstored, hedges, hkinds, hproper, hone, hstable⟩
    rcases newETT with ⟨rounds, roundsPositive, replacementSeries,
      above, strict, below, generating⟩
    cases hround
    have hseriesEq : replacementSeries = newSeries := eq_of_heq hseries
    cases hseriesEq
    let RU : ExtendedTashkinovTree G k e0 newInput U mu :=
      { rounds := R.rounds
        roundsPositive := roundsPositive
        series := newSeries
        abovePenultimate := above
        strictAbovePenultimate := strict
        belowFinal := below
        generatingColoring := generating }
    change HierarchyBase RU mu at baseU
    change MaximumProperty RU at hMP
    have hTnEq : newSeries.data.tree n.castSucc = Tn := by
      let z : Fin R.rounds := ⟨R.rounds - 1, by have := R.roundsPositive; omega⟩
      have hz : z.succ = n := Fin.ext (by have := R.roundsPositive; dsimp [z, n]; omega)
      rw [← hz]
      simpa only [Tn, ← hz] using htrees z
    have hstoredEq : TashkinovStoredColors newSeries.data n =
        TashkinovStoredColors R.series.data n := by as_aux_lemma =>
      clear * - hstored hTnEq hgen R n Tn
      have hmissing : TreeMissingColors (newSeries.data.coloring n)
          (newSeries.data.tree n.castSucc) =
          TreeMissingColors (R.series.data.coloring n) Tn := by
        rw [← hgen, ← R.generatingColoring, hTnEq]
      unfold TashkinovStoredColors
      split
      · rfl
      · rw [hmissing]
        congr 1
        apply congrArg (Finset.univ.biUnion)
        funext i
        rw [hstored i]
    have stageA (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) A := by
      by_cases hz : H.dividerCount = 0
      · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        rw [hi]
        simpa only [Fin.castSucc_zero, H.baseStage] using hTnA
      · rw [lastPositive hz]
        exact chain H.dividerCount (by omega) i.castSucc
          (Nat.le_of_lt_succ i.isLt)
    have stageU (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) U := trans (stageA i) hAU
    have stageB (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) B := trans (stageA i) hAB
    have hdivB (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
      have hl := congrArg TreeSequence.length (H.dividerStage i)
      change (H.stage ⟨i.val + 1, by omega⟩).length = (H.dividerPosition i).val at hl
      have hs := (stageB i.succ).1
      change (H.stage ⟨i.val + 1, by omega⟩).length ≤ B.length at hs
      omega
    have prefixEq (p : ℕ) (hp : 1 ≤ p) (hpB : p ≤ B.length) :
        TreeSequencePrefix U p hp (hpB.trans hBU.1) =
          TreeSequencePrefix T p hp (hpB.trans hBT.1) := by as_aux_lemma =>
      clear * - hBU hBT p hp hpB
      unfold TreeSequencePrefix
      congr
      · funext i
        have hu := hBU.2.1 (Fin.castLE (Nat.succ_le_succ hpB) i)
        have ht := hBT.2.1 (Fin.castLE (Nat.succ_le_succ hpB) i)
        exact hu.trans ht.symm
      · funext i
        have hu := hBU.2.2 (Fin.castLE hpB i)
        have ht := hBT.2.2 (Fin.castLE hpB i)
        exact hu.trans ht.symm
    -- Only the terminal hierarchy stage changes.
    let newStage : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
      fun i => if i.val = H.dividerCount + 1 then U else H.stage i
    have newStageOld (i : Fin (H.dividerCount + 1)) :
        newStage i.castSucc = H.stage i.castSucc := by
      simp only [newStage, Fin.val_castSucc, if_neg (Nat.ne_of_lt i.isLt)]
    have newStageLast : newStage (Fin.last (H.dividerCount + 1)) = U := by
      simp only [newStage, Fin.val_last, ite_true]
    have newStageAt (i : Fin (H.dividerCount + 2)) (hi : i.val ≤ H.dividerCount) :
        newStage i = H.stage i := by
      simp only [newStage, if_neg (by omega : i.val ≠ H.dividerCount + 1)]
    have newNested : ∀ i : Fin (H.dividerCount + 1),
        TreeSequenceInitialSegment (newStage i.castSucc) (newStage i.succ) := by
      intro i
      by_cases hi : i.val = H.dividerCount
      · have he : i = q := Fin.ext hi
        rw [he, newStageOld, show q.succ = Fin.last (H.dividerCount + 1) from rfl,
          newStageLast]
        exact stageU q
      · rw [newStageOld, newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)]
        exact H.nested i
    have newStrict : ∀ i : Fin (H.dividerCount + 1),
        (newStage i.castSucc).length < (newStage i.succ).length := by
      intro i
      by_cases hi : i.val = H.dividerCount
      · have he : i = q := Fin.ext hi
        rw [he, newStageOld, show q.succ = Fin.last (H.dividerCount + 1) from rfl,
          newStageLast]
        exact lt_of_le_of_lt (stageA q).1 hAUstrict
      · rw [newStageOld, newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)]
        exact H.strict i
    let K : TashkinovHierarchy RU baseU :=
      { dividerCount := H.dividerCount
        stage := newStage
        baseStage := by
          rw [show newStage 0 = H.stage 0 by simp [newStage], H.baseStage]
          exact hTnEq.symm
        terminalStage := newStageLast
        nested := newNested
        strict := newStrict
        dividerPosition := fun i => ⟨(H.dividerPosition i).val,
          Nat.lt_succ_of_le ((hdivB i).trans hBU.1)⟩
        dividerPositive := H.dividerPositive
        dividerIncreasing := H.dividerIncreasing
        dividerStage := by
          intro i
          rw [newStageAt ⟨i.val + 1, by omega⟩ (Nat.succ_le_of_lt i.isLt)]
          rw [prefixEq (H.dividerPosition i).val (H.dividerPositive i) (hdivB i)]
          exact H.dividerStage i
        coreInsideFirst := by
          rw [hcore]
          by_cases hz : H.dividerCount = 0
          · rw [show newStage ⟨1, by omega⟩ = U by simp [newStage, hz]]
            exact trans coreA hAU
          · rw [newStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hz)]
            exact H.coreInsideFirst }
    have stageEq (i : Fin (H.dividerCount + 1)) : K.stage i.castSucc = H.stage i.castSucc :=
      newStageOld i
    have starredEq (i : Fin (H.dividerCount + 1)) :
        HierarchyStarredStage K i = HierarchyStarredStage H i := by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hcore
      · exact stageEq i.succ
    have storedEq (i : Fin (H.dividerCount + 1)) :
        HierarchyStoredColorsAt K i = HierarchyStoredColorsAt H i := by
      change TashkinovStoredColors newSeries.data n \
          TreeMissingColors mu (HierarchyStarredStage K i) = _
      rw [hstoredEq, starredEq]
      rfl
    have missingEq (i : Fin (H.dividerCount + 1)) :
        HierarchyStageMissingColors K i = HierarchyStageMissingColors H i := by
      refine Fin.cases ?_ (fun i => ?_) i
      · change TreeMissingColors mu (newSeries.data.tree n.castSucc) = _
        rw [hTnEq]
        rfl
      · change TreeMissingColors mu (K.stage i.succ.castSucc) = _
        rw [stageEq]
        rfl
    have cutoffEq (c : Fin k) (p : ℕ) (hp : p ≤ S.length) :
        min (HierarchyFirstMissingPosition mu U c).val p =
          min (HierarchyFirstMissingPosition mu T c).val p :=
      (HierarchyFirstMissingPositionPrefixCutoff mu S U hSU c p hp).symm.trans
        (HierarchyFirstMissingPositionPrefixCutoff mu S T hST c p hp)
    have ownerBound (eta : Fin k)
        (he : (HierarchyFirstMissingPosition mu T eta).val ≤ B.length) :
        (HierarchyFirstMissingPosition mu U eta).val ≤ B.length := by as_aux_lemma =>
      clear * - he hBT hBU hBXLen hXshort firstMem firstBound
      let i : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition mu T eta).val, Nat.lt_succ_of_le he⟩
      have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i =
          HierarchyFirstMissingPosition mu T eta := Fin.ext rfl
      have hm : eta ∈ MissingColors G mu (B.vertex i) := by
        rw [← hBT.2.1 i, hi]
        apply firstMem T eta
        omega
      apply firstBound hBU eta
      apply Finset.mem_biUnion.mpr
      refine ⟨B.vertex i, ?_, hm⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩
    -- Old edges retain their cutoff; appended colors are excluded from each pair.
    have lastAvoidance (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt H q)
        (c : Fin k) (hc : c ∈ P.counterexample.good.gamma q eta) :
        c ∉ HierarchySegmentColors K q eta := by as_aux_lemma =>
      clear * - heta hc hUcolors hSU hST hBS hBLen hXLen hXshort hBT
        haChoice hbGamma ownerBound cutoffEq starredEq K H q A mu T U S B
      intro hseg
      unfold HierarchySegmentColors at hseg
      dsimp only at hseg
      rw [show K.stage q.succ = U from K.terminalStage] at hseg
      obtain ⟨r, hrA, hrp, hrc⟩ := (Finset.mem_filter.mp hseg).2
      rw [starredEq q] at hrA
      by_cases hrS : r.val < S.length
      · let rs : Fin S.length := ⟨r.val, hrS⟩
        let rt : Fin T.length := Fin.castLE hST.1 rs
        have hrU : Fin.castLE hSU.1 rs = r := Fin.ext rfl
        have hcol : mu (T.edge rt) = some c := by
          rw [hST.2.2 rs, ← hSU.2.2 rs, hrU]
          exact hrc
        have hcut := cutoffEq eta S.length le_rfl
        have hrnew : r.val < min (HierarchyFirstMissingPosition mu U eta).val S.length :=
          lt_min (lt_min_iff.mp hrp).1 hrS
        rw [hcut] at hrnew
        have hold : c ∈ HierarchySegmentColors H q eta := by
          change c ∈ Finset.univ.filter (fun c => ∃ t : Fin (H.stage q.succ).length,
            A.length ≤ t.val ∧
              t.val < min (HierarchyFirstMissingPosition mu T eta).val
                (H.stage q.succ).length ∧ mu ((H.stage q.succ).edge t) = some c)
          rw [show H.stage q.succ = T by exact H.terminalStage]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rt, hrA,
            lt_min (lt_min_iff.mp hrnew).1 rt.isLt, hcol⟩
        exact (Finset.mem_sdiff.mp (P.counterexample.good.avoidance q eta heta hc)).2 hold
      · have hcolors := hUcolors r (by omega)
        have he : c = alpha ∨ c = beta := by
          rcases hcolors with h | h
          · exact Or.inl (Option.some.inj (hrc.symm.trans h))
          · exact Or.inr (Option.some.inj (hrc.symm.trans h))
        rcases he with he | he
        · subst c
          rcases haChoice with hfree | ⟨theta, htheta, hatheta, hpos⟩
          · exact hfree (Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩))
          · by_cases het : eta = theta
            · subst theta
              have hb := ownerBound eta hpos
              have hbs := hBS.1
              have hrbefore := (lt_min_iff.mp hrp).1
              omega
            · exact Finset.disjoint_left.mp
                (P.counterexample.good.disjointPairs q eta theta heta htheta het) hc hatheta
        · subst c
          exact hbGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)
    have earlierSegment (i : Fin (H.dividerCount + 1)) (hi : i.val < H.dividerCount)
        (eta : Fin k) : HierarchySegmentColors K i eta = HierarchySegmentColors H i eta := by
      have hnext : K.stage i.succ = H.stage i.succ :=
        newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)
      have hnextB : (H.stage i.succ).length ≤ B.length := by
        have he : i.succ = (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 1)).castSucc :=
          Fin.ext rfl
        rw [he]
        exact (stageB _).1
      have hcut := cutoffEq eta (H.stage i.succ).length (hnextB.trans hBS.1)
      unfold HierarchySegmentColors
      dsimp only
      rw [starredEq i, hnext, hcut]
    let goodU : GoodHierarchy K :=
      { gamma := P.counterexample.good.gamma
        twoColors := by
          intro i eta heta
          exact P.counterexample.good.twoColors i eta (by rw [← storedEq i]; exact heta)
        avoidance := by
          intro i eta heta c hc
          have hstored := (storedEq i) ▸ heta
          have hold := P.counterexample.good.avoidance i eta hstored hc
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · rw [missingEq]
            exact (Finset.mem_sdiff.mp hold).1
          · by_cases hi : i.val = H.dividerCount
            · have he : i = q := Fin.ext hi
              subst i
              exact lastAvoidance eta hstored c hc
            · rw [earlierSegment i (by omega)]
              exact (Finset.mem_sdiff.mp hold).2
        disjointPairs := by
          intro i eta theta heta htheta hne
          exact P.counterexample.good.disjointPairs i eta theta
            ((storedEq i) ▸ heta) ((storedEq i) ▸ htheta) hne
        uniqueRefresh := by
          intro i
          change ∃! eta : Fin k, eta ∈ HierarchyStoredColorsAt K i.succ ∧
            P.counterexample.good.gamma i.succ eta ⊆
              ((TreeSequenceVertexSet (K.stage i.succ.castSucc) \
                TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
                  fun v => MissingColors G mu v) ∧
            ∀ theta ∈ HierarchyStoredColorsAt K i.succ, theta ≠ eta →
              P.counterexample.good.gamma i.succ theta = P.counterexample.good.gamma i.castSucc theta
          rw [stageEq i.succ, starredEq i.castSucc, storedEq i.succ]
          exact P.counterexample.good.uniqueRefresh i
        parallelBase := by
          change newSeries.data.kind n = some TashkinovExtensionKind.PE → _
          rw [hkinds n]
          intro hpe
          change ¬ TreeColorSetMinusClosed G mu baseU.core
              ((HierarchyStoredColorsAt K 0).biUnion (P.counterexample.good.gamma 0)) ∧ _
          rw [hcore, hclosure, storedEq 0, hTnEq]
          exact P.counterexample.good.parallelBase hpe
        minusClosed := by
          intro i
          change TreeColorSetMinusClosed G mu (K.stage i.succ.castSucc)
            ((HierarchyStoredColorsAt K i.succ).biUnion (P.counterexample.good.gamma i.castSucc))
          rw [stageEq i.succ, storedEq i.succ]
          exact P.counterexample.good.minusClosed i }
    have hnotElementary : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet U) := by
      intro helem
      obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp haB
      have hvU := TreeSequenceInitialSegmentVertexSetSubset hBU hv
      have hyU : y ∈ TreeSequenceVertexSet U := by
        rw [← hUlast]
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨Fin.last U.length, rfl⟩
      have hne : v ≠ y := by
        intro he
        exact hyB (he ▸ hv)
      exact Finset.disjoint_left.mp (helem hvU hyU hne) hmissing hay
    let CU : HierarchyCounterexample baseU :=
      { positive := P.counterexample.positive
        hierarchy := K
        good := goodU
        maximum := hMP
        notElementary := hnotElementary }
    -- The possibly internal first attachment lies before this candidate suffix.
    have hpU : HierarchyPathNumber K ≤ j - 1 := by as_aux_lemma =>
      clear * - K starredEq hUpath hXLen hBLen hSUstrict hBS hjlow
      let candidates := (Finset.Icc 1 (U.length - A.length)).filter fun i =>
        ∀ r : Fin U.length, A.length + i ≤ r.val →
          G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)
      have hm : j - 1 ∈ candidates := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
        · have hbs := hBS.1
          omega
        · intro r hr
          exact hUpath r (by omega)
      have hn : candidates.Nonempty := ⟨j - 1, hm⟩
      unfold HierarchyPathNumber
      dsimp only
      rw [starredEq (Fin.last H.dividerCount)]
      change (if h : candidates.Nonempty then candidates.min' h else U.length - A.length) ≤ j - 1
      rw [dif_pos hn]
      exact Finset.min'_le candidates (j - 1) hm
    have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure CU)
        (HierarchyCounterexampleMeasure P.counterexample) := by
      apply Or.inl
      change HierarchyPathNumber K < HierarchyPathNumber H
      rw [hpOld]
      omega
    exact P.minimumContext.lexicographicMinimality CU rfl rfl hless
