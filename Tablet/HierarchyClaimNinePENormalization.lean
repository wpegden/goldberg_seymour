import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySplitter
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumPropertyTransport
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableChangeCasesOneTwo
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeInterchangeable
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.interchange
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.P2813_T1_BaseControl
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.CorrespondingExtendedTashkinovTreeTrans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: HierarchyClaimNinePENormalization]
theorem HierarchyClaimNinePENormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hzero : P.counterexample.hierarchy.dividerCount = 0)
    (hpe : P.corresponding.replacementETT.series.data.kind
        (Fin.last P.corresponding.replacementETT.rounds) =
          some TashkinovExtensionKind.PE)
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnotTerminalLadder :
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      alpha ∉ TreeMissingColors P.coloring Tn)
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) :
    (HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx).Nonempty ∨
      ∃ P' : HierarchyReplacementPresentation
          G k e0 input T phi ett base C ctx,
        ∃ beta : Fin k,
          let ett' := P'.corresponding.replacementETT
          let n' : Fin (ett'.rounds + 1) := Fin.last ett'.rounds
          let Tn' := ett'.series.data.tree n'.castSucc
          let H' := P'.counterexample.hierarchy
          let A' := HierarchyStarredStage H' (Fin.last H'.dividerCount)
          beta ∈ TreeMissingColors P'.coloring Tn' ∧
            beta ∈ TreeMissingColors P'.coloring A' ∧
            beta ∈ MissingColors G P'.coloring
              (T.vertex (Fin.last T.length)) ∧
            ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
              Disjoint
                (MissingColors G P'.coloring
                  ((HierarchyFullTailPrefix C i).vertex
                    (Fin.last (HierarchyFullTailPrefix C i).length)))
                (MissingColors G P'.coloring
                  (T.vertex (Fin.last T.length))) := by
-- BODY
  classical
  let mu := P.coloring
  let F := P.corresponding.replacementETT
  let b := P.replacementBase
  let X := P.counterexample
  let mctx := P.minimumContext
  let H := X.hierarchy
  let n : Fin (F.rounds + 1) := Fin.last F.rounds
  let Tn := F.series.data.tree n.castSucc
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := T.length - A.length
  let B := TreeSequencePrefix T (min (A.length + (ell - 1)) T.length)
    (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
  let y := T.vertex (Fin.last T.length)
  have hz : H.dividerCount = 0 := hzero
  have hp : F.series.data.kind n = some TashkinovExtensionKind.PE := hpe
  have hA : A = b.core := by
    have hi : Fin.last H.dividerCount = 0 := Fin.ext (by simp [hz])
    dsimp only [A]
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    simpa only [hA, hi, H.terminalStage] using H.coreInsideFirst
  have htwo : 2 ≤ ell :=
    HierarchyCounterexampleTailAtLeastTwo G k e0 P.corresponding.replacementInput
      T mu F b X mctx.proper mctx.oneEdgeUncolored mctx.lowerRung
      mctx.fewerDividers mctx.lexicographicMinimality mctx.largeMissingSet
  have hBlen : B.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    dsimp only [ell] at htwo ⊢
    have := hAT.1
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := by
    have hlen : A.length ≤ B.length := by rw [hBlen]; dsimp [ell] at htwo; omega
    exact ⟨hlen, fun i => hAT.2.1 i, fun i => hAT.2.2 i⟩
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T mu F b X mctx.proper
      mctx.oneEdgeUncolored mctx.lowerRung mctx.fewerDividers
      mctx.lexicographicMinimality mctx.largeMissingSet
  have hyB : y ∉ TreeSequenceVertexSet B := by
    intro hy
    obtain ⟨i, hi⟩ : ∃ i, B.vertex i = y := by
      simpa [TreeSequenceVertexSet] using hy
    have hv := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hval := congrArg Fin.val hv
    have := i.isLt
    simp only [Fin.val_castLE, Fin.val_last] at hval
    omega
  obtain ⟨u⟩ := (b.parallel hp).2.2
  have hTnA : TreeSequenceInitialSegment Tn A := by simpa only [hA] using u.leftSegment
  have hTnT : TreeSequenceInitialSegment Tn T := by
    refine ⟨hTnA.1.trans hAT.1, ?_, ?_⟩
    · intro i
      exact (hAT.2.1 (Fin.castLE (Nat.succ_le_succ hTnA.1) i)).trans (hTnA.2.1 i)
    · intro i
      exact (hAT.2.2 (Fin.castLE hTnA.1 i)).trans (hTnA.2.2 i)
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have hay : alpha ∈ MissingColors G mu y := hstart.2
  have haTn : alpha ∉ TreeMissingColors mu Tn := hnotTerminalLadder
  have haR : alpha ∈ TreeMissingColors mu b.closure := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
    rw [hA, u.vertexSet] at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (haTn (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)).elim
    · exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
  -- The sole Gamma union is smaller than the terminal missing-color set.
  let D := HierarchyStoredColorsAt H 0
  let R := D.biUnion (X.good.gamma 0)
  have hRcard : R.card ≤ 2 * F.rounds := by
    calc
      R.card ≤ ∑ c ∈ D, (X.good.gamma 0 c).card := Finset.card_biUnion_le
      _ = 2 * D.card := by
        rw [Finset.sum_congr rfl (fun c hc => X.good.twoColors 0 c hc)]
        simp [D, H, Nat.mul_comm]
      _ ≤ 2 * F.rounds := Nat.mul_le_mul_left 2 (HierarchyStoredColorsCardinality H 0)
  obtain ⟨beta, hbTn, hbR⟩ : ∃ beta, beta ∈ TreeMissingColors mu Tn ∧ beta ∉ R := by
    by_contra hnone
    have hsub : TreeMissingColors mu Tn ⊆ R := by
      intro c hc
      by_contra hn
      exact hnone ⟨c, hc, hn⟩
    have hc := Finset.card_le_card hsub
    have hl : 2 * F.rounds + 11 ≤ (TreeMissingColors mu Tn).card := mctx.largeMissingSet
    omega
  have hne : beta ≠ alpha := by intro heq; subst beta; exact haTn hbTn
  have haRnot : alpha ∉ R := by
    intro hc
    obtain ⟨eta, heta, hc⟩ := Finset.mem_biUnion.mp hc
    have hm := (Finset.mem_sdiff.mp (X.good.avoidance 0 eta heta hc)).1
    exact haTn hm
  have missingMono {U W : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W) {c : Fin k}
      (hc : c ∈ TreeMissingColors mu U) : c ∈ TreeMissingColors mu W := by
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hUW hv, hvc⟩
  have hbA := missingMono hTnA hbTn
  have firstIn (U : TreeSequence G e0) (hUT : TreeSequenceInitialSegment U T)
      (c : Fin k) (hc : c ∈ TreeMissingColors mu U) :
      T.vertex (HierarchyFirstMissingPosition mu T c) ∈ TreeSequenceVertexSet U ∧
        c ∈ MissingColors G mu (T.vertex (HierarchyFirstMissingPosition mu T c)) := by
    clear * - U hUT c hc
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i, hi⟩ : ∃ i, U.vertex i = v := by
      simpa [TreeSequenceVertexSet] using hv
    let iT := Fin.castLE (Nat.succ_le_succ hUT.1) i
    let S := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G mu (T.vertex j)
    have hiS : iT ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa only [iT, hUT.2.1 i, hi] using hvc⟩
    have hS : S.Nonempty := ⟨iT, hiS⟩
    have hpos : HierarchyFirstMissingPosition mu T c = S.min' hS := by
      simp only [HierarchyFirstMissingPosition, S, dif_pos hS]
    have hbound : (HierarchyFirstMissingPosition mu T c).val ≤ U.length := by
      have hh := Finset.min'_le S iT hiS
      rw [← hpos] at hh
      have := i.isLt
      change (HierarchyFirstMissingPosition mu T c).val ≤ i.val at hh
      omega
    let j : Fin (U.length + 1) := ⟨(HierarchyFirstMissingPosition mu T c).val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hUT.1) j =
        HierarchyFirstMissingPosition mu T c := Fin.ext rfl
    refine ⟨?_, ?_⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, (hUT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
    rw [hpos]
    exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  let va := T.vertex (HierarchyFirstMissingPosition mu T alpha)
  let vb := T.vertex (HierarchyFirstMissingPosition mu T beta)
  have hva := firstIn A hAT alpha haA
  have hvb := firstIn Tn hTnT beta hbTn
  have hvaB : va ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hAB hva.1
  have hvbA : vb ∈ TreeSequenceVertexSet A := TreeSequenceInitialSegmentVertexSetSubset hTnA hvb.1
  have hvbB : vb ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hAB hvbA
  -- Coincident witnesses would make alpha missing on Tn, contrary to the hypothesis.
  have hvab : va ≠ vb := by
    intro h
    exact haTn (Finset.mem_biUnion.mpr ⟨vb, hvb.1, h ▸ hva.2⟩)
  have stableRefl (U : TreeSequence G e0) (D : Finset (Fin k)) :
      StableColoring U D mu mu := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hi : TreeInterchangeable G A mu beta alpha := by
    rw [hA]
    exact (interchange G k e0 P.corresponding.replacementInput T mu mu F
      X.maximum X.positive mctx.lowerRung hp b mctx.proper mctx.oneEdgeUncolored
      ⟨stableRefl _ _, stableRefl _ _⟩ beta alpha).2.2.2 hbTn haR
  let J := TwoColorIncidenceGraph G mu beta alpha
  have selfMem (z : Sum V E) : z ∈ TwoColorComponent G mu beta alpha z := by
    change J.connectedComponentMk z = J.connectedComponentMk z
    rfl
  have endpoint (v : V) (hm : beta ∈ MissingColors G mu v ∨ alpha ∈ MissingColors G mu v) :
      Set.Subsingleton (J.neighborSet (Sum.inl v)) := by
    have hdeg : @SimpleGraph.degree _ J (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hm with hm | hm
      · exact MissingColorIncidenceEndpoint G mu beta alpha hne mctx.proper v hm
      · have hg : TwoColorIncidenceGraph G mu alpha beta = J := by
          ext x y
          cases x <;> cases y <;> simp [J, TwoColorIncidenceGraph, or_comm]
        rw [← hg]
        exact MissingColorIncidenceEndpoint G mu alpha beta hne.symm mctx.proper v hm
    letI : Fintype (J.neighborSet (Sum.inl v)) := Fintype.ofFinite _
    have hc : Fintype.card (J.neighborSet (Sum.inl v)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hdeg
    intro x hx w hw
    exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨x, hx⟩ ⟨w, hw⟩)
  have pathMissing (v : V) (hm : beta ∈ MissingColors G mu v ∨ alpha ∈ MissingColors G mu v) :
      TwoColorPathComponent G mu beta alpha (Sum.inl v) :=
    ⟨hne, Sum.inl v, selfMem _, endpoint v hm⟩
  have habComp : TwoColorComponent G mu beta alpha (Sum.inl va) =
      TwoColorComponent G mu beta alpha (Sum.inl vb) :=
    hi _ _ (pathMissing va (Or.inr hva.2)) (pathMissing vb (Or.inl hvb.2))
      ⟨va, hva.1, selfMem _⟩ ⟨vb, hvbA, selfMem _⟩
  let Q := TwoColorComponent G mu beta alpha (Sum.inl y)
  have hpath : TwoColorPathComponent G mu beta alpha (Sum.inl y) :=
    pathMissing y (Or.inr hay)
  have hend {s t : Sum V E} (p : J.Walk s t) (hpp : p.IsPath)
      (v : Sum V E) (hv : v ∈ p.support) (hvdeg : Set.Subsingleton (J.neighborSet v)) :
      v = s ∨ v = t := by
    obtain ⟨i, hvi, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    by_cases h0 : i = 0
    · left
      simpa only [h0, p.getVert_zero] using hvi.symm
    by_cases hl : i = p.length
    · right
      simpa only [hl, p.getVert_length] using hvi.symm
    have hlft : J.Adj v (p.getVert (i - 1)) := by
      rw [← hvi, ← show i - 1 + 1 = i by omega]
      exact (p.adj_getVert_succ (by omega : i - 1 < p.length)).symm
    have hrgt : J.Adj v (p.getVert (i + 1)) := by
      rw [← hvi]
      exact p.adj_getVert_succ (by omega : i < p.length)
    have heq := hvdeg hlft hrgt
    have heqi := hpp.getVert_injOn (by omega : i - 1 ≤ p.length)
      (by omega : i + 1 ≤ p.length) heq
    omega
  have hdisjoint : Disjoint Q (TwoColorComponent G mu beta alpha (Sum.inl vb)) := by
    rcases TwoColorComponentsDisjoint G mu beta alpha (Sum.inl y) (Sum.inl vb) with heq | hd
    · obtain ⟨s, t, p, hpp, hsupp⟩ := TwoColorComponentSpanningPath G mu beta alpha mctx.proper (Sum.inl y)
      have hayQ : Sum.inl va ∈ Q := by dsimp only [Q]; rw [heq, ← habComp]; exact selfMem _
      have hbyQ : Sum.inl vb ∈ Q := by dsimp only [Q]; rw [heq]; exact selfMem _
      have hs : ∀ x, x ∈ p.support ↔ x ∈ Q := fun x => Set.ext_iff.mp hsupp x
      have haend := hend p hpp (Sum.inl va) ((hs _).2 hayQ) (endpoint va (Or.inr hva.2))
      have hbend := hend p hpp (Sum.inl vb) ((hs _).2 hbyQ) (endpoint vb (Or.inl hvb.2))
      have hyend := hend p hpp (Sum.inl y) ((hs _).2 (selfMem _)) (endpoint y (Or.inr hay))
      have hya : y ≠ va := by intro hh; exact hyB (hh ▸ hvaB)
      have hyb : y ≠ vb := by intro hh; exact hyB (hh ▸ hvbB)
      rcases haend with ha | ha <;> rcases hbend with hb | hb <;> rcases hyend with hy | hy
      all_goals first
        | exact (hvab (Sum.inl.inj (ha.trans hb.symm))).elim
        | exact (hya (Sum.inl.inj (hy.trans ha.symm))).elim
        | exact (hyb (Sum.inl.inj (hy.trans hb.symm))).elim
    · exact hd
  let sigma := TwoColorComponentSwap G mu beta alpha (Sum.inl y)
  have control := P2813_T1_BaseControl G k e0 P.corresponding.replacementInput
    T mu F b X mctx helem beta alpha hne
    ⟨missingMono hAB hbA, missingMono hAB haA⟩ (Sum.inl y) hpath sigma rfl
    (Or.inr ⟨hz, Or.inl hbTn⟩) hdisjoint
  have hcombined : CombinedStableColoring Tn b.closure
      (TashkinovStoredColors F.series.data n) mu sigma := by
    have hp' : F.series.data.kind (Fin.last F.rounds) = some TashkinovExtensionKind.PE := hp
    simpa only [hp', if_pos, n, Tn] using control.1
  have hsproper : IsProperEdgeColoring G sigma := control.2.2.1
  have hsone : IsOneEdgeUncolored sigma e0 := control.2.2.2.1
  have behavior := TwoColorComponentSwapMissingBehavior G mu beta alpha hne mctx.proper (Sum.inl y)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ Q)
      (hinc : Incident G v f) (hc : mu f = some beta ∨ mu f = some alpha) :
      Sum.inr f ∈ Q := by
    have hadj : J.Adj (Sum.inr f) (Sum.inl v) := ⟨hinc, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have missingB (v : V) (hv : v ∈ TreeSequenceVertexSet B) :
      MissingColors G sigma v = MissingColors G mu v := by
    by_cases hout : Sum.inl v ∉ Q
    · exact behavior.1 v hout
    · have hin : Sum.inl v ∈ Q := not_not.mp hout
      have hna : alpha ∉ MissingColors G mu v := by
        intro hm
        have heq : v = va := by
          by_contra hn
          exact Finset.disjoint_left.mp (helem hv hvaB hn) hm hva.2
        apply Set.disjoint_left.mp hdisjoint hin
        rw [heq, ← habComp]
        exact selfMem _
      have hnb : beta ∉ MissingColors G mu v := by
        intro hm
        have heq : v = vb := by
          by_contra hn
          exact Finset.disjoint_left.mp (helem hv hvbB hn) hm hvb.2
        exact Set.disjoint_left.mp hdisjoint hin (heq ▸ selfMem (Sum.inl v))
      have newPresent (c d : Fin k) (hcd : c = beta ∧ d = alpha ∨ c = alpha ∧ d = beta)
          (hd : d ∉ MissingColors G mu v) : c ∉ MissingColors G sigma v := by
        have hpresent : d ∈ PresentColors G mu v := by simpa [MissingColors] using hd
        obtain ⟨f, hf, hcol⟩ : ∃ f, Incident G v f ∧ mu f = some d := by
          simpa [PresentColors] using hpresent
        have hfe : Sum.inr f ∈ Q := by
          apply edgeOfVertex hin hf
          rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr hcol
          · exact Or.inl hcol
        have hnew : sigma f = some c := by
          rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [sigma, TwoColorComponentSwap, hfe, hcol, hne.symm, Q]
          · simp [sigma, TwoColorComponentSwap, hfe, hcol, Q]
        have hpnew : c ∈ PresentColors G sigma v := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨f, hf, hnew⟩
        simpa [MissingColors] using hpnew
      ext c
      by_cases hcb : c = beta
      · subst c
        simp only [hnb, newPresent beta alpha (Or.inl ⟨rfl, rfl⟩) hna]
      · by_cases hca : c = alpha
        · subst c
          simp only [hna, newPresent alpha beta (Or.inr ⟨rfl, rfl⟩) hnb]
        · exact behavior.2.2.2 v c hcb hca
  have treeMissingEq (U : TreeSequence G e0) (hm : ∀ v ∈ TreeSequenceVertexSet U,
      MissingColors G sigma v = MissingColors G mu v) :
      TreeMissingColors sigma U = TreeMissingColors mu U :=
    Finset.biUnion_congr rfl hm
  have hmA : TreeMissingColors sigma A = TreeMissingColors mu A :=
    treeMissingEq A (fun v hv => missingB v (TreeSequenceInitialSegmentVertexSetSubset hAB hv))
  have hmTn : TreeMissingColors sigma Tn = TreeMissingColors mu Tn := treeMissingEq Tn hcombined.1.2
  have hmR : TreeMissingColors sigma b.closure = TreeMissingColors mu b.closure := treeMissingEq _ hcombined.2.2
  have hbetaA : beta ∈ TreeMissingColors sigma A := hmA ▸ hbA
  have halphaA : alpha ∈ TreeMissingColors sigma A := hmA ▸ haA
  have hbetaTn : beta ∈ TreeMissingColors sigma Tn := hmTn ▸ hbTn
  have hbetay : beta ∈ MissingColors G sigma y := behavior.2.2.1 y (selfMem _) hay
  -- Extract the actual PE route; only its core part needs fixed displayed values.
  have oldRoute : TashkinovAugmentationSequence mu Tn T := by
    have step := F.series.certified n
    generalize hi : n = i at step
    cases step with
    | initial =>
      have hv := congrArg Fin.val hi
      simp [n] at hv
      have := F.roundsPositive
      omega
    | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
        seed adjoin closure ordered strict =>
      have hk : F.series.data.kind n = some TashkinovExtensionKind.SE := by simpa [hi] using kind
      rw [hp] at hk
      cases hk
    | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
        seed adjoin closure ordered strict =>
      have hk : F.series.data.kind n = some TashkinovExtensionKind.RE := by simpa [hi] using kind
      rw [hp] at hk
      cases hk
    | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
        edges kind vertex outside delta gammaEq closure ordered strict =>
      have hj : j.succ = n := hi.symm
      have hlast : j.succ.succ = Fin.last (F.rounds + 1) :=
        Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
      apply TashkinovAugmentationSequenceRestrict mu Tn T _ _ hTnT F.belowFinal
      simpa [Tn, hj, hlast, ← F.generatingColoring, n] using closure.1
  have oldCore := TashkinovAugmentationSequenceRestrict mu Tn A T oldRoute hTnA hAT
  have oldSuffix := TashkinovAugmentationSequenceSuffix mu Tn A T oldRoute hTnA hAT
  have displayed := CombinedStableClosurePreserved G k e0 P.corresponding.replacementInput
    T mu mu sigma F X.positive b F.generatingColoring hp mctx.proper mctx.oneEdgeUncolored
    hsproper hsone hcombined
  have fixedA (j : Fin A.length) : sigma (A.edge j) = mu (A.edge j) := by
    by_cases hj : j.val < Tn.length
    · let i : Fin Tn.length := ⟨j.val, hj⟩
      have he : A.edge j = Tn.edge i := by
        have he := hTnA.2.2 i
        simpa [i] using he
      rw [he]
      exact displayed.1 i
    · obtain ⟨i, he, hv⟩ := u.newEntryFromRight (Fin.cast (congrArg TreeSequence.length hA) j) (by simpa using Nat.le_of_not_gt hj)
      have edgeTransport (U W : TreeSequence G e0) (h : U = W) (j : Fin U.length) :
          W.edge (Fin.cast (congrArg TreeSequence.length h) j) = U.edge j := by
        cases h
        rfl
      have he' : A.edge j = b.closure.edge i := (edgeTransport A b.core hA j).symm.trans he
      rw [he']
      exact displayed.2.1 i
  have newCore : TashkinovAugmentationSequence sigma Tn A := by
    have transport : ∀ (U W : TreeSequence G e0), TashkinovAugmentationSequence mu U W →
        TreeSequenceInitialSegment W A → TashkinovAugmentationSequence sigma U W := by
      intro U W hseq
      unfold TashkinovAugmentationSequence at hseq ⊢
      induction hseq with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | @tail Z W hUZ hZW ih =>
        intro hWA
        rcases hZW with ⟨hlen, hZW, c, hedge, hc⟩
        have hZA : TreeSequenceInitialSegment Z A :=
          ⟨hZW.1.trans hWA.1,
            fun i => (hWA.2.1 (Fin.castLE (Nat.succ_le_succ hZW.1) i)).trans (hZW.2.1 i),
            fun i => (hWA.2.2 (Fin.castLE hZW.1 i)).trans (hZW.2.2 i)⟩
        refine Relation.ReflTransGen.tail (ih hZA) ⟨hlen, hZW, c, ?_, ?_⟩
        · let i := Fin.cast hlen.symm (Fin.last Z.length)
          have he := hWA.2.2 i
          have hf := fixedA (Fin.castLE hWA.1 i)
          rw [he] at hf
          exact hf.trans hedge
        · obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
          exact Finset.mem_biUnion.mpr ⟨v, hv, by
            rw [missingB v (TreeSequenceInitialSegmentVertexSetSubset hAB
              (TreeSequenceInitialSegmentVertexSetSubset hZA hv))]
            exact hvc⟩
    exact transport Tn A oldCore ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have newSuffix : TashkinovAugmentationSequence sigma A T :=
    TashkinovAugmentationSequenceComponentSwap G k e0 mu beta alpha hne (Sum.inl y)
      A T oldSuffix hbetaA halphaA
  have newRoute : TashkinovAugmentationSequence sigma Tn T := newCore.trans newSuffix
  obtain ⟨corr, hmaximum, bs, K, hsame⟩ := HierarchySplitter G k e0
    P.corresponding.replacementInput T mu sigma F X.maximum X.positive mctx.lowerRung
    b H hp mctx.proper mctx.oneEdgeUncolored hsproper hsone hcombined newRoute
  have corrData : corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        F.series.data.kind n ∧
      TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) = TashkinovStoredColors F.series.data n := by
    rcases corr with ⟨ri, rs, re, hr, hs, hgen, ht, hd, he, hk, hproper, hone, hstable⟩
    cases re with
    | mk rounds positive data above strict below generating =>
      cases hr
      have hs' : data = rs := eq_of_heq hs
      cases hs'
      let a : Fin F.rounds := ⟨F.rounds - 1, by have := F.roundsPositive; omega⟩
      have ha : a.succ = Fin.last F.rounds := Fin.ext (by have := F.roundsPositive; simp [a]; omega)
      have htree : rs.data.tree (Fin.last F.rounds).castSucc = Tn := by
        change rs.data.tree (Fin.last F.rounds).castSucc = F.series.data.tree (Fin.last F.rounds).castSucc
        rw [← ha]
        exact ht a
      have hmnew : TreeMissingColors (rs.data.coloring (Fin.last F.rounds))
          (rs.data.tree (Fin.last F.rounds).castSucc) = TreeMissingColors mu Tn := by
        rw [← hgen, htree, hmTn]
      have hmold : TreeMissingColors (F.series.data.coloring (Fin.last F.rounds))
          (F.series.data.tree (Fin.last F.rounds).castSucc) = TreeMissingColors mu Tn := by
        rw [← F.generatingColoring]
      refine ⟨htree, hk _, ?_⟩
      change TashkinovStoredColors rs.data (Fin.last F.rounds) = TashkinovStoredColors F.series.data (Fin.last F.rounds)
      simp only [TashkinovStoredColors, hd, hmnew, hmold]
  have hkzero : K.dividerCount = 0 := hsame.2.1.symm.trans hz
  have coreEq : bs.core = A := hsame.1.symm.trans hA.symm
  have closureEq : bs.closure = b.closure := (hsame.2.2.2.2.2 hp).symm
  have starK (j : Fin (K.dividerCount + 1)) : HierarchyStarredStage K j = bs.core := by
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    rw [hj]
    rfl
  have termK (j : Fin (K.dividerCount + 1)) : K.stage j.succ = T := by
    have hj : j.succ = Fin.last (K.dividerCount + 1) := Fin.ext (by have := j.isLt; simp; omega)
    rw [hj, K.terminalStage]
  have termH : H.stage (0 : Fin (H.dividerCount + 1)).succ = T := by
    have hj : (0 : Fin (H.dividerCount + 1)).succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    rw [hj, H.terminalStage]
  have storedEq (j : Fin (K.dividerCount + 1)) : HierarchyStoredColorsAt K j = D := by
    change TashkinovStoredColors corr.replacementETT.series.data (Fin.last corr.replacementETT.rounds) \
        TreeMissingColors sigma (HierarchyStarredStage K j) = D
    rw [corrData.2.2, starK j, coreEq, hmA]
    change _ = TashkinovStoredColors F.series.data n \ TreeMissingColors mu b.core
    rw [hA]
  have stageMissingEq (j : Fin (K.dividerCount + 1)) :
      HierarchyStageMissingColors K j = TreeMissingColors mu Tn := by
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    rw [hj]
    change TreeMissingColors sigma (corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc) = _
    rw [corrData.1, hmTn]
  have unaffectedValue (f : E) (c : Fin k) (hcb : c ≠ beta) (hca : c ≠ alpha) :
      sigma f = some c ↔ mu f = some c := by
    by_cases hcomp : Sum.inr f ∈ Q
    · by_cases hb : mu f = some beta
      · simp [sigma, TwoColorComponentSwap, Q, hcomp, hb, hcb.symm, hca.symm]
      · by_cases ha : mu f = some alpha
        · simp [sigma, TwoColorComponentSwap, Q, hcomp, hb, ha, hne.symm, hcb.symm, hca.symm]
        · simp [sigma, TwoColorComponentSwap, Q, hcomp, hb, ha]
    · simp [sigma, TwoColorComponentSwap, Q, hcomp]
  have firstEq (eta : Fin k) (heb : eta ≠ beta) (hea : eta ≠ alpha) :
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition mu T eta := by
    have hcandidates : (Finset.univ.filter fun j : Fin (T.length + 1) =>
        eta ∈ MissingColors G sigma (T.vertex j)) =
        (Finset.univ.filter fun j : Fin (T.length + 1) => eta ∈ MissingColors G mu (T.vertex j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact behavior.2.2.2 _ eta heb hea
    simp only [HierarchyFirstMissingPosition, hcandidates]
  -- A boundary witness survives even when its value is one of the swapped colors.
  have notClosed : ¬ TreeColorSetMinusClosed G sigma A R := by
    have hnot := (X.good.parallelBase hp).1
    change ¬ TreeColorSetClosed G mu b.core (TreeMissingColors mu b.core \ R) at hnot
    rw [← hA] at hnot
    unfold TreeColorSetClosed at hnot
    push_neg at hnot
    obtain ⟨c, hc, hn⟩ := hnot
    obtain ⟨f, hf⟩ := hn
    have hfdata : f ∈ BoundaryEdges G (TreeSequenceVertexSet A) ∧ mu f = some c := by
      simpa [BoundaryColorEdges] using hf
    obtain ⟨d, hd, hfd⟩ : ∃ d, d ∈ TreeMissingColors sigma A \ R ∧ sigma f = some d := by
      by_cases hcb : c = beta
      · subst c
        by_cases hcomp : Sum.inr f ∈ Q
        · exact ⟨alpha, Finset.mem_sdiff.mpr ⟨halphaA, haRnot⟩, by
            simp [sigma, TwoColorComponentSwap, Q, hcomp, hfdata.2]⟩
        · exact ⟨beta, Finset.mem_sdiff.mpr ⟨hbetaA, hbR⟩, by
            simp [sigma, TwoColorComponentSwap, Q, hcomp, hfdata.2]⟩
      · by_cases hca : c = alpha
        · subst c
          by_cases hcomp : Sum.inr f ∈ Q
          · exact ⟨beta, Finset.mem_sdiff.mpr ⟨hbetaA, hbR⟩, by
              simp [sigma, TwoColorComponentSwap, Q, hcomp, hfdata.2, hne]⟩
          · exact ⟨alpha, Finset.mem_sdiff.mpr ⟨halphaA, haRnot⟩, by
              simp [sigma, TwoColorComponentSwap, Q, hcomp, hfdata.2]⟩
        · exact ⟨c, by rwa [hmA], (unaffectedValue f c hcb hca).2 hfdata.2⟩
    intro hclosed
    have hfnew : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet A) d := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨hfdata.1, hfd⟩
    rw [hclosed d hd] at hfnew
    exact Finset.notMem_empty f hfnew
  let gs : GoodHierarchy K := {
    gamma := fun _ eta => X.good.gamma 0 eta
    twoColors := by
      intro j eta heta
      exact X.good.twoColors 0 eta (by rwa [storedEq] at heta)
    avoidance := by
      intro j eta heta c hcg
      have hetaD : eta ∈ D := by rwa [storedEq] at heta
      have hold := X.good.avoidance 0 eta hetaD hcg
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [stageMissingEq]
        exact (Finset.mem_sdiff.mp hold).1
      · intro hseg
        have hn : eta ∉ TreeMissingColors mu A := by
          have hn := (Finset.mem_sdiff.mp hetaD).2
          change eta ∉ TreeMissingColors mu b.core at hn
          rwa [← hA] at hn
        have heb : eta ≠ beta := by intro h; subst eta; exact hn hbA
        have hea : eta ≠ alpha := by intro h; subst eta; exact hn haA
        have hcR : c ∈ R := Finset.mem_biUnion.mpr ⟨eta, hetaD, hcg⟩
        have hcb : c ≠ beta := by intro h; subst c; exact hbR hcR
        have hca : c ≠ alpha := by intro h; subst c; exact haRnot hcR
        have hfirst := firstEq eta heb hea
        change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (K.stage j.succ).length,
          (HierarchyStarredStage K j).length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition sigma T eta).val (K.stage j.succ).length ∧
            sigma ((K.stage j.succ).edge r) = some c) at hseg
        rw [starK j, coreEq, termK j, hfirst] at hseg
        obtain ⟨r, hr, hp, hcol⟩ := (Finset.mem_filter.mp hseg).2
        apply (Finset.mem_sdiff.mp hold).2
        change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (H.stage (0 : Fin (H.dividerCount + 1)).succ).length,
          b.core.length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition mu T eta).val (H.stage (0 : Fin (H.dividerCount + 1)).succ).length ∧
            mu ((H.stage (0 : Fin (H.dividerCount + 1)).succ).edge r) = some c)
        rw [termH, ← hA]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hp, (unaffectedValue _ c hcb hca).1 hcol⟩
    disjointPairs := by
      intro j eta theta heta htheta hne'
      exact X.good.disjointPairs 0 eta theta (by rwa [storedEq] at heta)
        (by rwa [storedEq] at htheta) hne'
    uniqueRefresh := by
      intro i
      have := i.isLt
      omega
    parallelBase := by
      dsimp only
      intro hpe'
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma bs.core
          ((HierarchyStoredColorsAt K 0).biUnion (X.good.gamma 0))
        rw [coreEq, storedEq]
        exact notClosed
      · change 4 ≤ ((TreeMissingColors sigma (corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc) ∩ TreeMissingColors sigma bs.closure) \
          (HierarchyStoredColorsAt K 0).biUnion (X.good.gamma 0)).card
        rw [corrData.1, closureEq, storedEq, hmTn, hmR]
        exact (X.good.parallelBase hp).2
    minusClosed := by
      intro i
      have := i.isLt
      omega }
  have sameHX : SameGoodHierarchy X.good gs := by
    refine ⟨hsame, hsame.2.1, ?_⟩
    intro j
    have hj : j = 0 := Fin.ext (by
      simp only [Fin.val_zero]
      have hlt : j.val < H.dividerCount + 1 := j.isLt
      simp only [hz] at hlt
      omega)
    subst j
    exact ⟨(storedEq _).symm, fun _ _ => rfl⟩
  have sameC : SameGoodHierarchy C.good gs := by
    have hs0 := P.sameGood.1
    have hs1 := sameHX.1
    refine ⟨?_, ?_⟩
    · refine ⟨hs0.1.trans hs1.1, hs0.2.1.trans hs1.2.1,
        hs0.2.2.1.trans hs1.2.2.1, hs0.2.2.2.1.trans hs1.2.2.2.1,
        hs0.2.2.2.2.1.trans hs1.2.2.2.2.1, ?_⟩
      intro hpeC
      exact (hs0.2.2.2.2.2 hpeC).trans (hs1.2.2.2.2.2 (hs0.2.2.2.2.1.mp hpeC))
    · obtain ⟨hcount, hg⟩ := P.sameGood.2
      refine ⟨hcount.trans hsame.2.1, ?_⟩
      intro j
      have hj : Fin.cast (congrArg (fun q => q + 1) hcount) j = 0 :=
        Fin.ext (by have := (Fin.cast (congrArg (fun q => q + 1) hcount) j).isLt; omega)
      have ho := hg j
      dsimp only at ho ⊢
      rw [hj] at ho
      refine ⟨ho.1.trans (storedEq _).symm, ?_⟩
      intro eta heta
      exact ho.2 eta heta
  have hvbT : vb ∈ TreeSequenceVertexSet T := TreeSequenceInitialSegmentVertexSetSubset hBT hvbB
  have hyT : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  have hvby : vb ≠ y := by intro h; exact hyB (h ▸ hvbB)
  have hbetavb : beta ∈ MissingColors G sigma vb := by rw [missingB vb hvbB]; exact hvb.2
  let Y : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact X.positive
    hierarchy := K
    good := gs
    maximum := hmaximum
    notElementary := by
      intro hel
      exact Finset.disjoint_left.mp (hel hvbT hyT hvby) hbetavb hbetay }
  have evalHEq {r s : ℕ} (h : r = s)
      (f : Fin r → TreeSequence G e0) (g : Fin s → TreeSequence G e0)
      (hh : HEq f g) (i : Fin r) : g (Fin.cast h i) = f i := by
    cases h
    cases hh
    rfl
  have measureEq : HierarchyCounterexampleMeasure Y = HierarchyCounterexampleMeasure X := by
    have hstage : K.stage ⟨K.dividerCount, by omega⟩ = H.stage ⟨H.dividerCount, by omega⟩ := by
      have he := evalHEq (congrArg (fun q => q + 2) hsame.2.1) H.stage K.stage hsame.2.2.1
        ⟨H.dividerCount, by omega⟩
      convert he using 1
      apply congrArg K.stage
      apply Fin.ext
      simp only [Fin.val_cast]
      exact hsame.2.1.symm
    change (HierarchyPathNumber K, T.length - (K.stage ⟨K.dividerCount, by omega⟩).length) =
      (HierarchyPathNumber H, T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
    rw [hstage]
    congr 1
    unfold HierarchyPathNumber
    rw [starK, coreEq]
  let ctxY : HierarchyMinimumCounterexampleContext G k e0 corr.replacementInput
      T sigma corr.replacementETT bs Y := {
    proper := hsproper
    oneEdgeUncolored := hsone
    lowerRung := by
      intro inp W gen lower hpos hlt hmp
      rw [corr.rungAgreement] at hlt
      exact mctx.lowerRung lower hpos hlt hmp
    fewerDividers := by
      intro inp W gen other hround hmp bs' K' good' hdiv
      apply mctx.fewerDividers other (hround.trans corr.rungAgreement) hmp bs' K' good'
      exact hdiv.trans_eq hsame.2.1.symm
    lexicographicMinimality := by
      intro inp W gen other bs' Y' hround hcount
      change ¬ HierarchyCounterexampleLess (HierarchyCounterexampleMeasure Y') (HierarchyCounterexampleMeasure Y)
      rw [measureEq]
      exact mctx.lexicographicMinimality Y' (hround.trans corr.rungAgreement)
        (hcount.trans hsame.2.1.symm)
    largeMissingSet := by
      dsimp only
      rw [corrData.1, hmTn, corr.rungAgreement]
      exact mctx.largeMissingSet }
  have hCzero : C.hierarchy.dividerCount = 0 := P.sameGood.1.2.1.trans hz
  have hCstar : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A := by
    have hi : Fin.last C.hierarchy.dividerCount = 0 := Fin.ext (by simp [hCzero])
    rw [hi]
    change base.core = A
    exact P.sameGood.1.1.trans hA.symm
  have htailC : HierarchyFullTailLength C = ell := by
    change T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length = ell
    rw [hCstar]
  have noCommonSigma : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint (MissingColors G sigma ((HierarchyFullTailPrefix C i).vertex
        (Fin.last (HierarchyFullTailPrefix C i).length))) (MissingColors G sigma y) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    rw [htailC] at hi'
    let U := HierarchyFullTailPrefix C i
    let v := U.vertex (Fin.last U.length)
    have hUlen : U.length = A.length + i := by
      change min ((HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i) T.length = _
      rw [hCstar]
      dsimp [ell] at hi'
      omega
    have hUT : TreeSequenceInitialSegment U T := ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have hvB : v ∈ TreeSequenceVertexSet B := by
      let j : Fin (B.length + 1) := ⟨U.length, by rw [hBlen, hUlen]; dsimp [ell] at hi'; omega⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨j, ?_⟩
      change T.vertex _ = T.vertex _
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hvne : v ≠ vb := by
      intro hv
      obtain ⟨j, hj⟩ : ∃ j, A.vertex j = vb := by simpa [TreeSequenceVertexSet] using hvbA
      have heq : T.vertex (Fin.castLE (Nat.succ_le_succ hUT.1) (Fin.last U.length)) =
          T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j) :=
        (hUT.2.1 _).trans (hv.trans ((hAT.2.1 j).trans hj).symm)
      have hval := congrArg Fin.val (T.vertex_injective heq)
      simp only [Fin.val_castLE, Fin.val_last] at hval
      have := j.isLt
      omega
    apply Finset.disjoint_left.mpr
    intro c hcv hcy
    have holdv : c ∈ MissingColors G mu v := by rw [← missingB v hvB]; exact hcv
    by_cases hcb : c = beta
    · subst c
      exact Finset.disjoint_left.mp (helem hvB hvbB hvne) holdv hvb.2
    · by_cases hca : c = alpha
      · subst c
        exact Finset.disjoint_left.mp (hnoCommon i hi) holdv hay
      · exact Finset.disjoint_left.mp (hnoCommon i hi) holdv
          ((behavior.2.2.2 y c hcb hca).1 hcy)
  let Package (inp : PartialEdgeColoring E k)
      (L : ExtendedTashkinovTree G k e0 inp T sigma) : Prop :=
    MaximumProperty L ∧ ∃ bb : HierarchyBase L sigma,
      ∃ Z : HierarchyCounterexample bb,
        SameGoodHierarchy C.good Z.good ∧
          Nonempty (HierarchyMinimumCounterexampleContext G k e0 inp T sigma L bb Z) ∧
          beta ∈ TreeMissingColors sigma (L.series.data.tree (Fin.last L.rounds).castSucc) ∧
          beta ∈ TreeMissingColors sigma (HierarchyStarredStage Z.hierarchy (Fin.last Z.hierarchy.dividerCount))
  have package : Package corr.replacementInput corr.replacementETT := by
    refine ⟨hmaximum, bs, Y, sameC, ⟨ctxY⟩, ?_, ?_⟩
    · rw [corrData.1]
      exact hbetaTn
    · change beta ∈ TreeMissingColors sigma (HierarchyStarredStage K (Fin.last K.dividerCount))
      rw [starK, coreEq]
      exact hbetaA
  -- Compose provenance before presenting the new counterexample relative to the original ETT.
  obtain ⟨composite, hi, hs, he⟩ := CorrespondingExtendedTashkinovTreeTrans G k e0 input
    T phi mu sigma ett P.corresponding corr
  have package' : Package composite.replacementInput composite.replacementETT := by
    have transport {i j : PartialEdgeColoring E k}
        (L : ExtendedTashkinovTree G k e0 i T sigma)
        (M : ExtendedTashkinovTree G k e0 j T sigma)
        (h : i = j) (hh : HEq L M) : Package i L = Package j M := by
      cases h
      have hLM : L = M := eq_of_heq hh
      cases hLM
      rfl
    rw [transport _ _ hi he]
    exact package
  obtain ⟨mp', b', Z, same', ⟨ctx'⟩, hb', hbcore'⟩ := package'
  let P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := sigma
    corresponding := composite
    maximum := mp'
    replacementBase := b'
    counterexample := Z
    sameGood := same'
    minimumContext := ctx' }
  exact Or.inr ⟨P', beta, hb', hbcore', hbetay, noCommonSigma⟩
