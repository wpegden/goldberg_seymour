import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyEligibleCommonMissingIndices
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
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TashkinovHierarchy
import Tablet.Td
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.P2813_T1_TerminalRoute
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.HierarchySplitter

-- [TABLET NODE: HierarchySituationOneShorteningContradiction]
theorem HierarchySituationOneShorteningContradiction {V E : Type*}
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
    (hlast : HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx) : False := by
-- BODY
  classical
  open scoped Sym2 in
    obtain ⟨P, alpha, haB, haT⟩ := (Finset.mem_filter.mp hlast).2
    let old := P.counterexample
    let H := old.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let n := Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let mu := P.coloring
    have sameLast : ∀ {a b : ℕ}
        (s : Fin (a + 2) → TreeSequence G e0)
        (t : Fin (b + 2) → TreeSequence G e0)
        (u v : TreeSequence G e0),
        a = b → HEq s t → u = v →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      intro a b s t u v hab hst huv
      cases hab
      have he : s = t := eq_of_heq hst
      cases he
      cases huv
      rfl
    have hAold : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A :=
      sameLast _ _ _ _ P.sameGood.1.2.1 P.sameGood.1.2.2.1 P.sameGood.1.1
    have hp : HierarchyPathNumber H = 1 := by
      unfold HierarchyPathNumber at hsituation ⊢
      dsimp only at hsituation ⊢
      rw [hAold] at hsituation
      exact hsituation
    have htail : 2 ≤ T.length - A.length :=
      HierarchyCounterexampleTailAtLeastTwo G k e0 P.corresponding.replacementInput
        T mu P.corresponding.replacementETT P.replacementBase old
        P.minimumContext.proper P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
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
    have starNext (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H j) (H.stage j.succ) := by
      refine Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) j
    have hAT : TreeSequenceInitialSegment A T := by
      have hh := starNext (Fin.last H.dividerCount)
      simpa only [Fin.succ_last, H.terminalStage] using hh
    have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
      by_cases hpe : P.corresponding.replacementETT.series.data.kind n =
          some TashkinovExtensionKind.PE
      · exact (P.replacementBase.parallel hpe).2.2.some.leftSegment
      · rw [P.replacementBase.nonparallel hpe]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
      by_cases hq : H.dividerCount = 0
      · have he : A = P.replacementBase.core := by
          simp [A, HierarchyStarredStage, hq, Fin.last]
        rw [he]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      · have he : A = H.stage ⟨H.dividerCount, by omega⟩ := by
          unfold A HierarchyStarredStage
          obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
          · have hv := congrArg Fin.val hz
            simp only [Fin.val_last, Fin.val_zero] at hv
            contradiction
          · rw [hi]
            simp only [Fin.cases_succ]
            congr 1
            apply Fin.ext
            have hv := congrArg Fin.val hi
            simp only [Fin.val_last, Fin.val_succ] at hv
            exact hv.symm
        rw [he]
        exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
          (by change 1 ≤ H.dividerCount; omega))
    have hTnA := trans hTnCore coreA
    have hlenT : 3 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    let X := TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
    have hBlength : B.length = T.length - 1 := rfl
    have hXlength : X.length = T.length - 2 := rfl
    have hBT : TreeSequenceInitialSegment B T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have hXT : TreeSequenceInitialSegment X T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have common {S U W : TreeSequence G e0}
        (hSW : TreeSequenceInitialSegment S W)
        (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
        TreeSequenceInitialSegment S U := by
      refine ⟨hlen, ?_, ?_⟩
      · intro i
        exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
      · intro i
        exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
    have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by omega)
    have hXB : TreeSequenceInitialSegment X B := common hXT hBT (by omega)
    have hTnX := trans hTnA hAX
    have hAB := trans hAX hXB
    have hfull : HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1) = B := by
      have hnum : min ((HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length +
          (HierarchyFullTailLength C - 1)) T.length = T.length - 1 := by
        unfold HierarchyFullTailLength
        dsimp only
        rw [hAold]
        omega
      simp only [HierarchyFullTailPrefix, hnum]
      rfl
    have halphaB : alpha ∈ MissingColors G mu (B.vertex (Fin.last B.length)) := by
      rw [hfull] at haB
      exact haB
    let r : Fin T.length := ⟨T.length - 1, by omega⟩
    let f := T.edge r
    let y := B.vertex (Fin.last B.length)
    let w := T.vertex (Fin.last T.length)
    have hy : T.vertex r.castSucc = y := by rfl
    have hw : T.vertex r.succ = w := by
      apply congrArg T.vertex
      apply Fin.ext
      dsimp [r]
      omega
    have consecutive (t : Fin T.length) (ht : A.length + 1 ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
        ∀ t : Fin T.length, A.length + i ≤ t.val →
          G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
      have hp' := hp
      change (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) = 1 at hp'
      have hn : candidates.Nonempty := by
        by_contra hn
        have hp'' : T.length - A.length = 1 := by
          simpa only [dif_neg hn] using hp'
        omega
      have hm : candidates.min' hn = 1 := by
        simpa only [dif_pos hn] using hp'
      have hc := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      rw [hm] at hc
      exact hc t ht
    have hends : G.ends f = s(y, w) :=
      (consecutive r (by dsimp [r]; omega)).trans (by rw [hy, hw])
    have hyf : Incident G y f := by rw [Incident, hends]; exact Sym2.mem_mk_left _ _
    have hwf : Incident G w f := by rw [Incident, hends]; exact Sym2.mem_mk_right _ _
    have hsource : ∃ S : TreeSequence G e0,
        S.length ≤ B.length ∧ TashkinovAugmentationSequence mu S T := by
      rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu
        P.corresponding.replacementETT with ⟨hpe, hseq⟩ |
          ⟨hkind, edge, seed, hedges, hseed, hincident, hcontrol, hseq⟩
      · exact ⟨Tn, by have := hTnX.1; omega, hseq⟩
      · have hseedLen : seed.length = Tn.length + 1 := hseed.1
        exact ⟨seed, by have := hTnX.1; omega, hseq⟩
    obtain ⟨S, hSBlen, hseq⟩ := hsource
    obtain ⟨hlen, hpre, beta, hbetaColor, hbetaMissing⟩ :=
      (TashkinovAugmentationSequencePosition mu S T hseq r
        (by simpa only [B, TreeSequencePrefix, r] using hSBlen)).1
    have hbetaF : mu f = some beta := by
      convert hbetaColor using 1
      congr 2
    have hbetaB : beta ∈ TreeMissingColors mu B := hbetaMissing
    obtain ⟨z, hzB, hbetaz⟩ := Finset.mem_biUnion.mp hbetaB
    have hzy : z ≠ y := by
      intro he
      subst z
      have hnot : beta ∉ MissingColors G mu y := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun h => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hyf, hbetaF⟩)
      exact hnot hbetaz
    have hzX : z ∈ TreeSequenceVertexSet X := by
      obtain ⟨j, hj⟩ : ∃ j, B.vertex j = z := by simpa [TreeSequenceVertexSet] using hzB
      have hjlt : j.val < B.length := by
        by_contra hh
        have he : j = Fin.last B.length := Fin.ext (by simpa using Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_gt hh))
        exact hzy (hj.symm.trans (congrArg B.vertex he))
      let jX : Fin (X.length + 1) := ⟨j.val, by omega⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨jX, hj⟩
    have hab : alpha ≠ beta := by
      intro he
      have halphaPresent : alpha ∈ PresentColors G mu y := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hyf, by rw [he]; exact hbetaF⟩
      exact (Finset.mem_sdiff.mp halphaB).2 halphaPresent
    let sigma : PartialEdgeColoring E k := fun e => if e = f then some alpha else mu e
    have fixed (e : E) (hef : e ≠ f) : sigma e = mu e := by simp [sigma, hef]
    have hsproper : IsProperEdgeColoring G sigma := by
      intro e g c heg hadj he hg
      by_cases hef : e = f
      · subst e
        have hgf : g ≠ f := heg.symm
        have hc : c = alpha := by simpa [sigma] using he.symm
        subst c
        rw [fixed g hgf] at hg
        obtain ⟨v, hvf, hvg⟩ := hadj
        have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
        rcases hv with rfl | rfl
        · exact (Finset.mem_sdiff.mp halphaB).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
        · exact (Finset.mem_sdiff.mp haT).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
      · by_cases hgf : g = f
        · subst g
          have hc : c = alpha := by simpa [sigma] using hg.symm
          subst c
          rw [fixed e hef] at he
          obtain ⟨v, hve, hvf⟩ := hadj
          have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
          rcases hv with rfl | rfl
          · exact (Finset.mem_sdiff.mp halphaB).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
          · exact (Finset.mem_sdiff.mp haT).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
        · exact P.minimumContext.proper heg hadj ((fixed e hef).symm.trans he)
            ((fixed g hgf).symm.trans hg)
    have hfe0 : f ≠ e0 := by
      intro he
      have hh := T.edge_injective (he.trans T.first_edge.symm)
      have hv := congrArg Fin.val hh
      dsimp [r] at hv
      omega
    have hsone : IsOneEdgeUncolored sigma e0 := by
      refine ⟨?_, ?_⟩
      · rw [fixed e0 hfe0.symm]
        exact P.minimumContext.oneEdgeUncolored.1
      · intro e he
        by_cases hef : e = f
        · subst e; exact ⟨alpha, by simp [sigma]⟩
        · rw [fixed e hef]
          exact P.minimumContext.oneEdgeUncolored.2 e he
    have noInc (v : V) (hv : v ∈ TreeSequenceVertexSet X) : ¬ Incident G v f := by
      obtain ⟨j, hj⟩ : ∃ j, X.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
      intro hi
      have hv' : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hi
      rcases hv' with he | he
      · have hh := T.vertex_injective ((hXT.2.1 j).trans (hj.trans (he.trans hy.symm)))
        have hh := congrArg Fin.val hh
        have hj := j.isLt
        change j.val = T.length - 1 at hh
        change j.val < X.length + 1 at hj
        omega
      · have hh := T.vertex_injective ((hXT.2.1 j).trans (hj.trans he))
        have hh := congrArg Fin.val hh
        have hj := j.isLt
        change j.val = T.length at hh
        change j.val < X.length + 1 at hj
        omega
    have incidentFixed (e : E) (he : TreeIncidentEdge X e) : sigma e = mu e := by
      apply fixed
      intro hef
      obtain ⟨v, hv, hi⟩ := he
      exact noInc v hv (hef ▸ hi)
    have missingFixed (v : V) (hv : v ∈ TreeSequenceVertexSet X) :
        MissingColors G sigma v = MissingColors G mu v := by
      unfold MissingColors PresentColors
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨e, hi, hc⟩
      · exact ⟨e, hi, (incidentFixed e ⟨v, hv, hi⟩).symm.trans hc⟩
      · exact ⟨e, hi, (incidentFixed e ⟨v, hv, hi⟩).trans hc⟩
    have fixedB (t : Fin B.length) : sigma (B.edge t) = mu (B.edge t) := by
      apply fixed
      intro he
      have hh := T.edge_injective ((hBT.2.2 t).trans he)
      have hh := congrArg Fin.val hh
      have ht := t.isLt
      change t.val = T.length - 1 at hh
      omega
    have stable : StableColoring Tn
        (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
        (P.corresponding.replacementETT.series.data.coloring n) sigma := by
      rw [← P.corresponding.replacementETT.generatingColoring]
      refine ⟨?_, ?_⟩
      · intro e he _
        obtain ⟨v, hv, hi⟩ := he
        exact incidentFixed e ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnX hv, hi⟩
      · intro v hv
        exact missingFixed v (TreeSequenceInitialSegmentVertexSetSubset hTnX hv)
    have hrouteB :
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
            P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (edge : E) (seed : TreeSequence G e0),
            P.corresponding.replacementETT.series.data.connectingEdges n = {edge} ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧
            TashkinovAugmentationSequence sigma seed B) := by
      rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu
        P.corresponding.replacementETT with ⟨hpe, hseq⟩ |
          ⟨hkind, edge, seed, hedges, hseed, hincident, hcontrol, hseq⟩
      · have hpre := TashkinovAugmentationSequenceRestrict mu Tn B T hseq
          (trans hTnX hXB) hBT
        exact Or.inl ⟨hpe, TashkinovAugmentationSequenceColoringTransport mu sigma
          Tn X B hpre hXB (by omega) (fun t _ => fixedB t) missingFixed⟩
      · have hseedLen : seed.length = Tn.length + 1 := hseed.1
        have hseedB := common
          (TashkinovAugmentationSequenceInitialSegment mu seed T hseq) hBT
          (by have := hTnX.1; omega)
        have hpre := TashkinovAugmentationSequenceRestrict mu seed B T hseq hseedB hBT
        exact Or.inr ⟨hkind, edge, seed, hedges, hseed,
          TashkinovAugmentationSequenceColoringTransport mu sigma seed X B hpre hXB
            (by omega) (fun t _ => fixedB t) missingFixed⟩
    have missingTree (U : TreeSequence G e0)
        (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) :
        TreeMissingColors sigma U = TreeMissingColors mu U := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => missingFixed v (hUX hv))
    have boundaryEq (U : TreeSequence G e0)
        (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (c : Fin k) :
        BoundaryColorEdges G sigma (TreeSequenceVertexSet U) c =
          BoundaryColorEdges G mu (TreeSequenceVertexSet U) c := by
      apply Finset.filter_congr
      intro edge he
      obtain ⟨u, hu, v, hv, hends⟩ := by simpa [BoundaryEdges] using he
      have hi : TreeIncidentEdge X edge :=
        ⟨u, hUX hu, by rw [Incident, hends]; exact Sym2.mem_mk_left _ _⟩
      rw [incidentFixed edge hi]
    have minusEq (U : TreeSequence G e0)
        (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (R : Finset (Fin k)) :
        TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R := by
      unfold TreeColorSetMinusClosed TreeColorSetClosed
      rw [missingTree U hUX]
      simp only [boundaryEq U hUX]
    have lastPositive (hq : H.dividerCount ≠ 0) :
        A = H.stage ⟨H.dividerCount, by omega⟩ := by
      unfold A HierarchyStarredStage
      obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
      · exact (hq (by simpa using congrArg Fin.val hz)).elim
      · rw [hi]
        simp only [Fin.cases_succ]
        congr 1
        exact Fin.ext (by simpa using (congrArg Fin.val hi).symm)
    have ordinaryA (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage j.castSucc) A := by
      by_cases hq : H.dividerCount = 0
      · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
        subst j
        simpa only [Fin.castSucc_zero, H.baseStage] using hTnA
      · rw [lastPositive hq]
        exact chain H.dividerCount (by omega) j.castSucc
          (by change j.val ≤ H.dividerCount; have := j.isLt; omega)
    have starA (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
      refine Fin.cases coreA (fun i => ordinaryA i.succ) j
    -- Retain the old prefix data; construct the recolored ETT separately.
    obtain ⟨eb, hmaxB, hrungB, hseriesB, baseB, hcoreB, hclosureB, hsupportB,
        HB, hcountB, hstagesB, hdividersB, goodB, hcolorsB⟩ :=
      GoodHierarchyTerminalPrefixRepackage G k e0 P.corresponding.replacementInput T
        mu mu P.corresponding.replacementETT old.maximum P.replacementBase H old.good
        B hAB (by change A.length < B.length; omega) hBT
    rcases eb with ⟨roundsB, positiveB, seriesB, aboveB, strictB, belowB, generatingB⟩
    dsimp only at hrungB hseriesB
    cases hrungB
    have hs : seriesB = P.corresponding.replacementETT.series := eq_of_heq hseriesB
    cases hs
    let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu := {
      rounds := P.corresponding.replacementETT.rounds
      roundsPositive := positiveB
      series := P.corresponding.replacementETT.series
      abovePenultimate := aboveB
      strictAbovePenultimate := strictB
      belowFinal := belowB
      generatingColoring := generatingB }
    have coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X := by
      rw [hcoreB]
      exact TreeSequenceInitialSegmentVertexSetSubset (trans coreA hAX)
    have closureBX (hpe : EB.series.data.kind (Fin.last EB.rounds) =
        some TashkinovExtensionKind.PE) :
        TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X := by
      obtain ⟨union⟩ := (baseB.parallel hpe).2.2
      intro v hv
      apply coreBX
      rw [union.vertexSet]
      exact Finset.mem_union_right _ hv
    -- PE preparation rebuilds the base; SE/RE retain the exact seed.
    have hdata : ∃ corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B,
        MaximumProperty corr.replacementETT ∧
        ∃ bs : HierarchyBase corr.replacementETT sigma,
          ∃ K : TashkinovHierarchy corr.replacementETT bs,
            SameHierarchyStages HB K := by
      by_cases hpe : EB.series.data.kind (Fin.last EB.rounds) =
          some TashkinovExtensionKind.PE
      · have hb : TashkinovAugmentationSequence sigma Tn B := by
          rcases hrouteB with h | h
          · exact h.2
          · rcases h.1 with h | h <;> rw [hpe] at h <;> cases h
        have hcomb : CombinedStableColoring Tn baseB.closure
            (TashkinovStoredColors EB.series.data (Fin.last EB.rounds)) mu sigma := by
          refine ⟨?_, ?_⟩
          · have hh := stable
            change StableColoring Tn
              (TashkinovStoredColors EB.series.data (Fin.last EB.rounds))
              (P.corresponding.replacementETT.series.data.coloring
                (Fin.last P.corresponding.replacementETT.rounds)) sigma at hh
            rw [← P.corresponding.replacementETT.generatingColoring] at hh
            exact hh
          · refine ⟨?_, ?_⟩
            · intro edge he _
              obtain ⟨v, hv, hi⟩ := he
              exact incidentFixed edge ⟨v, closureBX hpe hv, hi⟩
            · intro v hv
              exact missingFixed v (closureBX hpe hv)
        exact HierarchySplitter G k e0 P.corresponding.replacementInput B mu sigma EB
          hmaxB old.positive P.minimumContext.lowerRung baseB HB hpe
          P.minimumContext.proper P.minimumContext.oneEdgeUncolored hsproper hsone hcomb hb
      · have hmodB := Td G k e0 P.corresponding.replacementInput B mu EB hmaxB
          old.positive P.minimumContext.lowerRung sigma hsproper hsone stable
        obtain ⟨corr⟩ := hmodB.2.2 B aboveB strictB hrouteB
        have hmaximum := MaximumPropertyTransport G k e0 EB sigma hmodB B corr hmaxB
        have terminalTree : corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
          rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
          rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
          cases hr
          have hs : data = rs := eq_of_heq hp
          cases hs
          let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
          have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
            dsimp [j]; have := EB.roundsPositive; omega)
          change rs.data.tree (Fin.last EB.rounds).castSucc =
            EB.series.data.tree (Fin.last EB.rounds).castSucc
          rw [← hj]
          exact hl j
        have terminalKind : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) = EB.series.data.kind (Fin.last EB.rounds) := by
          rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
          rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
          cases hr
          have hs : data = rs := eq_of_heq hp
          cases hs
          exact hk _
        let bs : HierarchyBase corr.replacementETT sigma := {
          core := baseB.core
          closure := baseB.closure
          supportPosition := Fin.cast (congrArg (fun U : TreeSequence G e0 => U.length + 1)
            terminalTree.symm) baseB.supportPosition
          supportPositive := baseB.supportPositive
          terminalMissingColors := rfl
          parallel := by
            dsimp only
            intro hp
            exact (hpe (terminalKind.symm.trans hp)).elim
          nonparallel := by
            dsimp only
            intro _
            exact (baseB.nonparallel hpe).trans terminalTree.symm }
        let K : TashkinovHierarchy corr.replacementETT bs := {
          dividerCount := HB.dividerCount
          stage := HB.stage
          baseStage := HB.baseStage.trans terminalTree.symm
          terminalStage := HB.terminalStage
          nested := HB.nested
          strict := HB.strict
          dividerPosition := HB.dividerPosition
          dividerPositive := HB.dividerPositive
          dividerIncreasing := HB.dividerIncreasing
          dividerStage := HB.dividerStage
          coreInsideFirst := HB.coreInsideFirst }
        refine ⟨corr, hmaximum, bs, K, rfl, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
        · exact ⟨fun h => (hpe h).elim, fun h => (hpe (terminalKind.symm.trans h)).elim⟩
        · intro _; rfl
    obtain ⟨corr, hmaximum, bs, K, hsame⟩ := hdata
    let KF := K
    rcases hsame with ⟨hcore, hcount, hstage, hposition, hpe, hclosure⟩
    rcases K with ⟨qK, stageK, baseStageK, terminalStageK, nestedK, strictK,
      positionK, positiveK, increasingK, dividerStageK, coreInsideK⟩
    change HB.dividerCount = qK at hcount
    cases hcount
    have hs : HB.stage = stageK := eq_of_heq hstage
    cases hs
    have hpos : HB.dividerPosition = positionK := eq_of_heq hposition
    cases hpos
    have starredEq (j : Fin (HB.dividerCount + 1)) :
        HierarchyStarredStage KF j = HierarchyStarredStage HB j := by
      refine Fin.cases hcore.symm (fun _ => rfl) j
    have stageBX (j : Fin (HB.dividerCount + 1)) :
        TreeSequenceInitialSegment (HB.stage j.castSucc) X := by
      rw [(hstagesB j).1]
      exact trans (ordinaryA _) hAX
    have starBX (j : Fin (HB.dividerCount + 1)) :
        TreeSequenceVertexSet (HierarchyStarredStage HB j) ⊆ TreeSequenceVertexSet X := by
      rw [(hstagesB j).2]
      exact TreeSequenceInitialSegmentVertexSetSubset (trans (starA _) hAX)
    have allStageB (j : Fin (HB.dividerCount + 2)) :
        TreeSequenceInitialSegment (HB.stage j) B := by
      exact Fin.reverseInduction (motive := fun j =>
        TreeSequenceInitialSegment (HB.stage j) B)
        (by rw [HB.terminalStage]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
        (fun i hi => trans (HB.nested i) hi) j
    have terminalTree : corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
      rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
      rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
      cases hr
      have hs : data = rs := eq_of_heq hp
      cases hs
      let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
      have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
        dsimp [j]; have := EB.roundsPositive; omega)
      change rs.data.tree (Fin.last EB.rounds).castSucc =
        EB.series.data.tree (Fin.last EB.rounds).castSucc
      rw [← hj]
      exact hl j
    have terminalStored : TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) = TashkinovStoredColors EB.series.data
          (Fin.last EB.rounds) := by
      rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
      rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
      cases hr
      have hs : data = rs := eq_of_heq hp
      cases hs
      let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
      have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
        dsimp [j]; have := EB.roundsPositive; omega)
      have ht : rs.data.tree (Fin.last EB.rounds).castSucc = Tn := by
        change rs.data.tree (Fin.last EB.rounds).castSucc =
          EB.series.data.tree (Fin.last EB.rounds).castSucc
        rw [← hj]; exact hl j
      have hm : TreeMissingColors (rs.data.coloring (Fin.last EB.rounds))
          (rs.data.tree (Fin.last EB.rounds).castSucc) = TreeMissingColors mu Tn := by
        rw [← hc, ht]
        exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX)
      have hmOld : TreeMissingColors (EB.series.data.coloring (Fin.last EB.rounds))
          (EB.series.data.tree (Fin.last EB.rounds).castSucc) = TreeMissingColors mu Tn := by
        rw [← EB.generatingColoring]
      change TashkinovStoredColors rs.data (Fin.last EB.rounds) =
        TashkinovStoredColors EB.series.data (Fin.last EB.rounds)
      simp only [TashkinovStoredColors, hstored, hm, hmOld]
    have storedEq (j : Fin (HB.dividerCount + 1)) :
        HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j := by
      unfold HierarchyStoredColorsAt
      dsimp only
      rw [terminalStored, starredEq j, missingTree _ (starBX j)]
    have stageMissingEq (j : Fin (HB.dividerCount + 1)) :
        HierarchyStageMissingColors KF j = HierarchyStageMissingColors HB j := by
      refine Fin.cases ?_ (fun i => ?_) j
      · change TreeMissingColors sigma
          (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) =
            TreeMissingColors mu Tn
        rw [terminalTree]
        exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX)
      · exact missingTree _ (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ))
    have earlyMissing (j : Fin (B.length + 1)) (hj : j.val < B.length) :
        MissingColors G sigma (B.vertex j) = MissingColors G mu (B.vertex j) := by
      let i : Fin (X.length + 1) := ⟨j.val, by omega⟩
      have he : Fin.castLE (Nat.succ_le_succ hXB.1) i = j := Fin.ext rfl
      apply missingFixed
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, by rw [← he, hXB.2.1 i]⟩
    -- Last-vertex changes preserve the totalized least missing position.
    have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
        (j : Fin (B.length + 1)) (hj : c ∈ MissingColors G psi (B.vertex j)) :
        (HierarchyFirstMissingPosition psi B c).val ≤ j.val := by
      let candidates := Finset.univ.filter fun j : Fin (B.length + 1) =>
        c ∈ MissingColors G psi (B.vertex j)
      have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hn : candidates.Nonempty := ⟨j, hm⟩
      unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact Finset.min'_le candidates j hm
    have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition psi B c).val < B.length) :
        c ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B c)) := by
      let candidates := Finset.univ.filter fun j : Fin (B.length + 1) =>
        c ∈ MissingColors G psi (B.vertex j)
      by_cases hn : candidates.Nonempty
      · unfold HierarchyFirstMissingPosition
        rw [dif_pos hn]
        exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
      · have hh : (HierarchyFirstMissingPosition psi B c).val = B.length := by
          unfold HierarchyFirstMissingPosition
          rw [dif_neg hn]
          rfl
        omega
    have firstEq (c : Fin k) : HierarchyFirstMissingPosition sigma B c =
        HierarchyFirstMissingPosition mu B c := by
      apply Fin.ext
      apply Nat.le_antisymm
      · by_contra hn
        have hlt : (HierarchyFirstMissingPosition mu B c).val < B.length := by
          have := (HierarchyFirstMissingPosition sigma B c).isLt
          omega
        have hm := firstMem mu c hlt
        rw [← earlyMissing _ hlt] at hm
        have := firstLe sigma c _ hm
        omega
      · by_contra hn
        have hlt : (HierarchyFirstMissingPosition sigma B c).val < B.length := by
          have := (HierarchyFirstMissingPosition mu B c).isLt
          omega
        have hm := firstMem sigma c hlt
        rw [earlyMissing _ hlt] at hm
        have := firstLe mu c _ hm
        omega
    have stageFixed (j : Fin (HB.dividerCount + 1)) (t : Fin (HB.stage j.succ).length) :
        sigma ((HB.stage j.succ).edge t) = mu ((HB.stage j.succ).edge t) := by
      rw [← (allStageB j.succ).2.2 t]
      exact fixedB _
    have segmentEq (j : Fin (HB.dividerCount + 1)) (c : Fin k) :
        HierarchySegmentColors KF j c = HierarchySegmentColors HB j c := by
      unfold HierarchySegmentColors
      dsimp only
      rw [starredEq j, firstEq c]
      apply Finset.filter_congr
      intro d _
      constructor <;> rintro ⟨r, hlo, hhi, hcol⟩
      · exact ⟨r, hlo, hhi, (stageFixed j r).symm.trans hcol⟩
      · exact ⟨r, hlo, hhi, (stageFixed j r).trans hcol⟩
    let goodS : GoodHierarchy KF := {
      gamma := goodB.gamma
      twoColors := by
        intro j c hc
        exact goodB.twoColors j c (by rw [storedEq j] at hc; exact hc)
      avoidance := by
        intro j c hc
        rw [stageMissingEq j, segmentEq j c]
        exact goodB.avoidance j c (by rw [storedEq j] at hc; exact hc)
      disjointPairs := by
        intro j c d hc hd hne
        exact goodB.disjointPairs j c d (by rw [storedEq j] at hc; exact hc)
          (by rw [storedEq j] at hd; exact hd) hne
      uniqueRefresh := by
        intro i
        have hnew :
            ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
                fun v => MissingColors G sigma v) =
            ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
                fun v => MissingColors G mu v) := by
          apply Finset.biUnion_congr rfl
          intro v hv
          exact missingFixed v (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ)
            (Finset.mem_sdiff.mp hv).1)
        change ∃! c : Fin k,
          c ∈ HierarchyStoredColorsAt KF i.succ ∧
            goodB.gamma i.succ c ⊆
              ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
                TreeSequenceVertexSet (HierarchyStarredStage KF i.castSucc)).biUnion
                  fun v => MissingColors G sigma v) ∧
            ∀ d ∈ HierarchyStoredColorsAt KF i.succ, d ≠ c →
              goodB.gamma i.succ d = goodB.gamma i.castSucc d
        rw [starredEq i.castSucc, hnew]
        simp only [storedEq]
        exact goodB.uniqueRefresh i
      parallelBase := by
        dsimp only
        intro hp
        have hpB := hpe.mpr hp
        have hcl : bs.closure = baseB.closure := (hclosure hpB).symm
        obtain ⟨hnot, hcard⟩ := goodB.parallelBase hpB
        constructor
        · change ¬ TreeColorSetMinusClosed G sigma bs.core
            ((HierarchyStoredColorsAt KF 0).biUnion (goodB.gamma 0))
          rw [← hcore, storedEq 0, minusEq baseB.core coreBX]
          exact hnot
        · change 4 ≤ ((TreeMissingColors sigma
            (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) ∩
            TreeMissingColors sigma bs.closure) \
              (HierarchyStoredColorsAt KF 0).biUnion (goodB.gamma 0)).card
          rw [terminalTree, hcl, storedEq 0,
            missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX),
            missingTree baseB.closure (closureBX hpB)]
          exact hcard
      minusClosed := by
        intro i
        change TreeColorSetMinusClosed G sigma (HB.stage i.succ.castSucc)
          ((HierarchyStoredColorsAt KF i.succ).biUnion (goodB.gamma i.castSucc))
        rw [storedEq i.succ, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ))]
        exact goodB.minusClosed i }
    have hbetaY : beta ∈ MissingColors G sigma y := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hp
      obtain ⟨edge, hi, hc⟩ := (Finset.mem_filter.mp hp).2
      by_cases hef : edge = f
      · subst edge
        have he : alpha = beta := by simpa [sigma] using hc
        exact hab he
      · have hcOld : mu edge = some beta := (fixed edge hef).symm.trans hc
        exact P.minimumContext.proper hef ⟨y, hi, hyf⟩ hcOld hbetaF
    have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) := by
      intro he
      have hbetazS : beta ∈ MissingColors G sigma z := by rw [missingFixed z hzX]; exact hbetaz
      have hyB : y ∈ TreeSequenceVertexSet B := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨Fin.last B.length, rfl⟩
      exact Finset.disjoint_left.mp (he hzB hyB hzy) hbetazS hbetaY
    let CS : HierarchyCounterexample bs := {
      positive := by rw [corr.rungAgreement]; exact old.positive
      hierarchy := KF
      good := goodS
      maximum := hmaximum
      notElementary := hnotElementary }
    have lastStar : HierarchyStarredStage KF (Fin.last KF.dividerCount) = A := by
      rw [starredEq]
      have hh := (hstagesB (Fin.last HB.dividerCount)).2
      have hi : Fin.cast (congrArg (fun q => q + 1) hcountB)
          (Fin.last HB.dividerCount) = Fin.last H.dividerCount :=
        Fin.ext hcountB
      simpa only [hi] using hh
    have hpS : HierarchyPathNumber KF = 1 := by
      let candidates := (Finset.Icc 1 (B.length - A.length)).filter fun i =>
        ∀ t : Fin B.length, A.length + i ≤ t.val →
          G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
      have hm : 1 ∈ candidates := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
        intro t ht
        rw [← hBT.2.2 t]
        have hc := consecutive (Fin.castLE hBT.1 t) ht
        have hv1 : (Fin.castLE hBT.1 t).castSucc =
            Fin.castLE (Nat.succ_le_succ hBT.1) t.castSucc := Fin.ext rfl
        have hv2 : (Fin.castLE hBT.1 t).succ =
            Fin.castLE (Nat.succ_le_succ hBT.1) t.succ := Fin.ext rfl
        rw [hv1, hv2, hBT.2.1 t.castSucc, hBT.2.1 t.succ] at hc
        exact hc
      have hn : candidates.Nonempty := ⟨1, hm⟩
      have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).1).1
      have hhi := Finset.min'_le candidates 1 hm
      unfold HierarchyPathNumber
      dsimp only
      rw [lastStar]
      change (if h : candidates.Nonempty then candidates.min' h else B.length - A.length) = 1
      rw [dif_pos hn]
      omega
    have lastOrdinary : HB.stage (Fin.last HB.dividerCount).castSucc =
        H.stage (Fin.last H.dividerCount).castSucc := by
      have hh := (hstagesB (Fin.last HB.dividerCount)).1
      have hi : Fin.cast (congrArg (fun q => q + 1) hcountB)
          (Fin.last HB.dividerCount) = Fin.last H.dividerCount :=
        Fin.ext hcountB
      simpa only [hi] using hh
    have hlastLength : (H.stage (Fin.last H.dividerCount).castSucc).length < B.length := by
      have hh := HB.strict (Fin.last HB.dividerCount)
      simpa only [lastOrdinary, Fin.succ_last, HB.terminalStage] using hh
    -- The comparison is at the original rung and divider count.
    apply P.minimumContext.lexicographicMinimality CS corr.rungAgreement hcountB
    change HierarchyCounterexampleLess
      (HierarchyPathNumber KF, B.length - (HB.stage ⟨HB.dividerCount, by omega⟩).length)
      (HierarchyPathNumber H, T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
    rw [hpS, hp]
    right
    refine ⟨rfl, ?_⟩
    have hidx : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
        (Fin.last HB.dividerCount).castSucc := Fin.ext rfl
    have hidxH : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
        (Fin.last H.dividerCount).castSucc := Fin.ext rfl
    rw [hidx, hidxH, lastOrdinary]
    dsimp only
    omega
