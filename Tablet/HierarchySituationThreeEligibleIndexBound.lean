import Tablet.P2963_T1_TerminalKempeStageSwitch
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.TreeSequencePrefix
import Tablet.P2813_T1_TerminalRoute
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.ChangeLemma
import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyEligibleCommonMissingIndices
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchySegmentColors
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySplitter
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.MaximumPropertyTransport
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
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: HierarchySituationThreeEligibleIndexBound]
theorem HierarchySituationThreeEligibleIndexBound {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty) :
    ∀ i ∈ HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx,
      i < HierarchyPathNumber C.hierarchy := by
-- BODY
  classical
  have shortening (hlast : HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx) : False := by
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
      have hp : HierarchyPathNumber H = HierarchyPathNumber C.hierarchy := by
        unfold HierarchyPathNumber
        dsimp only
        rw [hAold]
      have hpLower : 2 ≤ HierarchyPathNumber H := by rw [hp]; exact hpathLower
      have hpUpper : HierarchyPathNumber H < T.length - A.length := by
        rw [hp]
        have hh := hpathUpper
        unfold HierarchyFullTailLength at hh
        dsimp only at hh
        rw [hAold] at hh
        exact hh
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
      have consecutive (t : Fin T.length)
          (ht : A.length + HierarchyPathNumber H ≤ t.val) :
          G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
        let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
          ∀ t : Fin T.length, A.length + i ≤ t.val →
            G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
        have hp' : HierarchyPathNumber H =
            (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
        have hn : candidates.Nonempty := by
          by_contra hn
          rw [dif_neg hn] at hp'
          omega
        have hm : candidates.min' hn = HierarchyPathNumber H := by
          simpa only [dif_pos hn] using hp'.symm
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
      have hpS : HierarchyPathNumber KF ≤ HierarchyPathNumber H := by
        let candidates := (Finset.Icc 1 (B.length - A.length)).filter fun i =>
          ∀ t : Fin B.length, A.length + i ≤ t.val →
            G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
        have hm : HierarchyPathNumber H ∈ candidates := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by
            dsimp [B, TreeSequencePrefix]
            omega⟩, ?_⟩
          intro t ht
          rw [← hBT.2.2 t]
          have hc := consecutive (Fin.castLE hBT.1 t) ht
          have hv1 : (Fin.castLE hBT.1 t).castSucc =
              Fin.castLE (Nat.succ_le_succ hBT.1) t.castSucc := Fin.ext rfl
          have hv2 : (Fin.castLE hBT.1 t).succ =
              Fin.castLE (Nat.succ_le_succ hBT.1) t.succ := Fin.ext rfl
          rw [hv1, hv2, hBT.2.1 t.castSucc, hBT.2.1 t.succ] at hc
          exact hc
        have hn : candidates.Nonempty := ⟨HierarchyPathNumber H, hm⟩
        unfold HierarchyPathNumber
        dsimp only
        rw [lastStar]
        change (if h : candidates.Nonempty then candidates.min' h else B.length - A.length) ≤ _
        rw [dif_pos hn]
        exact Finset.min'_le candidates _ hm
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
      by_cases hlt : HierarchyPathNumber KF < HierarchyPathNumber H
      · exact Or.inl hlt
      · right
        refine ⟨Nat.le_antisymm hpS (by omega), ?_⟩
        have hidx : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
            (Fin.last HB.dividerCount).castSucc := Fin.ext rfl
        have hidxH : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
            (Fin.last H.dividerCount).castSucc := Fin.ext rfl
        rw [hidx, hidxH, lastOrdinary]
        dsimp only
        omega

  classical
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
      change HierarchyPathNumber C.hierarchy < T.length - A.length at hpathUpper
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
        (haLast : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
        m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      have hm : 2 ≤ m := le_trans hpathLower hmLower
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
      by_cases hAlphaStored : alpha ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)
      · obtain ⟨gamma, hgamma, hgap⟩ := gammaChoice P alpha hAlphaStored (T.edge tnext)
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
      · by_cases hThetaStored : theta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
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
    intro i hi
    by_contra hn
    let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
    have hI : I.Nonempty := ⟨i, hi⟩
    let m := I.max' hI
    have hmI : m ∈ I := Finset.max'_mem I hI
    have him : i ≤ m := Finset.le_max' I i hi
    have hmBounds : 1 ≤ m ∧ m ≤ HierarchyFullTailLength C - 1 :=
      Finset.mem_Icc.mp (Finset.mem_filter.mp hmI).1
    obtain ⟨P, alpha, ha, haLast⟩ := (Finset.mem_filter.mp hmI).2
    by_cases hlast : m = HierarchyFullTailLength C - 1
    · exact shortening (hlast ▸ hmI)
    · have hnext := advance m (by omega) (by omega) P alpha ha haLast
      have hh : m + 1 ≤ m := Finset.le_max' I (m + 1) hnext
      omega
