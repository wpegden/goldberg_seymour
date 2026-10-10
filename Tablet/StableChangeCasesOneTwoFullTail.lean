import Tablet.TechnicalTheoremBase
import Tablet.CertifiedETTPredecessor
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CombinedStableColoring
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchySegmentColors
import Tablet.HierarchySplitter
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyWeaklyStable
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColorSetClosed
import Tablet.TreeColoringInvariant
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorPathComponent
import Tablet.P2813_T1_BaseControl
import Tablet.P2813_T1_DisplayedEdges
import Tablet.P2813_T1_PrefixReconstruction
import Tablet.P2813_T1_MinusClosedTransport
import Tablet.P2813_T1_PrefixSegmentTransport
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequencePosition

-- [TABLET NODE: StableChangeCasesOneTwoFullTail]
theorem StableChangeCasesOneTwoFullTail {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      alpha ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
        beta ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va)))
    (htailEdges :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        sigma (T.edge t) = phi (T.edge t))
    (hpenultimateMissing :
      ∀ v, v ∈ TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) →
        MissingColors G sigma v = MissingColors G phi v)
    (hstoredFirst :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
      (A = Tn ∨
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            MaximumProperty ettA) ∧
      (∀ hq : 0 < H.dividerCount,
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            ∃ baseA : HierarchyBase ettA sigma,
              ∃ K : TashkinovHierarchy ettA baseA,
                ∃ goodA : GoodHierarchy K,
                  MaximumProperty ettA ∧
                    ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                      baseA.core = base.core ∧
                      baseA.closure = base.closure ∧
                      (∀ j : Fin (K.dividerCount + 2),
                        K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                      (∀ j : Fin (K.dividerCount + 1),
                        let jH : Fin (H.dividerCount + 1) :=
                          ⟨j.val, by omega⟩
                        HierarchyStoredColorsAt K j =
                            HierarchyStoredColorsAt H jH ∧
                          ∀ eta ∈ HierarchyStoredColorsAt K j,
                            goodA.gamma j eta = C.good.gamma jH eta) ∧
                      TreeColorSetMinusClosed G sigma Tnq
                        (Dnq.biUnion
                          (C.good.gamma ⟨C.hierarchy.dividerCount - 1,
                            by omega⟩))) ∧
      (∃ corrT : CorrespondingExtendedTashkinovTree
            G k e0 ett sigma T,
          MaximumProperty corrT.replacementETT ∧
            ∃ baseT : HierarchyBase corrT.replacementETT sigma,
              ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                ∃ goodT : GoodHierarchy K,
                  SameGoodHierarchy C.good goodT) := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  have htwo : 2 ≤ T.length - A.length :=
    HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  obtain ⟨hbase, missingA, sigmaProper, sigmaOne, outside⟩ :=
    P2813_T1_BaseControl G k e0 input T phi ett base C ctx helem
      alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  have preStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn) := by
    dsimp only
    by_cases hn : ett.rounds = 1
    · have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
        Fin.ext (by simp [hn])
      have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
        Fin.ext (by simp [n, hn])
      dsimp only [Tn]
      rw [hcolor, htree]
      exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    · have hmore : 1 < ett.rounds := by have := C.positive; omega
      obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
      have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
        Fin.ext rfl
      dsimp only [Tn]
      rw [htree]
      exact (ctx.lowerRung predecessor (by omega) (by omega) hmaximum).1

  have fixedA := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary helem alpha beta z sigma hsigma
    sigmaOne hbase outside
  obtain ⟨hmod, prefixPresentation⟩ := P2813_T1_PrefixReconstruction
    G k e0 input T phi ett base C ctx sigma sigmaProper sigmaOne hbase fixedA missingA
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at fixedA
  change (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) at missingA
  change (∀ t : Fin T.length, A.length ≤ t.val →
    sigma (T.edge t) = phi (T.edge t)) at htailEdges
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    clear * - hSU hUW
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
      (hlen : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
    clear * - hSW hUW hlen
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
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
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    clear * - H a d hbound segRefl segTrans
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
    have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
      Fin.ext (by have := j.isLt; simp only [Fin.val_mk, Fin.val_last]; omega)
    simpa [he, H.terminalStage] using hs
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    have hq : q = 0 := Fin.ext (by simpa [q] using hz)
    simp only [A, hq, HierarchyStarredStage]
    rfl
  have lastPositive (hz : H.dividerCount ≠ 0) : A = H.stage q.castSucc := by
    have hq : q ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [q, Fin.val_last, Fin.val_zero] at this
      exact hz this
    dsimp only [A]
    rw [← Fin.succ_pred q hq]
    rfl
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]; exact segRefl _
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : (⟨1 + (H.dividerCount - 1), by omega⟩ :
          Fin (H.dividerCount + 2)) = q.castSucc := Fin.ext (by simp [q]; omega)
      rw [he] at hs
      exact segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (base.parallel hp).2.2.some.leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT _)
    · rw [lastPositive hz]; exact stageToT _
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    by_cases hj : j.val = 0
    · have he : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext hj
      rw [he, H.baseStage]; exact TnToA
    · have hz : H.dividerCount ≠ 0 := by have := j.isLt; omega
      rw [lastPositive hz]
      have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
      have he : (⟨j.val + (H.dividerCount - j.val), by omega⟩ :
          Fin (H.dividerCount + 2)) = q.castSucc := Fin.ext (by simp [q]; omega)
      rw [he] at hs
      convert hs using 1
      apply congrArg H.stage
      apply Fin.ext
      rfl
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBlen : T.length = B.length + 1 := by
    change 2 ≤ T.length - A.length at htwo
    change T.length = min (A.length + ((T.length - A.length) - 1)) T.length + 1
    have := AToT.1
    omega
  have fixedT (t : Fin T.length) : sigma (T.edge t) = phi (T.edge t) := by
    by_cases ht : t.val < A.length
    · let ta : Fin A.length := ⟨t.val, ht⟩
      have he : Fin.castLE AToT.1 ta = t := Fin.ext rfl
      rw [← he, AToT.2.2 ta]
      exact fixedA ta
    · exact htailEdges t (by omega)
  have weak : HierarchyWeaklyStable H q sigma := by
    have allWeak (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma := by
      refine Fin.cases hbase (fun i => ⟨hbase, ?_⟩) j
      refine ⟨?_, ?_⟩
      · intro t _
        rw [← (ordinaryToA i.succ).2.2 t]
        exact fixedA _
      · intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv)
    exact allWeak q
  have treeMissingEq (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      missingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv))
  have combined (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma) at hbase
    simpa only [hp, if_true] using hbase
  have sigmaRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
      ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
    · exact Or.inl ⟨hp, TashkinovAugmentationSequenceColoringTransport phi sigma
        Tn B T hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩
    · obtain ⟨c, hc, hcol⟩ := hcontrol
      have seedFixed : sigma f = phi f := by
        have hs : StableColoring Tn Dn phi sigma := by
          change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
            CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma) at hbase
          split at hbase
          · exact hbase.1
          · exact hbase
        exact hs.1 f hincident ⟨c, hc, hcol⟩
      exact Or.inr ⟨hp, f, seed, hedges, hseed,
        TashkinovAugmentationSequenceColoringTransport phi sigma seed B T
          hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩
  have corrData (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
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
      have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases hs
      let a : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      have ha : a.succ = Fin.last ett.rounds := by
        apply Fin.ext
        change ett.rounds - 1 + 1 = ett.rounds
        have := ett.roundsPositive
        omega
      have ht : replacementSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
        change replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc
        rw [← ha]
        exact ladderTreesAgree a
      have hm : TreeMissingColors (replacementSeries.data.coloring (Fin.last ett.rounds))
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) = TreeMissingColors phi Tn := by
        rw [← finalGeneratingColoring, ht]
        exact treeMissingEq Tn TnToA
      have hmOld : TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) = TreeMissingColors phi Tn := by
        rw [← ett.generatingColoring]
      refine ⟨ht, extensionKindsAgree (Fin.last ett.rounds), ?_⟩
      change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
      simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]
  have fullBase :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
        MaximumProperty corr.replacementETT ∧
        ∃ baseT : HierarchyBase corr.replacementETT sigma,
          baseT.core = base.core ∧ baseT.closure = base.closure := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · have hb : TashkinovAugmentationSequence sigma Tn T := by
        rcases sigmaRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
        · exact hseq
        · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
      obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
        ett C.maximum C.positive ctx.lowerRung base H hp ctx.proper ctx.oneEdgeUncolored
        sigmaProper sigmaOne (combined hp) hb
      exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
    · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate sigmaRoute
      have hd := corrData corr
      let pos : Fin ((corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
        Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
          base.supportPosition
      let baseT : HierarchyBase corr.replacementETT sigma := {
        core := base.core
        closure := base.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using base.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only
          intro hPE
          exact False.elim (hp (hd.2.1.symm.trans hPE))
        nonparallel := by
          dsimp only
          intro _
          exact (base.nonparallel hp).trans hd.1.symm }
      exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum,
        baseT, rfl, rfl⟩
  obtain ⟨corrT, hmaximumT, baseT, hcoreT, hclosureT⟩ := fullBase
  have terminalData := corrData corrT
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans terminalData.1.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j :=
    Fin.cases hcoreT (fun _ => rfl) j
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalData.2.2, starredEq j, treeMissingEq _ (starredToA j)]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn TnToA
    · exact treeMissingEq _ (ordinaryToA i.succ)
  have segmentEq (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) :
      HierarchySegmentColors K j eta = HierarchySegmentColors H j eta := by
    clear * - j eta heta K H A q T phi sigma ordinaryToA AToT fixedA missingA
      starredEq stageToT fixedT hstoredFirst
    by_cases hj : j.val < H.dividerCount
    · have hjA : TreeSequenceInitialSegment (H.stage j.succ) A := by
        let js : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
        have he : js.castSucc = j.succ := Fin.ext rfl
        simpa only [he] using ordinaryToA js
      have hcut := HierarchyFirstMissingPositionPrefixCutoff sigma A T AToT eta
        (H.stage j.succ).length hjA.1
      have hseg := P2813_T1_PrefixSegmentTransport phi sigma (H.stage j.succ) A T
        hjA AToT fixedA missingA eta (HierarchyStarredStage H j).length
      unfold HierarchySegmentColors
      dsimp only
      rw [starredEq j, ← hcut]
      exact hseg
    · have he : j = q := Fin.ext (by simp [q]; have := j.isLt; omega)
      subst j
      unfold HierarchySegmentColors
      dsimp only
      rw [starredEq q, hstoredFirst eta heta]
      apply Finset.filter_congr
      intro c _
      constructor <;> rintro ⟨t, hlo, hhi, hc⟩ <;> refine ⟨t, hlo, hhi, ?_⟩
      · change sigma ((H.stage q.succ).edge t) = some c at hc
        have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
          rw [← (stageToT q.succ).2.2 t]
          exact fixedT _
        exact hf.symm.trans hc
      · have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
          rw [← (stageToT q.succ).2.2 t]
          exact fixedT _
        exact hf.trans hc
  -- The first refresh prevents the core from being the whole first stage.
  have coreStrict : base.core.length < (H.stage ⟨1, by omega⟩).length := by
    clear * - H C base A lastZero htwo equalTrees
    by_cases hz : H.dividerCount = 0
    · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
      rw [he, H.terminalStage]
      change 2 ≤ T.length - A.length at htwo
      rw [lastZero hz] at htwo
      omega
    · by_contra hnot
      have hlen : base.core.length = (H.stage ⟨1, by omega⟩).length := by
        have := H.coreInsideFirst.1
        omega
      have he := equalTrees H.coreInsideFirst hlen
      let i : Fin H.dividerCount := ⟨0, by omega⟩
      obtain ⟨eta, ⟨heta, hgamma, _⟩, _⟩ := C.good.uniqueRefresh i
      have hstage : H.stage i.succ.castSucc = base.core := by
        exact he.symm
      have hstar : HierarchyStarredStage H i.castSucc = base.core := rfl
      rw [hstage, hstar, Finset.sdiff_self, Finset.biUnion_empty] at hgamma
      have hempty : C.good.gamma i.succ eta = ∅ := Finset.subset_empty.mp hgamma
      have hcard := C.good.twoColors i.succ eta heta
      rw [hempty, Finset.card_empty] at hcard
      omega
  have parallelNotClosed (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      ¬ TreeColorSetMinusClosed G sigma base.core
        ((HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0)) := by
    clear * - hp G k e0 input T phi sigma ett H C base n Tn
      coreToA AToT TnToCore coreStrict equalTrees commonPrefix treeMissingEq fixedT segTrans
      stageToT
    have hseq : TashkinovAugmentationSequence phi Tn T := by
      rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
        ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    have coreToT := segTrans coreToA AToT
    have suffix := TashkinovAugmentationSequenceSuffix phi Tn base.core T
      hseq TnToCore coreToT
    let t : Fin T.length := ⟨base.core.length, by
      have := (stageToT ⟨1, by omega⟩).1
      omega⟩
    let S := TreeSequencePrefix T t.val base.core.positive (Nat.le_of_lt t.isLt)
    let U := TreeSequencePrefix T (t.val + 1) (by have := base.core.positive; omega)
      (Nat.succ_le_of_lt t.isLt)
    have hS : S = base.core := by
      apply (equalTrees (commonPrefix coreToT
        (show TreeSequenceInitialSegment S T from
          ⟨Nat.le_of_lt t.isLt, fun _ => rfl, fun _ => rfl⟩) le_rfl) rfl).symm
    have aug := (TashkinovAugmentationSequencePosition phi base.core T suffix t le_rfl).1
    change TashkinovAugmentation phi S U at aug
    obtain ⟨hlen, hSU, c, hcol, hcm⟩ := aug
    have hcolT : phi (T.edge t) = some c := by
      have he : U.edge (Fin.cast hlen.symm (Fin.last S.length)) = T.edge t := by
        change T.edge _ = T.edge t
        apply congrArg T.edge
        apply Fin.ext
        rfl
      rw [← he]
      exact hcol
    have hcmCore : c ∈ TreeMissingColors phi base.core := hS ▸ hcm
    have hcSigma : c ∈ TreeMissingColors sigma base.core := by
      rw [treeMissingEq base.core coreToA]; exact hcmCore
    have hreserved : c ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
      intro hc
      obtain ⟨eta, heta, hcg⟩ := Finset.mem_biUnion.mp hc
      have hn : eta ∉ TreeMissingColors phi base.core := (Finset.mem_sdiff.mp heta).2
      have hfirst : base.core.length < (HierarchyFirstMissingPosition phi T eta).val := by
        let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
          eta ∈ MissingColors G phi (T.vertex j)
        unfold HierarchyFirstMissingPosition
        change base.core.length < (if h : candidates.Nonempty then candidates.min' h
          else Fin.last T.length).val
        split
        · rename_i hnon
          by_contra hh
          have hle : (candidates.min' hnon).val ≤ base.core.length := by omega
          let j : Fin (base.core.length + 1) := ⟨(candidates.min' hnon).val, by omega⟩
          have he : Fin.castLE (Nat.succ_le_succ coreToT.1) j = candidates.min' hnon := Fin.ext rfl
          have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hnon)).2
          apply hn
          refine Finset.mem_biUnion.mpr ⟨base.core.vertex j, ?_, ?_⟩
          · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨j, rfl⟩
          · rw [← coreToT.2.1 j, he]; exact hm
        · exact t.isLt
      have hseg : c ∈ HierarchySegmentColors H 0 eta := by
        let r : Fin (H.stage (0 : Fin (H.dividerCount + 1)).succ).length :=
          ⟨base.core.length, coreStrict⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, r, le_rfl, Nat.lt_min.mpr ⟨hfirst, coreStrict⟩, ?_⟩
        have he : Fin.castLE (stageToT (0 : Fin (H.dividerCount + 1)).succ).1 r = t := Fin.ext rfl
        rw [← (stageToT (0 : Fin (H.dividerCount + 1)).succ).2.2 r, he]
        exact hcolT
      exact (Finset.mem_sdiff.mp (C.good.avoidance 0 eta heta hcg)).2 hseg
    have hboundary : T.edge t ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) := by
      clear * - T t base coreToT
      obtain ⟨i, hi⟩ := T.attaches t
      let old : Fin (base.core.length + 1) := ⟨i.val, i.isLt⟩
      let it : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ coreToT.1) old
      have hOld : T.vertex it = base.core.vertex old := coreToT.2.1 old
      have hNew : T.vertex t.succ ∉ TreeSequenceVertexSet base.core := by
        intro hv
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
        obtain ⟨j, hj⟩ := hv
        have he := T.vertex_injective (hj.symm.trans (coreToT.2.1 j).symm)
        have hval := congrArg Fin.val he
        have := j.isLt
        change base.core.length + 1 = j.val at hval
        omega
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨T.vertex it, ?_, T.vertex t.succ, hNew, ?_⟩
      · rw [hOld]
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨old, rfl⟩
      · have he : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt)) = it := Fin.ext rfl
        rw [hi, he]
        exact Sym2.eq_swap
    intro hclosed
    have hf : T.edge t ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) c :=
      Finset.mem_filter.mpr ⟨hboundary, (fixedT t).trans hcolT⟩
    rw [hclosed c (Finset.mem_sdiff.mpr ⟨hcSigma, hreserved⟩)] at hf
    exact Finset.notMem_empty _ hf
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      rw [stageMissingEq j, segmentEq j eta ho]
      exact C.good.avoidance j eta ho hc
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta
        (by rw [storedEq j] at heta; exact heta)
        (by rw [storedEq j] at htheta; exact htheta) hne
    uniqueRefresh := by
      intro i
      have hnew :
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G sigma v) =
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G phi v) := by
        apply Finset.biUnion_congr rfl
        intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ)
          (Finset.mem_sdiff.mp hv).1)
      change ∃! eta : Fin k,
        eta ∈ HierarchyStoredColorsAt K i.succ ∧
          C.good.gamma i.succ eta ⊆
            ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt K i.succ, theta ≠ eta →
            C.good.gamma i.succ theta = C.good.gamma i.castSucc theta
      rw [starredEq i.castSucc, hnew]
      simp only [storedEq]
      exact C.good.uniqueRefresh i
    parallelBase := by
      dsimp only
      intro hp
      have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans hp
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0]
        exact parallelNotClosed hpOld
      · change 4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
        have closureMissing : TreeMissingColors sigma base.closure =
            TreeMissingColors phi base.closure := by
          unfold TreeMissingColors
          exact Finset.biUnion_congr rfl (combined hpOld).2.2
        rw [terminalData.1, hclosureT, storedEq 0, treeMissingEq Tn TnToA, closureMissing]
        exact (C.good.parallelBase hpOld).2
    minusClosed := by
      intro i
      change TreeColorSetMinusClosed G sigma (H.stage i.succ.castSucc)
        ((HierarchyStoredColorsAt K i.succ).biUnion (C.good.gamma i.castSucc))
      rw [storedEq i.succ]
      apply P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
        ctx.proper ctx.oneEdgeUncolored _ (C.good.minusClosed i)
      · intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv)
      · exact outside i.succ }
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  have prefixMaximum : A = Tn ∨
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA := by
    rcases prefixPresentation with he | ⟨corrA, hMPA⟩
    · exact Or.inl he
    · exact Or.inr ⟨corrA.replacementInput, corrA.replacementETT, hMPA⟩
  refine ⟨weak, hmod, prefixMaximum, ?_, corrT, hmaximumT, baseT, K, goodT, same⟩
  intro hq
  have hqK : 1 ≤ q.val := by change 0 < H.dividerCount at hq; dsimp [q]; omega
  have hqpos : H.dividerCount ≠ 0 := by change 0 < H.dividerCount at hq; omega
  have hA : A = H.stage q.castSucc := lastPositive hqpos
  have positivePackage (U : TreeSequence G e0) (hU : U = H.stage q.castSucc) :
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA U sigma,
          ∃ baseA : HierarchyBase ettA sigma,
            ∃ KA : TashkinovHierarchy ettA baseA,
              ∃ goodA : GoodHierarchy KA,
                MaximumProperty ettA ∧
                  ∃ hcount : KA.dividerCount + 1 = H.dividerCount,
                    baseA.core = base.core ∧ baseA.closure = base.closure ∧
                    (∀ j : Fin (KA.dividerCount + 2),
                      KA.stage j = H.stage ⟨j.val, by omega⟩) ∧
                    (∀ j : Fin (KA.dividerCount + 1),
                      let jH : Fin (H.dividerCount + 1) := ⟨j.val, by omega⟩
                      HierarchyStoredColorsAt KA j = HierarchyStoredColorsAt H jH ∧
                        ∀ eta ∈ HierarchyStoredColorsAt KA j,
                          goodA.gamma j eta = C.good.gamma jH eta) ∧
                    TreeColorSetMinusClosed G sigma (H.stage ⟨H.dividerCount, by omega⟩)
                      ((HierarchyStoredColorsAt H q).biUnion
                        (C.good.gamma ⟨H.dividerCount - 1, by
                          exact Nat.lt_succ_of_le (Nat.sub_le H.dividerCount 1)⟩)) := by
    subst U
    obtain ⟨ettA, hMPA, hrA, hsA, baseA, hcoreA, hclosureA, hsupportA,
        KA, hcount, hstages, hdividers, goodA, hgammaA, hminusA⟩ :=
      GoodHierarchyPrefixRepackage G k e0 corrT.replacementInput T sigma sigma
        corrT.replacementETT hmaximumT baseT K goodT q hqK
    refine ⟨corrT.replacementInput, ettA, baseA, KA, goodA, hMPA, ?_⟩
    have hcount' : KA.dividerCount + 1 = H.dividerCount := by
      change KA.dividerCount = H.dividerCount - 1 at hcount
      change 0 < H.dividerCount at hq
      omega
    refine ⟨hcount', hcoreA.trans hcoreT, hclosureA.trans hclosureT, ?_, ?_, ?_⟩
    · intro j
      let jp : Fin (q.val + 1) := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
      have he : Fin.cast (by omega) jp = j := Fin.ext rfl
      simpa only [he] using hstages jp
    · intro j
      let jp : Fin q.val := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
      have he : Fin.cast (by omega) jp = j := Fin.ext rfl
      have hg := hgammaA jp
      simp only [he] at hg
      refine ⟨hg.1.trans (storedEq _), ?_⟩
      intro eta heta
      exact hg.2 eta
    · have he : (Fin.last H.dividerCount).castSucc =
          (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext rfl
      simpa [K, goodT, storedEq, q, he] using hminusA
  exact positivePackage A hA
