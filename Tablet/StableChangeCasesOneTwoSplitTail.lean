import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CombinedStableColoring
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
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
import Tablet.HierarchyWeaklyStable
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TashkinovAugmentation
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColoringInvariant
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorPathComponent

-- [TABLET NODE: StableChangeCasesOneTwoSplitTail]
theorem StableChangeCasesOneTwoSplitTail {V E : Type*}
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
    (X : TreeSequence G e0)
    (hAX :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      TreeSequenceInitialSegment A X)
    (hAXstrict :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      A.length < X.length)
    (hXB : TreeSequenceInitialSegment X
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (hfixedPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        sigma (T.edge t) = phi (T.edge t))
    (hrouteX :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn X) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed X))
    (hsuffix : TashkinovAugmentationSequence phi X T)
    (hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧
      beta ∈ TreeMissingColors sigma X)
    (hpenultimateMissing :
      ∀ v, v ∈ TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) →
        MissingColors G sigma v = MissingColors G phi v)
    (hstoredFirst :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta)
    (hgammaCutoff :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        (alpha ∈ C.good.gamma q eta ∨ beta ∈ C.good.gamma q eta) →
          (HierarchyFirstMissingPosition phi T eta).val ≤ X.length) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
      ∃ corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
        MaximumProperty corrT.replacementETT ∧
          ∃ baseT : HierarchyBase corrT.replacementETT sigma,
            ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
              ∃ goodT : GoodHierarchy K,
                SameGoodHierarchy C.good goodT := by
-- BODY
  sorry
