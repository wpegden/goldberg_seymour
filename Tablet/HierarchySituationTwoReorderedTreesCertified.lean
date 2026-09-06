import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ColoredVertexSetClosed
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyStarredStage
import Tablet.TashkinovHierarchy
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentation
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.StableColoring
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.sc1

-- [TABLET NODE: HierarchySituationTwoReorderedTreesCertified]
theorem HierarchySituationTwoReorderedTreesCertified {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoTailData
      G k e0 input T phi ett base C ctx) :
    ∃ R : HierarchySituationTwoReorderedTrees
        G k e0 input T phi ett base C ctx D,
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
      (B = Tn →
          ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.minus) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.minus)) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.star) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.star)) ∧
        ∃ corrMinus : CorrespondingExtendedTashkinovTree
            G k e0 ett phi R.minus,
          MaximumProperty corrMinus.replacementETT ∧
            ∃ corrStar : CorrespondingExtendedTashkinovTree
                G k e0 ett phi R.star,
              MaximumProperty corrStar.replacementETT := by
-- BODY
  sorry
