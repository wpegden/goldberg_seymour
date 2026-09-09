import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.OrderedTreeUnion
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: AlgorithmFiveFiveSeed]
theorem AlgorithmFiveFiveSeed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (base : HierarchyBase ett phi)
    (hcoreStrict :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          base.core.length)
    (hcoreClosure :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        TashkinovClosure phi base.core
          (ett.series.data.tree (Fin.last (ett.rounds + 1)))) :
    ∃ (J : TreeSequence G e0)
        (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J),
      MaximumProperty corrJ.replacementETT ∧
      TreeSequenceInitialSegment J
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) ∧
      ∃ baseJ : HierarchyBase corrJ.replacementETT phi,
        baseJ.core = base.core ∧
        baseJ.closure = base.closure ∧
        baseJ.supportPosition.val = base.supportPosition.val ∧
        ∃ KJ : TashkinovHierarchy corrJ.replacementETT baseJ,
          KJ.dividerCount = 0 ∧
          KJ.stage 0 =
            ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
          KJ.stage (Fin.last (KJ.dividerCount + 1)) = J ∧
          ((ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE ∧
              J = base.core) ∨
            ((ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.RE) ∧
              ∃ f : E,
                ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
                TreeSequenceAdjoinEdge
                  (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                  f J ∧
                TashkinovAugmentationSequence phi J
                  (ett.series.data.tree (Fin.last (ett.rounds + 1))))) := by
-- BODY
  sorry
