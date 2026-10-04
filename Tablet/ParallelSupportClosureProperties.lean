import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HkuTreeColorsControlled
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: ParallelSupportClosureProperties]
theorem ParallelSupportClosureProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (base : HierarchyBase ett sigma) :
    ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet base.closure) ∧
      ColoredVertexSetClosed G sigma
        (TreeSequenceVertexSet base.closure) ∧
      ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma base.closure ∨
          beta ∈ TreeMissingColors sigma base.closure) →
        TreeInterchangeable G base.closure sigma alpha beta := by
-- BODY
  sorry
