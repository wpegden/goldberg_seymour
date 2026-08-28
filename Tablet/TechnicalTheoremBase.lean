import Tablet.ColoredVertexSetClosed
import Tablet.KTriple
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TashkinovTree
import Tablet.TechnicalTheoremBaseClaims
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TashTree
import Tablet.Tchange
import Tablet.sc1

-- [TABLET NODE: TechnicalTheoremBase]
theorem TechnicalTheoremBase {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) :
    TechnicalTheoremBaseClaims series := by
-- BODY
  sorry
