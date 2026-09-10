import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.ElementaryClosedMissingColorOdd
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyBaseExists
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.ParallelClosureUnionElementary
import Tablet.StableColoring
import Tablet.TashkinovOrder
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColorsCardLowerBound
import Tablet.TreeSequenceInitialSegmentVertexSetStrict
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.sc2

-- [TABLET NODE: TechnicalCurrentLadderMissingBoundLarge]
theorem TechnicalCurrentLadderMissingBoundLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    2 * ett.rounds + 11 <= (TreeMissingColors generating Tn).card := by
-- BODY
  sorry
