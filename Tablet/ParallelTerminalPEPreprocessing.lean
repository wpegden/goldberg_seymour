import Tablet.Basic2
import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ExtensionBase
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: ParallelTerminalPEPreprocessing]
theorem ParallelTerminalPEPreprocessing {V E : Type*}
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
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∃ support common : V, ∃ gamma delta : Fin k,
      ett.series.data.chosenVertex n = some support ∧
      ett.series.data.gamma n = some gamma ∧
      ett.series.data.delta n = some delta ∧
      support ∈ TreeSequenceVertexSet Tn ∧
      support ∈ TreeSequenceVertexSet base.closure ∧
      common ∈ TreeSequenceVertexSet Tn ∧
      common ∈ TreeSequenceVertexSet base.closure ∧
      common ≠ support ∧
      delta ∈ MissingColors G sigma support ∧
      gamma ∉ TreeMissingColors sigma Tn ∧
      (MissingColors G sigma common).Nonempty ∧
      ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Tn) := by
-- BODY
  sorry
