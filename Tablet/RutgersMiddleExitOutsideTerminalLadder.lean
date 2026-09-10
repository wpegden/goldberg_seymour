import Tablet.BoundaryColorEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.RutgersClosedPresentation
import Tablet.RutgersCounterexample
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeExitPath
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeMissingColorsCardLowerBound
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: RutgersMiddleExitOutsideTerminalLadder]
theorem RutgersMiddleExitOutsideTerminalLadder
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentFour : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall (v : V) (gamma delta : Fin k),
        current.series.data.kind terminal = some TashkinovExtensionKind.PE ->
        current.series.data.chosenVertex terminal = some v ->
        current.series.data.gamma terminal = some gamma ->
        current.series.data.delta terminal = some delta ->
        forall sigma : PartialEdgeColoring E k,
          IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
          StableColoring Tterminal
            (TashkinovStoredColors current.series.data terminal)
            (current.series.data.coloring terminal) sigma ->
          forall w, w ∈ TreeSequenceVertexSet Tterminal ->
            (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                (Sum.inl v) <-> w = v))
    (hlowerTwo : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < original.rounds ->
      MaximumProperty lower ->
      let terminal : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let Tnext : TreeSequence G e0 :=
        lower.series.data.tree (Fin.last (lower.rounds + 1))
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tnext
          (TashkinovStoredColors lower.series.data terminal)
          (lower.series.data.coloring terminal) sigma ->
        forall alpha beta : Fin k,
          (alpha ∈ TreeMissingColors sigma Tnext ∨
            beta ∈ TreeMissingColors sigma Tnext) ->
          TreeInterchangeable G Tnext sigma alpha beta)
    (presentation : RutgersClosedPresentation G k e0 original)
    (counterexample : RutgersCounterexample G k e0 original presentation)
    (helementary : ColoredVertexSetElementary G presentation.sigma
      (TreeSequenceVertexSet presentation.U)) :
    let replacement := presentation.corresponding.replacementETT
    let terminal : Fin (replacement.rounds + 1) := Fin.last replacement.rounds
    counterexample.b2 ∉
      TreeSequenceVertexSet (replacement.series.data.tree terminal.castSucc) := by
-- BODY
  sorry
