import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CorrespondingExtendedTashkinovTreeTransTrees
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.ModColoring
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.RutgersClosedPresentation
import Tablet.RutgersCounterexample
import Tablet.RutgersCounterexampleMeasure
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovStoredColors
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: RutgersStrictShortening]
theorem RutgersStrictShortening
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentOne : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hcurrentSix : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tterminal
          (TashkinovStoredColors current.series.data terminal)
          (current.series.data.coloring terminal) sigma ->
        ModColoring current sigma)
    (presentation : RutgersClosedPresentation G k e0 original)
    (counterexample : RutgersCounterexample G k e0 original presentation)
    (hmiddle :
      let replacement := presentation.corresponding.replacementETT
      let terminal : Fin (replacement.rounds + 1) :=
        Fin.last replacement.rounds
      counterexample.b2 ∉ TreeSequenceVertexSet
        (replacement.series.data.tree terminal.castSucc)) :
    exists (newPresentation : RutgersClosedPresentation G k e0 original)
      (newCounterexample :
        RutgersCounterexample G k e0 original newPresentation),
      RutgersCounterexampleMeasure newCounterexample <
        RutgersCounterexampleMeasure counterexample := by
-- BODY
  sorry
