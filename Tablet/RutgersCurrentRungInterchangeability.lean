import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.PartialEdgeColoring
import Tablet.RutgersClosedPresentation
import Tablet.RutgersCounterexample
import Tablet.RutgersCounterexampleMeasure
import Tablet.RutgersCounterexampleMinimumExists
import Tablet.RutgersMiddleExitOutsideTerminalLadder
import Tablet.RutgersStrictShortening
import Tablet.StableColoring
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: RutgersCurrentRungInterchangeability]
theorem RutgersCurrentRungInterchangeability
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty original)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentOne : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hcurrentFour : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall (v : V) (gamma delta : Fin k),
        current.series.data.kind terminal =
          some TashkinovExtensionKind.PE ->
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
          TreeInterchangeable G Tnext sigma alpha beta) :
    let terminal : Fin (original.rounds + 1) := Fin.last original.rounds
    let Tnext : TreeSequence G e0 :=
      original.series.data.tree (Fin.last (original.rounds + 1))
    forall sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
      StableColoring Tnext
        (TashkinovStoredColors original.series.data terminal)
        (original.series.data.coloring terminal) sigma ->
      forall alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma Tnext ∨
          beta ∈ TreeMissingColors sigma Tnext) ->
        TreeInterchangeable G Tnext sigma alpha beta := by
-- BODY
  sorry
