import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ElementaryClosedExitPairExtendsTriple
import Tablet.ElementaryClosedNoninterchangeableExitPair
import Tablet.HkuMissingStoredMonotone
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.RutgersClosedPresentation
import Tablet.RutgersCounterexample
import Tablet.RutgersCounterexampleMeasure
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeExitPath
import Tablet.TreeInterchangeable
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeVertexOrder
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent

-- [TABLET NODE: RutgersCounterexampleMinimumExists]
theorem RutgersCounterexampleMinimumExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty original)
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
      let n : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tn
          (TashkinovStoredColors current.series.data n)
          (current.series.data.coloring n) sigma ->
        ModColoring current sigma)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (original.series.data.tree (Fin.last (original.rounds + 1)))
      (TashkinovStoredColors original.series.data
        (Fin.last original.rounds))
      (original.series.data.coloring (Fin.last original.rounds)) sigma)
    (alpha beta : Fin k) (hcolors : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors sigma
      (original.series.data.tree (Fin.last (original.rounds + 1))))
    (hnot : ¬ TreeInterchangeable G
      (original.series.data.tree (Fin.last (original.rounds + 1)))
      sigma alpha beta) :
    exists (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample :
        RutgersCounterexample G k e0 original presentation),
      forall (otherPresentation :
          RutgersClosedPresentation G k e0 original)
        (otherCounterexample :
          RutgersCounterexample G k e0 original otherPresentation),
        RutgersCounterexampleMeasure counterexample <=
          RutgersCounterexampleMeasure otherCounterexample := by
-- BODY
  sorry
