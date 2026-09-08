import Tablet.ChangeLemma
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationThreeColorChoice
import Tablet.HierarchySituationThreeClaimJMinusOneEmpty
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColorIncidenceEndpoint
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.Td
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeInterchangeable
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentTashkinovSplice
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc1

-- [TABLET NODE: HierarchySituationThreeComponentIntersectionShortening]
theorem HierarchySituationThreeComponentIntersectionShortening
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) /\
        alpha ∈ TreeMissingColors P.coloring B /\
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          exists eta : Fin k, eta ∈ D /\
            alpha ∈ P.counterexample.good.gamma q eta /\
            (HierarchyFirstMissingPosition P.coloring T eta).val <=
              B.length))
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          exists r : Fin T.length,
            A.length <= r.val /\ r.val < A.length + j /\
              P.coloring (T.edge r) = some c
      beta ≠ alpha /\
        beta ∈ TreeMissingColors P.coloring B /\
        beta ∉ Gamma /\ beta ∉ tailUsedThroughJ /\
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D /\
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ))
    (hintersection :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      ∃ u ∈ TreeSequenceVertexSet X,
        Sum.inl u ∈ TwoColorComponent G P.coloring alpha beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    False := by
-- BODY
  sorry
