import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ColoredVertexSetElementary
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyLEMStable
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchySituationTwoCommonTailData
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStoredColorsAt
import Tablet.IsProperEdgeColoring
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OutsideKempeRecoloring
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: HierarchySituationTwoOutsidePenultimateReconstruction]
theorem HierarchySituationTwoOutsidePenultimateReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hbetaMissingTwoBefore :
      beta ∈ TreeMissingColors phi
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)))
    (hbetaUnusedOnFullTail :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
    (hbetaAlternative :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Dn := TashkinovStoredColors ett.series.data n
      let Dnq := HierarchyStoredColorsAt H q
      let Gamma := Dnq.biUnion (C.good.gamma q)
      let A := HierarchyStarredStage H q
      let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ t : Fin T.length, A.length ≤ t.val ∧
          phi (T.edge t) = some c
      (0 < H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma) ∨
        (H.dividerCount = 0 ∧ beta ∉ Dn ∧ beta ∉ Gamma) ∨
        (beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed))
    (hbetaPresentTerminal :
      beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex))
    (houtsidePenultimate :
      let Bplus := HierarchyFullTailPrefix C
        (HierarchyFullTailLength C - 1)
      let yp := T.vertex D.terminalVertexIndex
      ∀ v : V,
        Sum.inl v ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp) →
          v ∉ TreeSequenceVertexSet Bplus) :
    let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    let yp := T.vertex D.terminalVertexIndex
    let Q := TwoColorComponent G phi D.alpha beta (Sum.inl yp)
    let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
    Sum.inl yp ∈ Q ∧
      (∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ Q) ∧
      ∃ P : HierarchyReplacementPresentation
          G k e0 input T phi ett base C ctx,
        P.coloring = sigma ∧
          ∃ N : HierarchySituationTwoCaseThreeNormalizedData
              G k e0 P.corresponding.replacementInput T P.coloring
                P.corresponding.replacementETT P.replacementBase
                P.counterexample P.minimumContext,
            N.alpha = beta := by
-- BODY
  sorry
