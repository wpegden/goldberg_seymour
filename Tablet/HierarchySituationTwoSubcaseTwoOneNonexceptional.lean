import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoCaseTwoExclusions
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsProperEdgeColoring
import Tablet.NineN
import Tablet.TashkinovHierarchy
import Tablet.TashkinovStoredColorsCardinality
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: HierarchySituationTwoSubcaseTwoOneNonexceptional]
theorem HierarchySituationTwoSubcaseTwoOneNonexceptional {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx)
    (hnonexceptional :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ¬ ∃ eta, eta ∈ HierarchyStoredColorsAt H q ∧
        eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧
        D.theta ∈ C.good.gamma q eta) :
    False := by
-- BODY
  sorry
