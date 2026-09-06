import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyPathNumber
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoReorderedTreesCertified
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.SameGoodHierarchy
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: HierarchySituationTwoSubcaseOneOneNonexceptional]
theorem HierarchySituationTwoSubcaseOneOneNonexceptional {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneData
      G k e0 input T phi ett base C ctx)
    (hnonexceptional :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      D.theta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∨
        ∃ eta, eta ∈ HierarchyStoredColorsAt H q ∧
          D.theta ∈ C.good.gamma q eta ∧
          eta ∉ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
    False := by
-- BODY
  sorry
