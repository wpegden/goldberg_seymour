import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence

-- [TABLET NODE: AlgorithmFiveFiveParallelStrictGrowth]
theorem AlgorithmFiveFiveParallelStrictGrowth {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
    (baseJ : HierarchyBase corrJ.replacementETT phi)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (hzero : KJ.dividerCount = 0)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hJcore : J = baseJ.core)
    (m : ℕ) (U : TreeSequence G e0)
    (hUlength : U.length = J.length + m)
    (hzeroEndpoint : m = 0 → U = J)
    (hmaximal : ∀ W : TreeSequence G e0,
      TashkinovAugmentation phi U W →
      (∀ eta : Fin k,
        eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
        Disjoint (goodJ.gamma (Fin.last KJ.dividerCount) eta)
          (Finset.univ.filter fun c =>
            ∃ r : Fin W.length,
              (HierarchyStarredStage KJ
                (Fin.last KJ.dividerCount)).length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi W eta).val
                W.length ∧
              phi (W.edge r) = some c)) →
      False) :
    J.length < U.length := by
-- BODY
  sorry
