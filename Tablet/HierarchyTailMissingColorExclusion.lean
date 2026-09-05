import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.ColoredVertexSetClosed
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyStarredStage
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors
import Tablet.TreeIncidentEdge
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: HierarchyTailMissingColorExclusion]
theorem HierarchyTailMissingColorExclusion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hpenultimate :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := fun i : ℕ =>
        TreeSequencePrefix T (min (A.length + i) T.length)
          (by have hA := A.positive; have hT := T.positive; omega)
          (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (Ty (ell - 1)))) :
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := T.length - A.length
    let Ty := fun i : ℕ =>
      TreeSequencePrefix T (min (A.length + i) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ∀ i : ℕ, 1 ≤ i → i < ell →
      ∀ beta : Fin k,
        beta ∈ MissingColors G phi
          ((Ty i).vertex (Fin.last (Ty i).length)) →
        ∀ t : Fin (Ty i).length,
          A.length ≤ t.val → t.val < A.length + i →
          phi ((Ty i).edge t) = some beta →
          H.dividerCount = 0 ∧ base.core = Tn ∧
            t.val = A.length ∧
            ∃ f : E,
              TashkinovSeriesStep G k ett.rounds e0 input
                  ett.series.data n ∧
                (ett.series.data.kind n =
                    some TashkinovExtensionKind.SE ∨
                  ett.series.data.kind n =
                    some TashkinovExtensionKind.RE) ∧
                ett.series.data.connectingEdges n = {f} ∧
                (Ty i).edge t = f ∧ phi f = some beta ∧
                beta ∈ TashkinovStoredColors ett.series.data n := by
-- BODY
  sorry
