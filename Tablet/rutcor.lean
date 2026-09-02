import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.GoodHierarchyNewMissingClosed
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStoredColorsAntitone
import Tablet.MaximumDefectiveChoice
import Tablet.OrderedTreeUnion
import Tablet.ParallelCommonMissingClosed
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeColorSetClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeSequenceEdgeSet
import Tablet.TreeSequencePrefix
import Tablet.sc2

-- [TABLET NODE: rutcor]
theorem rutcor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hq : 0 < H.dividerCount)
    (hprefixElementary :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hpreStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by
        have hp := ett.roundsPositive
        omega⟩
      let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn))
    (alpha : Fin k)
    (halpha : alpha ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount))) :
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    let Tnq := HierarchyStarredStage H q
    ((∃ i : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H i) {alpha}) →
      ∀ r : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {alpha} →
        (∀ s : Fin (H.dividerCount + 1), r.val < s.val →
          ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha}) →
        alpha ∉ (Finset.univ.filter fun c =>
          ∃ t : Fin Tnq.length,
            (HierarchyStarredStage H r).length ≤ t.val ∧
              phi (Tnq.edge t) = some c)) ∧
    ((∀ i : Fin (H.dividerCount + 1),
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H i) {alpha}) →
      (∀ j : Fin H.dividerCount,
        alpha ∈ (HierarchyStoredColorsAt H j.succ).biUnion
            (good.gamma j.castSucc) ∧
          alpha ∈ (HierarchyStoredColorsAt H j.castSucc).biUnion
            (good.gamma j.castSucc)) ∧
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE ∧
      T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
        TreeSequenceVertexSet Tn \ TreeSequenceVertexSet base.closure ∧
      alpha ∉ (Finset.univ.filter fun c =>
        ∃ t : Fin Tnq.length,
          Tn.length ≤ t.val ∧ phi (Tnq.edge t) = some c)) := by
-- BODY
  sorry
