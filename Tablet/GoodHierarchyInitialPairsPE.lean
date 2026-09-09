import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.TashkinovExtensionKind
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: GoodHierarchyInitialPairsPE]
theorem GoodHierarchyInitialPairsPE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hnotClosed : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi base.core ∧
        ¬ TreeColorSetClosed G phi base.core {alpha})
    (hcommonClosed : TreeColorSetClosed G phi base.core
      (TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure))
    (hcommonFour : 4 ≤
      (TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure).card) :
    ∃ gamma : Fin k → Finset (Fin k),
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt H 0 →
        (gamma eta).card = 2 ∧
          gamma eta ⊆ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) ∧
      (∀ eta theta : Fin k,
        eta ∈ HierarchyStoredColorsAt H 0 →
        theta ∈ HierarchyStoredColorsAt H 0 → eta ≠ theta →
        Disjoint (gamma eta) (gamma theta)) ∧
      ¬ TreeColorSetMinusClosed G phi base.core
        ((HierarchyStoredColorsAt H 0).biUnion gamma) ∧
      4 ≤ ((TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure) \
          (HierarchyStoredColorsAt H 0).biUnion gamma).card := by
-- BODY
  sorry
