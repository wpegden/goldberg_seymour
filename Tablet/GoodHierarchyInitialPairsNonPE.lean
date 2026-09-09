import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.TashkinovExtensionKind
import Tablet.TreeMissingColors

-- [TABLET NODE: GoodHierarchyInitialPairsNonPE]
theorem GoodHierarchyInitialPairsNonPE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card) :
    ∃ gamma : Fin k → Finset (Fin k),
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt H 0 →
        (gamma eta).card = 2 ∧
          gamma eta ⊆ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) ∧
      ∀ eta theta : Fin k,
        eta ∈ HierarchyStoredColorsAt H 0 →
        theta ∈ HierarchyStoredColorsAt H 0 → eta ≠ theta →
        Disjoint (gamma eta) (gamma theta) := by
-- BODY
  sorry
