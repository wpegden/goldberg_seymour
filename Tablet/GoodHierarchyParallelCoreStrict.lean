import Tablet.GoodHierarchy
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: GoodHierarchyParallelCoreStrict]
theorem GoodHierarchyParallelCoreStrict {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hclosed : TreeColorSetClosed G phi T (TreeMissingColors phi T)) :
    H.stage ⟨1, by omega⟩ ≠ base.core := by
-- BODY
  sorry
