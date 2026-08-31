import Tablet.ColoredVertexSetElementary
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: ParallelCommonMissingClosed]
theorem ParallelCommonMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (hphi : phi = ett.series.data.coloring (Fin.last ett.rounds))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hlowerElementary :
      let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
      ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc))) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    TreeColorSetClosed G phi base.core
      (TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) := by
-- BODY
  sorry
