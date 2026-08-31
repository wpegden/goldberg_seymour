import Tablet.ExtendedTashkinovTree
import Tablet.OrderedTreeUnion
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TreeMissingColors
import Tablet.TreeSequencePrefix

-- [TABLET NODE: HierarchyBase]
structure HierarchyBase {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (phi : PartialEdgeColoring E k) where
-- BODY
  core : TreeSequence G e0
  closure : TreeSequence G e0
  supportPosition : Fin
    ((ett.series.data.tree (Fin.last ett.rounds).castSucc).length + 1)
  supportPositive : 1 ≤ supportPosition.val
  terminalMissingColors :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    TreeMissingColors phi Tn = TreeMissingColors generating Tn
  parallel :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex n = some (Tn.vertex supportPosition) ∧
      TashkinovClosure phi
        (TreeSequencePrefix Tn supportPosition.val supportPositive
          (Nat.le_of_lt_succ supportPosition.isLt)) closure ∧
      Nonempty (OrderedTreeUnion Tn closure core)
  nonparallel :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ett.series.data.kind n ≠ some TashkinovExtensionKind.PE → core = Tn
