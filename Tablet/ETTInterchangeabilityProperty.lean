import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors

-- [TABLET NODE: ETTInterchangeabilityProperty]
def ETTInterchangeabilityProperty {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) : Prop :=
-- BODY
  T = ett.series.data.tree (Fin.last (ett.rounds + 1)) ∧
    ∀ sigmaN : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigmaN → IsOneEdgeUncolored sigmaN e0 →
      StableColoring T
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        (ett.series.data.coloring (Fin.last ett.rounds)) sigmaN →
      ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigmaN T ∨
          beta ∈ TreeMissingColors sigmaN T) →
        TreeInterchangeable G T sigmaN alpha beta
