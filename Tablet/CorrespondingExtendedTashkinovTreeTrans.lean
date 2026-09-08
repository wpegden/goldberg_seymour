import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: CorrespondingExtendedTashkinovTreeTrans]
lemma CorrespondingExtendedTashkinovTreeTrans
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma tau : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (second : CorrespondingExtendedTashkinovTree
      G k e0 first.replacementETT tau T) :
    exists composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T,
      composite.replacementInput = second.replacementInput /\
        HEq composite.replacementSeries second.replacementSeries /\
        HEq composite.replacementETT second.replacementETT := by
-- BODY
  sorry
