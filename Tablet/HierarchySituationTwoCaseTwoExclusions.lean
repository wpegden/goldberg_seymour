import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchyStarredStage
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchySituationTwoCaseTwoExclusions]
theorem HierarchySituationTwoCaseTwoExclusions {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx) :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let ell := HierarchyFullTailLength C
    let B := HierarchyFullTailPrefix C (ell - 2)
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    D.alpha ∉ TreeMissingColors phi B ∧
      D.alpha ∉ TashkinovStoredColors ett.series.data n ∧
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some D.alpha := by
-- BODY
  sorry
