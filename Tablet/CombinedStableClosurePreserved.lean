import Tablet.CombinedStableColoring
import Tablet.HierarchyBase
import Tablet.HkuTreeColorsControlled
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeSequencePrefix
import Tablet.sc2

-- [TABLET NODE: CombinedStableClosurePreserved]
theorem CombinedStableClosurePreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (hphi : phi = ett.series.data.coloring (Fin.last ett.rounds))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperSigma : IsProperEdgeColoring G sigma)
    (honeSigma : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    let seed := TreeSequencePrefix Tn base.supportPosition.val
      base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
    (∀ j : Fin Tn.length, sigma (Tn.edge j) = phi (Tn.edge j)) ∧
    (∀ j : Fin base.closure.length,
      sigma (base.closure.edge j) = phi (base.closure.edge j)) ∧
    TashkinovClosure sigma seed base.closure := by
-- BODY
  sorry
