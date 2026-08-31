import Tablet.CombinedStableColoring
import Tablet.HierarchyBase
import Tablet.OutsideKempeRecoloringStable
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovStoredColors
import Tablet.TashkinovHierarchy

-- [TABLET NODE: HierarchyOutsideKempeStable]
theorem HierarchyOutsideKempeStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring T Dn phi sigma ∧ TreeColoringInvariant T phi sigma ∧
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
      CombinedStableColoring Tn base.closure Dn phi sigma) := by
-- BODY
  sorry
