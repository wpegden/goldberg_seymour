import Tablet.CombinedStableColoring
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovExtensionKind
import Tablet.TreeColoringInvariant

-- [TABLET NODE: HierarchyWeaklyStable]
def HierarchyWeaklyStable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) (sigma : PartialEdgeColoring E k) : Prop :=
-- BODY
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let baseStable :=
    if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma
    else StableColoring Tn Dn phi sigma
  Fin.cases baseStable
    (fun i : Fin H.dividerCount =>
      baseStable ∧ TreeColoringInvariant (H.stage i.succ.castSucc) phi sigma) j
