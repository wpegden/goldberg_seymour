import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TashkinovClosure
import Tablet.TashkinovOrder
import Tablet.TashkinovStoredColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: MaximumProperty]
def MaximumProperty {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) : Prop :=
-- BODY
  let T1 : TreeSequence G e0 := ett.series.data.tree ⟨1, by omega⟩
  (TreeSequenceVertexSet T1).card = TashkinovOrder G ∧
    ∀ (i : ℕ) (hi : 1 ≤ i) (hbeforeLast : i < ett.rounds),
      let idx : Fin (ett.rounds + 1) := ⟨i, by omega⟩
      let nextIdx : Fin (ett.rounds + 2) := ⟨i + 1, by omega⟩
      let Ti : TreeSequence G e0 := ett.series.data.tree idx.castSucc
      ∀ (pi : PartialEdgeColoring E k) (seed candidate : TreeSequence G e0),
        IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring Ti (TashkinovStoredColors ett.series.data idx)
          (ett.series.data.coloring idx) pi →
        ((ett.series.data.kind idx = some TashkinovExtensionKind.PE ∧
            seed = Ti) ∨
          ((ett.series.data.kind idx = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind idx = some TashkinovExtensionKind.RE) ∧
            ∃ f : E, ett.series.data.connectingEdges idx = {f} ∧
              TreeSequenceAdjoinEdge Ti f seed)) →
        TashkinovClosure pi seed candidate →
        (TreeSequenceVertexSet candidate).card ≤
          (TreeSequenceVertexSet (ett.series.data.tree nextIdx)).card
