import Tablet.HkuMissingStoredMonotone
import Tablet.HkuTreeColorsControlled
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovStoredColors
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence

-- [TABLET NODE: ExtensionBaseClaimTreeEdgeColors]
theorem ExtensionBaseClaimTreeEdgeColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (rounds : ℕ) (series : TashkinovSeries G k rounds e0 input)
    (jSlot q : Fin rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = rounds)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (series.data.tree q.succ.castSucc)
      (TashkinovStoredColors series.data q.succ)
      (series.data.coloring q.succ) sigma) :
    (∀ f : E,
      f ∈ InternalEdges G
        (TreeSequenceVertexSet (series.data.tree jSlot.succ.castSucc)) →
      ∀ c : Fin k,
        series.data.coloring jSlot.castSucc f = some c →
        c ∈ TreeMissingColors (series.data.coloring jSlot.castSucc)
              (series.data.tree jSlot.succ.castSucc) ∪
            TashkinovStoredColors series.data jSlot.castSucc →
        sigma f = series.data.coloring jSlot.castSucc f) ∧
    ∀ a : Fin (series.data.tree jSlot.succ.castSucc).length,
      sigma ((series.data.tree jSlot.succ.castSucc).edge a) =
        series.data.coloring jSlot.castSucc
          ((series.data.tree jSlot.succ.castSucc).edge a) := by
-- BODY
  sorry
