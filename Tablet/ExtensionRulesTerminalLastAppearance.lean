import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HkuMissingStoredMonotone
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: ExtensionRulesTerminalLastAppearance]
theorem ExtensionRulesTerminalLastAppearance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (v : V)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex (Fin.last ett.rounds) = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T)
    (j : Fin (ett.rounds + 1))
    (hfirst : ETTFirstAppearanceIndex ett v hvFinal = j.val + 1)
    (hj : j.val + 1 = ett.rounds)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma) :
    StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧
      (0 < j.val →
        StableColoring (ett.series.data.tree j.castSucc)
          (TashkinovStoredColors ett.series.data j)
          (ett.series.data.coloring j) sigma) := by
-- BODY
  sorry
