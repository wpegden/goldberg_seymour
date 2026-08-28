import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseActiveIndices
import Tablet.HkuMissingStoredMonotone
import Tablet.ParallelExtensionColor
import Tablet.RevisitingExtensionCertificate
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeExit
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.sc2

-- [TABLET NODE: ExtensionBaseClaimStrongInterchangeable]
theorem ExtensionBaseClaimStrongInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hLowerInterchange : ∀ (t : Fin ett.rounds) (vt : V)
      (gamma delta : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gamma →
      ett.series.data.delta t.succ = some delta →
      TreeInterchangeable G (ett.series.data.tree t.succ.succ)
        (ett.series.data.coloring t.succ) gamma delta)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma) :
    ∀ (t : Fin ett.rounds) (vt : V) (gamma delta : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gamma →
      ett.series.data.delta t.succ = some delta →
      ETTStrongInterchangeable ett t vt sigma gamma delta := by
-- BODY
  sorry
