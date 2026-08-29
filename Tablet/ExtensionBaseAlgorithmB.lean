import Tablet.AdjacentEdges
import Tablet.ETTStrongInterchangeable
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseAlgorithmBInvariant
import Tablet.ExtensionBaseAlgorithmBTrace
import Tablet.ExtensionBaseCaseOneIndices
import Tablet.ExtensionBaseSupportClassColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ExtensionBaseAlgorithmB]
theorem ExtensionBaseAlgorithmB {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (jSlot : Fin ett.rounds)
    (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (hproper : IsProperEdgeColoring G rho1)
    (hone : IsOneEdgeUncolored rho1 e0)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hinitialSI : ∀ a : Fin (p + 1), a.val < b.val →
      ETTStrongInterchangeable ett (indices a) terminalSupport rho1
        (gamma a) (delta a))
    (hTjInitial : ∀ a : Fin (p + 1), a.val < b.val →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (indices a).succ.castSucc))
    (hterminalNoMissing :
      MissingColors G rho1 terminalSupport ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    ∃ trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
        p indices b,
      ExtensionBaseAlgorithmBInvariant ett terminalSupport jSlot rho1 u
        p indices b trace := by
-- BODY
  sorry
