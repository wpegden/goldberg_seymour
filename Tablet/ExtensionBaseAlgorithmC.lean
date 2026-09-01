import Tablet.AdjacentEdges
import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseAlgorithmCInvariant
import Tablet.ExtensionBaseAlgorithmCTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TashkinovExtensionKind
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
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: ExtensionBaseAlgorithmC]
theorem ExtensionBaseAlgorithmC {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (terminalSlot jSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k)
    (hproper : IsProperEdgeColoring G mu0)
    (hone : IsOneEdgeUncolored mu0 e0)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ s : Fin ett.rounds,
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = s)
    (hterminalIndex : indices (Fin.last p) = terminalSlot)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hTjInitial : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
        TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree s.succ.castSucc))
    (hterminalGammaMissing :
      gamma (Fin.last p) ∈ MissingColors G mu0 u)
    (hinitialGammaPresent : ∀ a : Fin p,
      gamma a.castSucc ∈ PresentColors G mu0 u)
    (hinitialSI : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS)
    (hterminalNoMissing :
      MissingColors G mu0 terminalSupport ∩
        ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot).biUnion
            (fun s => ett.series.data.stored s.succ) = ∅) :
    ∃ trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
        hterminalSupport terminalSlot mu0 u,
      ExtensionBaseAlgorithmCInvariant ett terminalSupport
        hterminalSupport terminalSlot jSlot mu0 u trace := by
-- BODY
  sorry
