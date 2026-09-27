import Tablet.ExtensionBaseAlgorithmBSingleStep
import Tablet.ExtensionBaseAlgorithmBTrace
import Tablet.ExtensionBaseCaseOneIndices
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ExtensionBaseAlgorithmBInduction]
theorem ExtensionBaseAlgorithmBInduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (hsteps : trace.steps = b.val)
    (hposition : ∀ a : Fin trace.steps,
      (trace.position a).val + a.val + 1 = b.val)
    (htraceGamma : ∀ a : Fin trace.steps,
      trace.gamma a = gamma (trace.position a))
    (htraceDelta : ∀ a : Fin trace.steps,
      trace.delta a = delta (trace.position a))
    (hproper : IsProperEdgeColoring G rho1)
    (hone : IsOneEdgeUncolored rho1 e0)
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hinitialSI : ∀ a : Fin (p + 1), a.val < b.val →
      ETTStrongInterchangeable ett (indices a) terminalSupport rho1
        (gamma a) (delta a))
    (hterminalNoMissing :
      MissingColors G rho1 terminalSupport ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    (∀ a : Fin (trace.steps + 1),
      IsProperEdgeColoring G (trace.coloring a) ∧
        IsOneEdgeUncolored (trace.coloring a) e0) ∧
    (∀ a : Fin trace.steps,
      trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) u ∧
        trace.gamma a ∈ PresentColors G (trace.coloring a.castSucc) u ∧
        trace.gamma a ∈
          PresentColors G (trace.coloring a.castSucc) terminalSupport ∧
        trace.delta a ∈
          PresentColors G (trace.coloring a.castSucc) terminalSupport ∧
        ETTStrongInterchangeable ett (trace.slot a) terminalSupport
          (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) ∧
        ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ ExtensionBaseCaseOneIndices ett p indices b →
          (∀ c : Fin trace.steps, c.val ≤ a.val → trace.slot c ≠ s) →
          ett.series.data.chosenVertex s.succ = some terminalSupport →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s terminalSupport
            (trace.coloring a.succ) gammaS deltaS) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ ExtensionBaseCaseOneIndices ett p indices b →
      (∀ a : Fin trace.steps, trace.slot a ≠ s) →
      ett.series.data.chosenVertex s.succ = some terminalSupport →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport
        (trace.coloring (Fin.last trace.steps)) gammaS deltaS := by
-- BODY
  sorry
