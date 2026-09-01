import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseAlgorithmCTrace
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: ExtensionBaseAlgorithmCInvariant]
def ExtensionBaseAlgorithmCInvariant {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (terminalSlot jSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V)
    (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
      hterminalSupport terminalSlot mu0 u) : Prop :=
-- BODY
  (∀ a : Fin (trace.steps + 1),
      IsProperEdgeColoring G (trace.coloring a) ∧
        IsOneEdgeUncolored (trace.coloring a) e0) ∧
    (∀ a : Fin trace.steps,
      TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
        trace.delta a ∈
          MissingColors G (trace.coloring a.castSucc) u ∧
        TwoColorNontrivialPathComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u) ∧
        (∀ w : V,
          w ∈ TreeSequenceVertexSet
              (ett.series.data.tree (trace.slot a).succ.castSucc) →
          Sum.inl w ∈ TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u) →
          w = terminalSupport) ∧
        (Sum.inl terminalSupport ∈
            TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u) →
          ¬ Set.Subsingleton
            ((TwoColorIncidenceGraph G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a)).neighborSet
                (Sum.inl terminalSupport))) ∧
        ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett terminalSupport
              hterminalSupport terminalSupport).erase terminalSlot →
          (∀ b : Fin trace.steps, b.val ≤ a.val → trace.slot b ≠ s) →
          ett.series.data.chosenVertex s.succ = some terminalSupport →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s terminalSupport
            (trace.coloring a.succ) gammaS deltaS) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      (∀ a : Fin trace.steps, trace.slot a ≠ s) →
      ett.series.data.chosenVertex s.succ = some terminalSupport →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport
        (trace.coloring (Fin.last trace.steps)) gammaS deltaS
