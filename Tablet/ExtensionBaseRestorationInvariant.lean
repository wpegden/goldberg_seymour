import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseRestorationTrace
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ExtensionBaseRestorationInvariant]
def ExtensionBaseRestorationInvariant {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN) : Prop :=
-- BODY
  (∀ a : Fin (trace.steps + 1),
      IsProperEdgeColoring G (trace.coloring a) ∧
        IsOneEdgeUncolored (trace.coloring a) e0) ∧
    (∀ a : Fin trace.steps,
      trace.slot a ∈
          ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport ∧
        TreeVertexOrder T terminalSupport (trace.support a) ∧
        TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
        trace.support a ∈ TreeSequenceVertexSet
          (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
        trace.delta a ∈
          MissingColors G (trace.coloring a.castSucc) (trace.support a) ∧
        TwoColorPathComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl (trace.support a)) ∧
        (∀ w : V,
          w ∈ TreeSequenceVertexSet
              (ett.series.data.tree (trace.slot a).succ.castSucc) →
          (Sum.inl w ∈ TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a)
              (Sum.inl (trace.support a)) ↔ w = trace.support a)) ∧
        ∀ (s : Fin ett.rounds) (vs : V) (gammaS deltaS : Fin k),
          s ∈ ExtensionBaseActiveIndices ett terminalSupport
              hterminalSupport →
          s ≠ q →
          (∀ b : Fin trace.steps, b.val ≤ a.val → trace.slot b ≠ s) →
          ett.series.data.chosenVertex s.succ = some vs →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s vs (trace.coloring a.succ)
            gammaS deltaS) ∧
    ∀ (s : Fin ett.rounds) (vs : V) (gammaS deltaS : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      s ≠ q →
      (∀ a : Fin trace.steps, trace.slot a ≠ s) →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s vs
        (trace.coloring (Fin.last trace.steps)) gammaS deltaS
