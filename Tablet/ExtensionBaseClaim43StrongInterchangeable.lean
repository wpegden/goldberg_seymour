import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseSupportClass

-- [TABLET NODE: ExtensionBaseClaim43StrongInterchangeable]
theorem ExtensionBaseClaim43StrongInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace) :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport →
      s ≠ q →
      ett.series.data.chosenVertex s.succ = some terminalSupport →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport
        (trace.coloring (Fin.last trace.steps)) gammaS deltaS := by
-- BODY
  sorry
