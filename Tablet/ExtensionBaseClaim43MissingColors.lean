import Tablet.ExtensionBaseClaimMissingColors
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ExtensionBaseClaim43MissingColors]
theorem ExtensionBaseClaim43MissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN phiJ : PartialEdgeColoring E k)
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace)
    (hunsupported : ∀ v : V,
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ ≠ some v) →
      MissingColors G sigmaN v = MissingColors G phiJ v)
    (hclassPrepared : ∀ w : V,
      w ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      w ≠ terminalSupport →
      (∃ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport ∧
        ett.series.data.chosenVertex t.succ = some w) →
      ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
        ∃ gamma delta : Fin (p + 1) → Fin k,
          (∀ a b, a.val < b.val →
            (indices a).val < (indices b).val) ∧
          (∀ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport w ↔
              ∃ a : Fin (p + 1), indices a = r) ∧
          (∀ a, ett.series.data.gamma (indices a).succ = some (gamma a)) ∧
          (∀ a, ett.series.data.delta (indices a).succ = some (delta a)) ∧
          (∀ a : Fin p, gamma a.succ = delta a.castSucc) ∧
          Function.Injective (Fin.cons (gamma 0) delta) ∧
          MissingColors G phiJ w =
            (MissingColors G sigmaN w \ {delta (Fin.last p)}) ∪
              {gamma 0}) :
    (∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G phiJ v) ∧
    MissingColors G (trace.coloring (Fin.last trace.steps))
        terminalSupport =
      MissingColors G sigmaN terminalSupport := by
-- BODY
  sorry
