import Tablet.ExtensionBaseRestorationIndices
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ExtensionBaseRestorationTrace]
structure ExtensionBaseRestorationTrace {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (sigmaN : PartialEdgeColoring E k) where
-- BODY
  steps : ℕ
  slot : Fin steps → Fin ett.rounds
  support : Fin steps → V
  gamma : Fin steps → Fin k
  delta : Fin steps → Fin k
  coloring : Fin (steps + 1) → PartialEdgeColoring E k
  initialColoring : coloring 0 = sigmaN
  enumerates : Finset.univ.image slot =
    ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
  strictlyDescending : ∀ a b, a.val < b.val → (slot b).val < (slot a).val
  chosenVertex : ∀ a,
    ett.series.data.chosenVertex (slot a).succ = some (support a)
  gammaField : ∀ a, ett.series.data.gamma (slot a).succ = some (gamma a)
  deltaField : ∀ a, ett.series.data.delta (slot a).succ = some (delta a)
  transition : ∀ a,
    coloring a.succ = TwoColorComponentSwap G (coloring a.castSucc)
      (gamma a) (delta a) (Sum.inl (support a))
