import Tablet.ExtensionBaseSupportClass
import Tablet.TashkinovExtensionKind
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ExtensionBaseAlgorithmCTrace]
structure ExtensionBaseAlgorithmCTrace {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (terminalSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V) where
-- BODY
  steps : ℕ
  slot : Fin steps → Fin ett.rounds
  gamma : Fin steps → Fin k
  delta : Fin steps → Fin k
  coloring : Fin (steps + 1) → PartialEdgeColoring E k
  initialColoring : coloring 0 = mu0
  terminalAtEnd : terminalSlot.val + 1 = ett.rounds
  terminalInClass : terminalSlot ∈
    ExtensionBaseSupportClass ett terminalSupport hterminalSupport
      terminalSupport
  enumerates : Finset.univ.image slot =
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
      terminalSupport).erase terminalSlot
  strictlyDescending : ∀ a b, a.val < b.val → (slot b).val < (slot a).val
  chosenSupport : ∀ a,
    ett.series.data.chosenVertex (slot a).succ = some terminalSupport
  extensionKind : ∀ a,
    ett.series.data.kind (slot a).succ = some TashkinovExtensionKind.PE
  gammaField : ∀ a,
    ett.series.data.gamma (slot a).succ = some (gamma a)
  deltaField : ∀ a,
    ett.series.data.delta (slot a).succ = some (delta a)
  transition : ∀ a,
    coloring a.succ = TwoColorComponentSwap G (coloring a.castSucc)
      (gamma a) (delta a) (Sum.inl u)
