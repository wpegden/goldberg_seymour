import Tablet.ExtensionBaseCaseOneIndices
import Tablet.ExtensionBaseSupportClass
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ExtensionBaseAlgorithmBTrace]
structure ExtensionBaseAlgorithmBTrace {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (b : Fin (p + 1)) where
-- BODY
  steps : ℕ
  position : Fin steps → Fin (p + 1)
  slot : Fin steps → Fin ett.rounds
  gamma : Fin steps → Fin k
  delta : Fin steps → Fin k
  coloring : Fin (steps + 1) → PartialEdgeColoring E k
  initialColoring : coloring 0 = rho1
  positionBefore : ∀ a, (position a).val < b.val
  slotIdentity : ∀ a, slot a = indices (position a)
  enumerates : Finset.univ.image slot =
    ExtensionBaseCaseOneIndices ett p indices b
  strictlyDescending : ∀ a c, a.val < c.val → (slot c).val < (slot a).val
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
