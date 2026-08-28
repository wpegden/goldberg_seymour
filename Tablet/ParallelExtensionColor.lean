import Tablet.MissingColors
import Tablet.TashkinovSeriesData

-- [TABLET NODE: ParallelExtensionColor]
def ParallelExtensionColor {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (rounds + 1)) (selected : PartialEdgeColoring E k)
    (v : V) (gamma : Fin k) : Prop :=
-- BODY
  gamma ∈ MissingColors G selected v ∧
    ((∃ h : Fin (rounds + 1),
        0 < h.val ∧ h.val ≤ i.val ∧
        data.kind h = some TashkinovExtensionKind.PE ∧
        data.chosenVertex h = some v ∧ data.delta h = some gamma ∧
        ∀ j : Fin (rounds + 1),
          0 < j.val → j.val ≤ i.val →
          data.kind j = some TashkinovExtensionKind.PE →
          data.chosenVertex j = some v → j.val ≤ h.val) ∨
      (∀ h : Fin (rounds + 1),
        0 < h.val → h.val ≤ i.val →
        data.kind h = some TashkinovExtensionKind.PE →
        data.chosenVertex h ≠ some v))
