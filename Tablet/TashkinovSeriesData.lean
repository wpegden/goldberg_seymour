import Tablet.PartialEdgeColoring
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequence

-- [TABLET NODE: TashkinovSeriesData]
structure TashkinovSeriesData {V E : Type*} (G : LooplessMultigraph V E)
    (k rounds : ℕ) (e0 : E) where
-- BODY
  tree : Fin (rounds + 2) → TreeSequence G e0
  coloring : Fin (rounds + 1) → PartialEdgeColoring E k
  stored : Fin (rounds + 1) → Finset (Fin k)
  connectingEdges : Fin (rounds + 1) → Finset E
  kind : Fin (rounds + 1) → Option TashkinovExtensionKind
  chosenVertex : Fin (rounds + 1) → Option V
  outsideVertex : Fin (rounds + 1) → Option V
  delta : Fin (rounds + 1) → Option (Fin k)
  gamma : Fin (rounds + 1) → Option (Fin k)
