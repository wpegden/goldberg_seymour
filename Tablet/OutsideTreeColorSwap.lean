import Tablet.TreeIncidentEdge
import Tablet.PartialEdgeColoring

-- [TABLET NODE: OutsideTreeColorSwap]
noncomputable def OutsideTreeColorSwap {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) : PartialEdgeColoring E k := by
-- BODY
  classical
  exact fun e =>
    if TreeIncidentEdge T e then phi e
    else if phi e = some alpha then some beta
    else if phi e = some beta then some alpha
    else phi e
