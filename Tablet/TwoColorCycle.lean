import Mathlib.Combinatorics.SimpleGraph.Paths
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorCycle]
structure TwoColorCycle {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) where
-- BODY
  base : Sum V E
  walk : (TwoColorIncidenceGraph G phi alpha beta).Walk base base
  isCycle : walk.IsCycle
