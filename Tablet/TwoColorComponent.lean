import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponent]
def TwoColorComponent {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E) :
    Set (Sum V E) :=
-- BODY
  (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z
