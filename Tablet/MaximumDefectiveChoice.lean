import Tablet.BoundaryEdges
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TreeVertexOrder

open scoped Sym2

-- [TABLET NODE: MaximumDefectiveChoice]
structure MaximumDefectiveChoice {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) where
-- BODY
  selected : PartialEdgeColoring E k
  selectedProper : IsProperEdgeColoring G selected
  selectedOneUncolored : IsOneEdgeUncolored selected e0
  selectedStable : StableColoring T C phi selected
  vertex : V
  vertexDefective :
    DefectiveVertex G selected (TreeSequenceVertexSet T) vertex
  maximal : ∀ (pi : PartialEdgeColoring E k) (w : V),
    IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
      StableColoring T C phi pi →
      DefectiveVertex G pi (TreeSequenceVertexSet T) w →
      w = vertex ∨ TreeVertexOrder T w vertex
  edge : E
  edgeDefective : DefectiveEdge G selected (TreeSequenceVertexSet T) edge
  edgeIncident : Incident G vertex edge
  otherEndpoint : V
  otherOutside : otherEndpoint ∉ TreeSequenceVertexSet T
  edgeEnds : G.ends edge = s(vertex, otherEndpoint)
  color : Fin k
  edgeColor : selected edge = some color
