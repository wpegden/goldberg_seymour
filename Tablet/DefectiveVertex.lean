import Tablet.DefectiveEdge
import Tablet.Incident

-- [TABLET NODE: DefectiveVertex]
def DefectiveVertex {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (X : Finset V) (v : V) : Prop :=
-- BODY
  v ∈ X ∧ ∃ f : E, DefectiveEdge G phi X f ∧ Incident G v f
