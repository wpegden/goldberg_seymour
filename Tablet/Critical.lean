import Tablet.ChromaticIndex
import Tablet.DeleteEdge

-- [TABLET NODE: Critical]
def Critical {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) : Prop :=
-- BODY
  ∀ e : E, ChromaticIndex (DeleteEdge G e) < ChromaticIndex G
