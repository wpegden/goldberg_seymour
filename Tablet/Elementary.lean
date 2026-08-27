import Tablet.ChromaticIndex
import Tablet.DensityCeil

-- [TABLET NODE: Elementary]
def Elementary {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : Prop :=
-- BODY
  ChromaticIndex G = DensityCeil G
