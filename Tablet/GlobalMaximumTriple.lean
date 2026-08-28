import Tablet.KTriple
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GlobalMaximumTriple]
def GlobalMaximumTriple {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
-- BODY
  KTriple G k e0 phi ∧ TashkinovTree G e0 phi T ∧
    (TreeSequenceVertexSet T).card = TashkinovOrder G
