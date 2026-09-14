import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreeBadPair]
def TashTreeBadPair {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
-- BODY
  KTriple G k e0 phi ∧ TashkinovTree G e0 phi T ∧
    ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)
