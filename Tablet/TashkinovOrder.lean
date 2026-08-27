import Tablet.ChromaticIndex
import Tablet.KTriple
import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashkinovOrder]
noncomputable def TashkinovOrder {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  let k := ChromaticIndex G - 1
  let orders := (Finset.range (Fintype.card V + 1)).filter fun n =>
    ∃ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0),
      KTriple G k e0 phi ∧ TashkinovTree G e0 phi T ∧
        (TreeSequenceVertexSet T).card = n
  exact (insert 0 orders).max' (by simp)
