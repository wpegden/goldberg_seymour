import Tablet.NormalGlobalMaximumTriple
import Tablet.TreeSequencePrefix

-- [TABLET NODE: NormalTripleTrunk]
noncomputable def NormalTripleTrunk {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
    (N : NormalGlobalMaximumTriple G k e0 phi T) : TreeSequence G e0 := by
-- BODY
  exact TreeSequencePrefix T (N.height - 1)
    (by have h := N.height_lower; omega)
    (by have h := N.height_upper; omega)
