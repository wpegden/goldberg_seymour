import Tablet.NormalGlobalMaximumTriple

-- [TABLET NODE: NormalCycleEdge]
noncomputable def NormalCycleEdge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
    (N : NormalGlobalMaximumTriple G k e0 phi T) (i : Fin N.height) : E := by
-- BODY
  classical
  if hzero : i.val = 0 then
    exact e0
  else if hlast : i.val + 1 = N.height then
    exact N.closingEdge
  else
    exact T.edge ⟨i.val, by
      have hi := i.isLt
      have hu := N.height_upper
      omega⟩
