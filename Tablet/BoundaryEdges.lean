import Tablet.Incident

open scoped Sym2

-- [TABLET NODE: BoundaryEdges]
noncomputable def BoundaryEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset V) : Finset E := by
-- BODY
  classical
  exact Finset.univ.filter fun e => ∃ u ∈ U, ∃ v ∉ U, G.ends e = s(u, v)
