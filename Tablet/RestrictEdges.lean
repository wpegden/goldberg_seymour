import Tablet.LooplessMultigraph

-- [TABLET NODE: RestrictEdges]
noncomputable def RestrictEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) : LooplessMultigraph V {e // e ∈ F} := by
-- BODY
  classical
  exact { ends := fun e => G.ends e.1
          loopless := fun e v => G.loopless e.1 v }
