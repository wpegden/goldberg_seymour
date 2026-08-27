import Tablet.TreeExitPath

-- [TABLET NODE: TreeExit]
def TreeExit {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (v : V) : Prop :=
-- BODY
  ∃ (u : V)
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
    TreeExitPath T phi alpha beta u v p
