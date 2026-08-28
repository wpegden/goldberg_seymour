import Tablet.ScheideStructuralConfiguration

-- [TABLET NODE: ScheideReducedConfiguration]
structure ScheideReducedConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    extends ScheideStructuralConfiguration G k e0 phi T where
-- BODY
  exit_card_eq : (ScheideExitVertices T phi).card = s
  exit_exactly_one : ∀ v ∈ ScheideExitVertices T phi,
    ∃! i : Fin s, gamma i ∈ MissingColors G phi v
  every_block_color_at_exit : ∀ i : Fin s,
    ∃ v ∈ ScheideExitVertices T phi, gamma i ∈ MissingColors G phi v
