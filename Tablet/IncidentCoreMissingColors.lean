import Tablet.IncidentCoreIncidence
import Tablet.IncidentVertexFintype
import Tablet.MissingColors

-- [TABLET NODE: IncidentCoreMissingColors]
theorem IncidentCoreMissingColors {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (phi : PartialEdgeColoring E k)
    (x : IncidentVertex G) :
    PresentColors (IncidentCore G) phi x = PresentColors G phi x.1 ∧
      MissingColors (IncidentCore G) phi x = MissingColors G phi x.1 := by
-- BODY
  classical
  have hp : PresentColors (IncidentCore G) phi x = PresentColors G phi x.1 := by
    unfold PresentColors
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, he, hc⟩
      exact ⟨e, (IncidentCoreIncidence G x e).1 he, hc⟩
    · rintro ⟨e, he, hc⟩
      exact ⟨e, (IncidentCoreIncidence G x e).2 he, hc⟩
  refine ⟨hp, ?_⟩
  unfold MissingColors
  rw [hp]
