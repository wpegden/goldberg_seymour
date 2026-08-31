import Tablet.Critical
import Tablet.IncidentCoreChromaticIndex

-- [TABLET NODE: IncidentCoreCritical]
theorem IncidentCoreCritical {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    Critical (IncidentCore G) ↔ Critical G := by
-- BODY
  constructor
  · intro hcore e
    change ChromaticIndex (RestrictEdges G (Finset.univ.erase e)) <
      ChromaticIndex G
    rw [← (IncidentCoreChromaticIndex G).2 (Finset.univ.erase e),
      ← (IncidentCoreChromaticIndex G).1]
    exact hcore e
  · intro horiginal e
    change ChromaticIndex (RestrictEdges (IncidentCore G) (Finset.univ.erase e)) <
      ChromaticIndex (IncidentCore G)
    rw [(IncidentCoreChromaticIndex G).2 (Finset.univ.erase e),
      (IncidentCoreChromaticIndex G).1]
    exact horiginal e
