import Tablet.IncidentCoreColoringTransport
import Tablet.IncidentCoreCritical
import Tablet.IncidentCoreMaximumDegree
import Tablet.KTriple

-- [TABLET NODE: IncidentCoreKTriple]
theorem IncidentCoreKTriple {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) :
    KTriple (IncidentCore G) k e0 phi ↔ KTriple G k e0 phi := by
-- BODY
  constructor
  · rintro ⟨hcrit, hchi, hdegree, hproper, huncolored⟩
    exact ⟨(IncidentCoreCritical G).1 hcrit,
      (IncidentCoreChromaticIndex G).1 ▸ hchi,
      (IncidentCoreMaximumDegree G) ▸ hdegree,
      (IncidentCoreColoringTransport G).2.1 k phi |>.1 hproper,
      huncolored⟩
  · rintro ⟨hcrit, hchi, hdegree, hproper, huncolored⟩
    exact ⟨(IncidentCoreCritical G).2 hcrit,
      (IncidentCoreChromaticIndex G).1.symm ▸ hchi,
      (IncidentCoreMaximumDegree G).symm ▸ hdegree,
      (IncidentCoreColoringTransport G).2.1 k phi |>.2 hproper,
      huncolored⟩
