import Tablet.IncidentCore

-- [TABLET NODE: IncidentCoreEndpoints]
theorem IncidentCoreEndpoints {V E : Type*} (G : LooplessMultigraph V E)
    (e : E) :
    Sym2.map (fun x : IncidentVertex G => x.1) ((IncidentCore G).ends e) =
      G.ends e := by
-- BODY
  classical
  simp only [IncidentCore]
  exact (G.ends e).out_eq
