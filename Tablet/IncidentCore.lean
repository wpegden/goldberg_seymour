import Tablet.IncidentVertex

open scoped Sym2

-- [TABLET NODE: IncidentCore]
noncomputable def IncidentCore {V E : Type*} (G : LooplessMultigraph V E) :
    LooplessMultigraph (IncidentVertex G) E := by
-- BODY
  classical
  let coreEnds : E → Sym2 (IncidentVertex G) := fun e =>
    s(⟨(G.ends e).out.1, e, Sym2.out_fst_mem (G.ends e)⟩,
      ⟨(G.ends e).out.2, e, Sym2.out_snd_mem (G.ends e)⟩)
  refine ⟨coreEnds, ?_⟩
  intro e v hloop
  apply G.loopless e v.1
  have hmapped := congrArg (Sym2.map (fun x : IncidentVertex G => x.1)) hloop
  have hout : Sym2.map (fun x : IncidentVertex G => x.1) (coreEnds e) = G.ends e := by
    simp only [coreEnds]
    exact (G.ends e).out_eq
  rw [hout] at hmapped
  exact hmapped
