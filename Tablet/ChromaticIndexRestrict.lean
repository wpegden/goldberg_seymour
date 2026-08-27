import Tablet.ChromaticIndexSpec
import Tablet.ProperColoringRestricts

-- [TABLET NODE: ChromaticIndexRestrict]
theorem ChromaticIndexRestrict {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    ChromaticIndex (RestrictEdges G F) ≤ ChromaticIndex G := by
-- BODY
  classical
  obtain ⟨φ, hproper, hfull⟩ := (ChromaticIndexSpec G).1
  apply (ChromaticIndexSpec (RestrictEdges G F)).2 (ChromaticIndex G)
  refine ⟨(fun e => φ e.1), ProperColoringRestricts G F φ hproper, ?_⟩
  intro e
  exact hfull e.1
