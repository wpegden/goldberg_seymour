import Tablet.ChromaticIndexSpec
import Tablet.IncidentCoreColoringTransport

-- [TABLET NODE: IncidentCoreChromaticIndex]
theorem IncidentCoreChromaticIndex {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex (IncidentCore G) = ChromaticIndex G ∧
      ∀ F : Finset E,
        ChromaticIndex (RestrictEdges (IncidentCore G) F) =
          ChromaticIndex (RestrictEdges G F) := by
-- BODY
  classical
  have full : ChromaticIndex (IncidentCore G) = ChromaticIndex G := by
    apply Nat.le_antisymm
    · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec G).1
      apply (ChromaticIndexSpec (IncidentCore G)).2 (ChromaticIndex G)
      exact ⟨phi, (IncidentCoreColoringTransport G).2.1
        (ChromaticIndex G) phi |>.2 hp, hf⟩
    · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec (IncidentCore G)).1
      apply (ChromaticIndexSpec G).2 (ChromaticIndex (IncidentCore G))
      exact ⟨phi, (IncidentCoreColoringTransport G).2.1
        (ChromaticIndex (IncidentCore G)) phi |>.1 hp, hf⟩
  refine ⟨full, ?_⟩
  intro F
  apply Nat.le_antisymm
  · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec (RestrictEdges G F)).1
    apply (ChromaticIndexSpec (RestrictEdges (IncidentCore G) F)).2
      (ChromaticIndex (RestrictEdges G F))
    exact ⟨phi, (IncidentCoreColoringTransport G).2.2.2 F
      (ChromaticIndex (RestrictEdges G F)) phi |>.2 hp, hf⟩
  · obtain ⟨phi, hp, hf⟩ :=
      (ChromaticIndexSpec (RestrictEdges (IncidentCore G) F)).1
    apply (ChromaticIndexSpec (RestrictEdges G F)).2
      (ChromaticIndex (RestrictEdges (IncidentCore G) F))
    exact ⟨phi, (IncidentCoreColoringTransport G).2.2.2 F
      (ChromaticIndex (RestrictEdges (IncidentCore G) F)) phi |>.1 hp, hf⟩
