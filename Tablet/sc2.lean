import Tablet.StableColoring
import Tablet.sc1

-- [TABLET NODE: sc2]
theorem sc2 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k)) :
    Equivalence
      (fun phi pi : {psi : PartialEdgeColoring E k //
          IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} =>
        StableColoring T C phi.1 pi.1) := by
-- BODY
  classical
  constructor
  · intro a
    unfold StableColoring
    constructor
    · intro f hf h
      rfl
    · intro v hv
      rfl
  · intro a b hab
    have hmiss : ∀ v, v ∈ TreeSequenceVertexSet T →
        MissingColors G b.1 v = MissingColors G a.1 v := by
      intro v hv
      exact hab.2 v hv
    have htree : TreeMissingColors b.1 T = TreeMissingColors a.1 T := by
      ext c
      unfold TreeMissingColors
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← hmiss v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [hmiss v hv]; exact hc⟩
    apply (sc1 G e0 T C b.1 a.1 b.2.1 b.2.2 a.2.1 a.2.2).2
    intro f hf h
    have hcrit := (sc1 G e0 T C a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2).mp hab
    rw [htree] at h
    rcases h with hb | ha
    have heq : b.1 f = a.1 f := by
      apply hcrit f hf
      exact Or.inr hb
    · exact heq.symm
    · have heq : b.1 f = a.1 f := by
        apply hcrit f hf
        exact Or.inl ha
      exact heq.symm
  · intro a b c hab hbc
    have hmissAB : ∀ v, v ∈ TreeSequenceVertexSet T →
        MissingColors G b.1 v = MissingColors G a.1 v := by
      intro v hv
      exact hab.2 v hv
    have hmissBC : ∀ v, v ∈ TreeSequenceVertexSet T →
        MissingColors G c.1 v = MissingColors G b.1 v := by
      intro v hv
      exact hbc.2 v hv
    have htreeAB : TreeMissingColors b.1 T = TreeMissingColors a.1 T := by
      ext x
      unfold TreeMissingColors
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hx⟩
        exact ⟨v, hv, by rw [← hmissAB v hv]; exact hx⟩
      · rintro ⟨v, hv, hx⟩
        exact ⟨v, hv, by rw [hmissAB v hv]; exact hx⟩
    have htreeBC : TreeMissingColors c.1 T = TreeMissingColors b.1 T := by
      ext x
      unfold TreeMissingColors
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hx⟩
        exact ⟨v, hv, by rw [← hmissBC v hv]; exact hx⟩
      · rintro ⟨v, hv, hx⟩
        exact ⟨v, hv, by rw [hmissBC v hv]; exact hx⟩
    apply (sc1 G e0 T C a.1 c.1 a.2.1 a.2.2 c.2.1 c.2.2).2
    have hcritAB := (sc1 G e0 T C a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2).mp hab
    have hcritBC := (sc1 G e0 T C b.1 c.1 b.2.1 b.2.2 c.2.1 c.2.2).mp hbc
    intro f hf h
    rcases h with ha | hc
    · have habf : b.1 f = a.1 f := by
        apply hcritAB f hf
        left
        exact ha
      have hbcf : c.1 f = b.1 f := by
        apply hcritBC f hf
        left
        rcases ha with ⟨color, hcolor, haf⟩
        refine ⟨color, ?_, ?_⟩
        · rw [htreeAB]
          exact hcolor
        · rw [habf]
          exact haf
      exact hbcf.trans habf
    · have hbcf : c.1 f = b.1 f := by
        apply hcritBC f hf
        right
        have hcB := hc
        rw [← htreeAB] at hcB
        exact hcB
      have habf : b.1 f = a.1 f := by
        apply hcritAB f hf
        right
        rcases hc with ⟨color, hcolor, hcf⟩
        refine ⟨color, hcolor, ?_⟩
        rw [← hbcf]
        exact hcf
      exact hbcf.trans habf
