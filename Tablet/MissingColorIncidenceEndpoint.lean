import Tablet.AdjacentEdges
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorIncidenceDegreeAtMostTwo

-- [TABLET NODE: MissingColorIncidenceEndpoint]
theorem MissingColorIncidenceEndpoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (v : V)
    (hmissing : alpha ∈ MissingColors G phi v) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
-- BODY
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have haAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) a :=
    by simpa [SimpleGraph.neighborFinset] using ha
  have hbAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) b :=
    by simpa [SimpleGraph.neighborFinset] using hb
  cases a with
  | inl a => simp [TwoColorIncidenceGraph] at haAdj
  | inr a =>
    cases b with
    | inl b => simp [TwoColorIncidenceGraph] at hbAdj
    | inr b =>
      by_contra hab
      have haData := haAdj
      have hbData := hbAdj
      simp [TwoColorIncidenceGraph] at haData hbData
      rcases haData with ⟨haIncident, haColor⟩
      rcases hbData with ⟨hbIncident, hbColor⟩
      have haNot : ¬ phi a = some alpha := by
        intro haAlpha
        have hpresent : alpha ∈ PresentColors G phi v := by
          simp [PresentColors]
          exact ⟨a, haIncident, haAlpha⟩
        have hnotpresent : alpha ∉ PresentColors G phi v := by
          simpa [MissingColors] using hmissing
        exact hnotpresent hpresent
      have haBeta : phi a = some beta := haColor.resolve_left haNot
      have hbBeta : phi b = some beta := hbColor.resolve_left (by
        intro hbAlpha
        have hpresent : alpha ∈ PresentColors G phi v := by
          simp [PresentColors]
          exact ⟨b, hbIncident, hbAlpha⟩
        have hnotpresent : alpha ∉ PresentColors G phi v := by
          simpa [MissingColors] using hmissing
        exact hnotpresent hpresent)
      have hadj : AdjacentEdges G a b := ⟨v, haIncident, hbIncident⟩
      have habEdges : a ≠ b := by
        intro habEdges
        exact hab (congrArg Sum.inr habEdges)
      exact (hproper habEdges hadj haBeta) hbBeta
