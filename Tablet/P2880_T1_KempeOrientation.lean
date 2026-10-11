import Tablet.TwoColorComponentSwap
import Tablet.TwoColorPathComponent

-- [TABLET NODE: P2880_T1_KempeOrientation]
theorem P2880_T1_KempeOrientation
    {V E : Type*} (G : LooplessMultigraph V E)
    {k : Nat} (mu : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hne : alpha ≠ beta) :
    TwoColorIncidenceGraph G mu alpha beta =
      TwoColorIncidenceGraph G mu beta alpha ∧
    (∀ z, TwoColorComponent G mu alpha beta z =
      TwoColorComponent G mu beta alpha z) ∧
    (∀ z, TwoColorComponentSwap G mu alpha beta z =
      TwoColorComponentSwap G mu beta alpha z) ∧
    (∀ z, TwoColorPathComponent G mu alpha beta z ↔
      TwoColorPathComponent G mu beta alpha z) := by
-- BODY
  classical
  have hgraph : TwoColorIncidenceGraph G mu alpha beta =
      TwoColorIncidenceGraph G mu beta alpha := by
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  have hcomp : ∀ z, TwoColorComponent G mu alpha beta z =
      TwoColorComponent G mu beta alpha z := by
    intro z
    unfold TwoColorComponent
    rw [hgraph]
  refine ⟨hgraph, hcomp, ?_, ?_⟩
  · intro z
    funext e
    unfold TwoColorComponentSwap
    rw [← hcomp z]
    by_cases hc : Sum.inr e ∈ TwoColorComponent G mu alpha beta z
    · by_cases ha : mu e = some alpha
      · simp [hc, ha, hne]
      · by_cases hb : mu e = some beta
        · simp [hc, ha, hb]
        · simp [hc, ha, hb]
    · simp [hc]
  · intro z
    unfold TwoColorPathComponent
    rw [hgraph, hcomp]
    simp only [ne_comm]

