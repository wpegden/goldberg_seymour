import Tablet.TreeInterchangeable
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent

-- [TABLET NODE: InterchangeableNonrootComponentCycle]
theorem InterchangeableNonrootComponentCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (A B : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (support : V)
    (hproper : IsProperEdgeColoring G phi)
    (hsegment : TreeSequenceInitialSegment A B)
    (hinterchange : TreeInterchangeable G B phi alpha beta)
    (hrootPath : TwoColorPathComponent G phi alpha beta
      (Sum.inl support))
    (hsupport : support ∈ TreeSequenceVertexSet A)
    (hrootOnly : ∀ w : V, w ∈ TreeSequenceVertexSet A →
      (Sum.inl w ∈ TwoColorComponent G phi alpha beta
        (Sum.inl support) ↔ w = support))
    (hnonisolated : ∀ v : V, v ∈ TreeSequenceVertexSet A →
      v ≠ support → ∃ f : E,
        Sum.inr f ∈ TwoColorComponent G phi alpha beta (Sum.inl v)) :
    ∀ v : V, v ∈ TreeSequenceVertexSet A → v ≠ support →
      TwoColorComponentCycle G phi alpha beta (Sum.inl v) ∧
        Sum.inl support ∉
          TwoColorComponent G phi alpha beta (Sum.inl v) := by
-- BODY
  sorry
