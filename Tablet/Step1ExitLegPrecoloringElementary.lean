import Tablet.CertifiedETTPredecessor
import Tablet.ExtendedTashkinovTree
import Tablet.Step1ExitLegPresentation
import Tablet.TechnicalTheoremBase

-- [TABLET NODE: Step1ExitLegPrecoloringElementary]
lemma Step1ExitLegPrecoloringElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (P : Step1ExitLegPresentation G k e0 n q)
    (hlowerElementary : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < P.ett.rounds →
      MaximumProperty lower →
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T')) :
    let r : Fin P.ett.rounds := ⟨P.ett.rounds - 1, by
      have h := P.ett.roundsPositive
      omega⟩
    ColoredVertexSetElementary G
      (P.ett.series.data.coloring r.castSucc)
      (TreeSequenceVertexSet
        (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)) := by
-- BODY
  dsimp
  by_cases hrounds : P.ett.rounds = 1
  · have hcolor :
        (⟨P.ett.rounds - 1, by omega⟩ : Fin (P.ett.rounds + 1)) = 0 := by
      apply Fin.ext
      simp [hrounds]
    have htree :
        (Fin.castSucc (Fin.last P.ett.rounds) : Fin (P.ett.rounds + 2)) =
          ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [hrounds]
    rw [hcolor, htree]
    exact (TechnicalTheoremBase G k P.ett.rounds e0 P.input
      P.ett.series).1
  · have hmore : 1 < P.ett.rounds := by
      have hpositive := P.ett.roundsPositive
      omega
    obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
      CertifiedETTPredecessor G k e0 P.input P.T P.phi P.ett
        P.maximum hmore
    have hpositive : 0 < predecessor.rounds := by
      rw [hr]
      omega
    have hlower : predecessor.rounds < P.ett.rounds := by
      rw [hr]
      omega
    have htree :
        (Fin.castSucc (Fin.last P.ett.rounds) : Fin (P.ett.rounds + 2)) =
          ⟨P.ett.rounds, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [htree]
    exact hlowerElementary predecessor hpositive hlower hmaximum
