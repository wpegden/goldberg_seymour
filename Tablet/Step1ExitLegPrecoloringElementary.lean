import Tablet.CertifiedETTPredecessor
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
  sorry
