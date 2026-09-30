import Tablet.BoundaryEdges
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorCycle

-- [TABLET NODE: RevisitingPriorityCycleContainment]
theorem RevisitingPriorityCycleContainment {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t terminal : Fin rounds) (support : V) (gamma delta : Fin k)
    (htTerminal : t.val < terminal.val)
    (hterminalKind : series.data.kind terminal.succ =
      some TashkinovExtensionKind.PE)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta)
    (hcycles : ∀ v : V,
      v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
      v ≠ support →
      TwoColorComponentCycle G (series.data.coloring t.succ)
        gamma delta (Sum.inl v)) :
    ∃ epsilon : Fin rounds,
      t.val < epsilon.val ∧ epsilon.val ≤ terminal.val ∧
      series.data.kind epsilon.succ ≠
        some TashkinovExtensionKind.RE ∧
      (∀ r : Fin rounds, t.val < r.val → r.val < epsilon.val →
        series.data.kind r.succ = some TashkinovExtensionKind.RE) ∧
      ∀ v : V,
        v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
        v ≠ support →
        ∀ w : V,
          Sum.inl w ∈ TwoColorComponent G
            (series.data.coloring t.succ) gamma delta (Sum.inl v) →
          w ∈ TreeSequenceVertexSet
            (series.data.tree epsilon.succ.castSucc) := by
-- BODY
  sorry
