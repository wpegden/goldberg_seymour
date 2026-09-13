import Tablet.BoundaryEdges
import Tablet.InternalEdges
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: EarlierPECycleFirstNonrevisitingInternal]
theorem EarlierPECycleFirstNonrevisitingInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (r : Fin rounds) (hrEarlier : r.succ ≠ Fin.last rounds)
    (gamma delta : Fin k)
    (hkindr : series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hgammar : series.data.gamma r.succ = some gamma)
    (hdeltar : series.data.delta r.succ = some delta)
    (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta)
    (hmeets : ∃ v ∈ TreeSequenceVertexSet
        (series.data.tree r.succ.castSucc),
      Sum.inl v ∈ cycle.walk.support)
    (hterminal : series.data.kind (Fin.last rounds) =
      some TashkinovExtensionKind.PE) :
    ∃ p : Fin rounds,
      r.val < p.val ∧
      (series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
        series.data.kind p.succ = some TashkinovExtensionKind.PE) ∧
      (∀ j : Fin rounds, r.val < j.val → j.val < p.val →
        series.data.kind j.succ = some TashkinovExtensionKind.RE) ∧
      series.data.coloring p.castSucc = series.data.coloring r.succ ∧
      ∀ f : E, Sum.inr f ∈ cycle.walk.support →
        f ∈ InternalEdges G
          (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)) := by
-- BODY
  sorry
