import Tablet.HkuMissingStoredMonotone
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.SameColorSeriesPreserved
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: StableSeriesCycleComponentTransport]
theorem StableSeriesCycleComponentTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t epsilon terminal : Fin rounds) (gamma delta : Fin k)
    (htEpsilon : t.val < epsilon.val)
    (hepsilonTerminal : epsilon.val ≤ terminal.val)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta)
    (hintervening : ∀ r : Fin rounds,
      t.val < r.val → r.val < epsilon.val →
      series.data.kind r.succ = some TashkinovExtensionKind.RE)
    (hterminalKind : series.data.kind terminal.succ =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (series.data.tree terminal.succ.castSucc)
      (TashkinovStoredColors series.data terminal.succ)
      (series.data.coloring terminal.succ) sigma)
    (z : Sum V E)
    (hcycle : TwoColorComponentCycle G
      (series.data.coloring t.succ) gamma delta z)
    (hcontained : ∀ w : V,
      Sum.inl w ∈ TwoColorComponent G
        (series.data.coloring t.succ) gamma delta z →
      w ∈ TreeSequenceVertexSet
        (series.data.tree epsilon.succ.castSucc)) :
    TwoColorComponent G sigma gamma delta z =
        TwoColorComponent G (series.data.coloring t.succ) gamma delta z ∧
      TwoColorComponentCycle G sigma gamma delta z := by
-- BODY
  sorry
