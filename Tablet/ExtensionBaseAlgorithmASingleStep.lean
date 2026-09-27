import Tablet.ETTStrongInterchangeable
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ExtensionBaseAlgorithmASingleStep]
theorem ExtensionBaseAlgorithmASingleStep {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (vt : V) (phi : PartialEdgeColoring E k)
    (gammaT deltaT : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hSI : ETTStrongInterchangeable ett t vt phi gammaT deltaT)
    (hvtTree : vt ∈ TreeSequenceVertexSet
      (ett.series.data.tree t.succ.castSucc))
    (hdeltaMissing : deltaT ∈ MissingColors G phi vt)
    (hgammaPresent : gammaT ∈ PresentColors G phi vt) :
    TwoColorNontrivialPathComponent G phi gammaT deltaT (Sum.inl vt) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet
            (ett.series.data.tree t.succ.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G phi gammaT deltaT (Sum.inl vt) ↔
          w = vt)) ∧
      IsProperEdgeColoring G
        (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) ∧
      IsOneEdgeUncolored
        (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) e0 := by
-- BODY
  sorry
