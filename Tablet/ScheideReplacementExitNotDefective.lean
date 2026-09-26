import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.MissingColors
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideLastExitPath
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementSelectionSwitch
import Tablet.ScheideReplacementUsedWitness
import Tablet.ScheideStructuralExitsInBase
import Tablet.TreeFreeColors
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: ScheideReplacementExitNotDefective]
theorem ScheideReplacementExitNotDefective {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∉ TreeSequenceVertexSet T)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)})
    (hpair : L.lastInside ∈ ({(R d).u1, (R d).u2} : Finset V))
    (hgraph : TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha) :
    (∃ beta,
      beta ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) L.lastInside ∧
      beta ∈ TreeFreeColors
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) (R d).replacementTree) ∧
    alpha ∉ DefectiveColors G
      (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)))
      (TreeSequenceVertexSet (R d).replacementTree) := by
-- BODY
  sorry
