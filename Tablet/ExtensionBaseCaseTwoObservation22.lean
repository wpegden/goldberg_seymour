import Tablet.MissingColors
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseCaseTwoObservation22]
theorem ExtensionBaseCaseTwoObservation22 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
    (supportColors : Finset (Fin k)) (terminalSupport u : V)
    (beta : Fin k)
    (hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn)
    (hu : u ∈ TreeSequenceVertexSet TjPrime \ TreeSequenceVertexSet Tn)
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hbeta : beta ∈ MissingColors G rho1 u) :
    beta ∉ supportColors := by
-- BODY
  sorry
