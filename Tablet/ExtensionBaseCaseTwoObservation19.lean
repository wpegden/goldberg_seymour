import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseCaseTwoObservation19]
theorem ExtensionBaseCaseTwoObservation19 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (rho1 : PartialEdgeColoring E k) (seed TjPrime : TreeSequence G e0)
    (terminalSupport : V) (supportColors : Finset (Fin k))
    (deltaN : Fin k)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminal : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hterminalColors :
      MissingColors G rho1 terminalSupport ∩ supportColors = {deltaN}) :
    TreeMissingColors rho1 TjPrime ∩ supportColors = {deltaN} ∧
      ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
        ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
          rho1 (TjPrime.edge a) ≠ some c := by
-- BODY
  sorry
