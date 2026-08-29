import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetClosed
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeIncidentEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.sc2

-- [TABLET NODE: ExtensionBaseCaseTwoObservation20]
theorem ExtensionBaseCaseTwoObservation20 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn seed TjPrime : TreeSequence G e0)
    (phiN sigmaN rho1 : PartialEdgeColoring E k)
    (controlled restorationColors : Finset (Fin k))
    (gammaN deltaN : Fin k) (fN : E) (terminalSupport : V)
    (hphiProper : IsProperEdgeColoring G phiN)
    (hphiOne : IsOneEdgeUncolored phiN e0)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hsigmaStable : StableColoring Tn controlled phiN sigmaN)
    (hgammaControlled : gammaN ∈ controlled)
    (hdeltaControlled : deltaN ∈ controlled)
    (hb3 : ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G (TreeSequenceVertexSet Tn) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors)
    (hgammaRestored : gammaN ∉ restorationColors)
    (hdeltaRestored : deltaN ∉ restorationColors)
    (hgammaBoundary :
      BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaLocation : ∀ f ∈ BoundaryColorEdges G phiN
        (TreeSequenceVertexSet Tn) deltaN,
      ∃ w ∈ TreeSequenceVertexSet seed, Incident G w f)
    (hseedN : TreeSequenceInitialSegment seed Tn)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport) :
    BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN = {fN} ∧
      BoundaryColorEdges G rho1
        (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) deltaN = ∅ := by
-- BODY
  sorry
