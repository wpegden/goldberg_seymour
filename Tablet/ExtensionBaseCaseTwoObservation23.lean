import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore

-- [TABLET NODE: ExtensionBaseCaseTwoObservation23]
theorem ExtensionBaseCaseTwoObservation23 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 : PartialEdgeColoring E k)
    (terminalSupport u : V) (beta gammaFirst : Fin k)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huSeed : u ∉ TreeSequenceVertexSet seed)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hbetaU : beta ∈ MissingColors G rho1 u)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hterminalRho : beta ∉ MissingColors G rho1 terminalSupport)
    (hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (hbetaGamma : beta ≠ gammaFirst)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a)) :
    ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj)
      (zPosition : Fin (Tj.length + 1)),
      Tj.vertex zPosition = z ∧ seed.length ≤ zPosition.val ∧
        ((seed.length < zPosition.val ∧
            beta ∈ MissingColors G rho1 z ∧
            ∀ r : Fin (Tj.length + 1),
              seed.length < r.val → r.val < zPosition.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
          (zPosition = Fin.last Tj.length ∧
            ∀ r : Fin (Tj.length + 1), seed.length < r.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r))) ∧
        (∀ w ∈ TreeVerticesBefore Tj z hz,
          beta ∉ MissingColors G rho1 w) ∧
        ∀ a : Fin Tj.length, seed.length ≤ a.val →
          a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta := by
-- BODY
  sorry
