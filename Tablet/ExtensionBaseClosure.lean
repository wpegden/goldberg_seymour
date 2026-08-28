import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosureExists
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: ExtensionBaseClosure]
theorem ExtensionBaseClosure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (rho1 : PartialEdgeColoring E k) (seed : TreeSequence G e0)
    (terminalSupport : V) (supportColors : Finset (Fin k))
    (hseedSegment : TreeSequenceInitialSegment
      (base.series.data.tree (Fin.last base.rounds).castSucc) seed)
    (hseedStrict :
      (base.series.data.tree (Fin.last base.rounds).castSucc).length <
        seed.length)
    (hseedEligible :
      (base.series.data.kind (Fin.last base.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho1
          (base.series.data.tree (Fin.last base.rounds).castSucc) seed) ∨
      ((base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.SE ∨
          base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          base.series.data.connectingEdges (Fin.last base.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (base.series.data.tree (Fin.last base.rounds).castSucc)
              f adjoinSeed ∧
            TashkinovAugmentationSequence rho1 adjoinSeed seed))
    (hmod : ModColoring base rho1) (hMP : MaximumProperty base)
    (hLowerElementary : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 base rho1 Tstar),
      MaximumProperty corr.replacementETT →
      ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet Tstar)) :
    ∃ (TjPrime : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 base rho1 TjPrime),
      TashkinovClosure rho1 seed TjPrime ∧
        MaximumProperty corr.replacementETT ∧
        ColoredVertexSetElementary G rho1
          (TreeSequenceVertexSet TjPrime) ∧
        (let awayMissing :=
          ((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
            fun v => MissingColors G rho1 v
         (awayMissing ∩ supportColors).Nonempty ∨
           awayMissing ∩ supportColors = ∅) := by
-- BODY
  sorry
