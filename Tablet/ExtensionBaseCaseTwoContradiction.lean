import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtensionBaseClaim45
import Tablet.InternalEdges
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosureExists
import Tablet.TashkinovStoredColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore

-- [TABLET NODE: ExtensionBaseCaseTwoContradiction]
theorem ExtensionBaseCaseTwoContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    {lowerInput : PartialEdgeColoring E k}
    {lowerTree : TreeSequence G e0}
    {lowerGenerating : PartialEdgeColoring E k}
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree
      lowerGenerating)
    (jSlot : Fin ett.rounds) (hjPositive : 1 ≤ jSlot.val)
    (Tjm1 Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 rho3 : PartialEdgeColoring E k)
    (Dprev : Finset (Fin k))
    (terminalSupport u z : V) (beta gammaFirst deltaN : Fin k)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (hzTj : z ∈ TreeSequenceVertexSet Tj)
    (zPosition : Fin (Tj.length + 1))
    (uPosition : Fin (TjPrime.length + 1))
    (hzPosition : Tj.vertex zPosition = z)
    (huPosition : TjPrime.vertex uPosition = u)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hseedAtMostZ : seed.length ≤ zPosition.val)
    (hseedBeforeU : seed.length < uPosition.val)
    (hterminalBeforeZ : terminalSupport ∈ TreeVerticesBefore Tj z hzTj)
    (huOutsideTj : u ∉ TreeSequenceVertexSet Tj)
    (hTjm1Stored :
      ett.series.data.tree jSlot.castSucc.castSucc = Tjm1)
    (hPhiJStored : ett.series.data.coloring jSlot.castSucc = phiJ)
    (hTjStored : ett.series.data.tree jSlot.succ.castSucc = Tj)
    (hDprevStored :
      TashkinovStoredColors ett.series.data jSlot.castSucc = Dprev)
    (hLowerRounds : lower.rounds = jSlot.val)
    (hLowerTree : lower.series.data.tree
      (Fin.last lower.rounds).castSucc = Tjm1)
    (hLowerColor : lower.series.data.coloring
      (Fin.last lower.rounds) = phiJ)
    (hLowerStored : TashkinovStoredColors lower.series.data
      (Fin.last lower.rounds) = Dprev)
    (hLowerKind : lower.series.data.kind (Fin.last lower.rounds) =
      ett.series.data.kind jSlot.castSucc)
    (hLowerConnecting : lower.series.data.connectingEdges
      (Fin.last lower.rounds) =
        ett.series.data.connectingEdges jSlot.castSucc)
    (hTjm1Before : TreeSequenceVertexSet Tjm1 ⊆
      TreeVerticesBefore Tj terminalSupport hterminalTj)
    (hseedBuild :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phiJ Tjm1 seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
            TashkinovAugmentationSequence phiJ adjoinSeed seed))
    (hTjAugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hprimeClosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hMP : MaximumProperty ett)
    (hLowerMP : MaximumProperty lower)
    (hLowerI : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3 Tstar),
      MaximumProperty corr.replacementETT →
        ColoredVertexSetElementary G rho3
          (TreeSequenceVertexSet Tstar))
    (hLowerVI : ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tjm1 Dprev phiJ sigma → ModColoring lower sigma)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
        MissingColors G rho1 v = MissingColors G phiJ v)
    (hb2Edges : ∀ a : Fin Tj.length,
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (huniquezang : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (hdeltaRho1 : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hbetaU : beta ∈ MissingColors G rho1 u)
    (hrhoProper : IsProperEdgeColoring G rho3)
    (hrhoOne : IsOneEdgeUncolored rho3 e0)
    (hd1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3)
    (hd2Missing : ∀ v : V,
      v ∈ (((TreeVerticesBefore Tj z hzTj ∪ {z}) ∪
          (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v)
    (hd2Edges : ∀ f : E,
      ((∃ a : Fin Tj.length, a.val < zPosition.val ∧ Tj.edge a = f) ∨
        (∃ a : Fin TjPrime.length,
          a.val < uPosition.val ∧ TjPrime.edge a = f)) →
      rho3 f = rho1 f)
    (hd2Delta : beta ∈ MissingColors G rho1 z →
      deltaN ∈ MissingColors G rho3 z)
    (hd2Z : z ∈ TreeVerticesBefore TjPrime u huPrime →
      MissingColors G rho3 z = MissingColors G rho1 z)
    (hd3 : gammaFirst ∈ MissingColors G rho3 u)
    (hzChoice : zPosition = Fin.last Tj.length ∨
      (zPosition.val < (Fin.last Tj.length).val ∧
        beta ∈ MissingColors G rho1 z)) : False := by
-- BODY
  sorry
