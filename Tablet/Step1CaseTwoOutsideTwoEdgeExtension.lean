import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.Incident
import Tablet.LooplessMultigraph
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: Step1CaseTwoOutsideTwoEdgeExtension]
lemma Step1CaseTwoOutsideTwoEdgeExtension {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi mu : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (C : TreeSequence G e0)
    (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C)
    (baseC : HierarchyBase corrC.replacementETT mu)
    (KC : TashkinovHierarchy corrC.replacementETT baseC)
    (goodC : GoodHierarchy KC)
    (hmod : ModColoring ett mu)
    (hMPC : MaximumProperty corrC.replacementETT)
    (heligible :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) C) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence mu seed C))
    (hlargeC : 2 * corrC.replacementETT.rounds + 11 ≤
      (TreeMissingColors mu
        (corrC.replacementETT.series.data.tree
          (Fin.last corrC.replacementETT.rounds).castSucc)).card)
    (beta gamma : Fin k)
    (hgammaReserved : gamma ∉ (HierarchyStoredColorsAt KC
      (Fin.last KC.dividerCount)).biUnion
        (goodC.gamma (Fin.last KC.dividerCount)))
    (hbetaReserved : beta ∉ (HierarchyStoredColorsAt KC
      (Fin.last KC.dividerCount)).biUnion
        (goodC.gamma (Fin.last KC.dividerCount)))
    (b₁ b₂ b₃ : V) (f₁ f₂ : E)
    (hbetaMissing : beta ∈ MissingColors G mu b₃)
    (hf₁ : f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (houtsideDistinct : ∀ u₁ u₂, Incident G u₁ f₁ →
      u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ →
      u₂ ∉ TreeSequenceVertexSet C → u₁ ≠ u₂)
    (hb₁ : b₁ ∈ TreeSequenceVertexSet C)
    (hb₂ : b₂ ∈ TreeSequenceVertexSet C)
    (hb₃ : b₃ ∈ TreeSequenceVertexSet C) :
    ∃ (J₁ J : TreeSequence G e0)
      (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett mu J)
      (baseJ : HierarchyBase corrJ.replacementETT mu)
      (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
      (goodJ : GoodHierarchy KJ),
      MaximumProperty corrJ.replacementETT ∧
      KJ.dividerCount = KC.dividerCount ∧
      2 * corrJ.replacementETT.rounds + 11 ≤
        (TreeMissingColors mu
          (corrJ.replacementETT.series.data.tree
            (Fin.last corrJ.replacementETT.rounds).castSucc)).card ∧
      gamma ∉ (HierarchyStoredColorsAt KJ
        (Fin.last KJ.dividerCount)).biUnion
          (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
      beta ∉ (HierarchyStoredColorsAt KJ
        (Fin.last KJ.dividerCount)).biUnion
          (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
      TreeSequenceAdjoinEdge C f₁ J₁ ∧
      TreeSequenceAdjoinEdge J₁ f₂ J ∧
      (∀ v, Incident G v f₁ → v ∈ TreeSequenceVertexSet J) ∧
      (∀ v, Incident G v f₂ → v ∈ TreeSequenceVertexSet J) ∧
      b₁ ∈ TreeSequenceVertexSet J ∧
      b₂ ∈ TreeSequenceVertexSet J ∧
      b₃ ∈ TreeSequenceVertexSet J := by
-- BODY
  sorry
