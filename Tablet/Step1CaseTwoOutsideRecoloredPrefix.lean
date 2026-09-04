import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: Step1CaseTwoOutsideRecoloredPrefix]
lemma Step1CaseTwoOutsideRecoloredPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (halpha : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∉ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (hpaths₁₂ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (hpaths₁₃ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₃ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hif₃ : Incident G b₃ f₃)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hPf₃ : Sum.inr f₃ ∈ P₃.support)
    (houtside : b₃ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))) :
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k)
      (Bminus C : TreeSequence G e0)
      (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₁) (Sum.inl b₁))
      (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₂) (Sum.inl b₂))
      (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₃) (Sum.inl b₃)),
      gamma ≠ beta ∧
      IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧
      StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        phi mu ∧
      (∀ e, TreeIncidentEdge Bminus e → mu e = phi e) ∧
      (∀ v, v ∈ TreeSequenceVertexSet Bminus →
        MissingColors G mu v = MissingColors G phi v) ∧
      gamma ∉ (HierarchyStoredColorsAt H
        (Fin.last H.dividerCount)).biUnion
          (good.gamma (Fin.last H.dividerCount)) ∧
      gamma ∈ MissingColors G phi b₃ ∧
      beta ∈ MissingColors G mu b₃ ∧
      mu f₃ = some gamma ∧
      (∀ v, v ∈ TreeSequenceVertexSet C → ∀ eta,
        eta ≠ gamma → eta ≠ beta →
        (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors G phi v)) ∧
      TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧
      TreeExitPath T mu gamma beta a₂ b₂ R₂ ∧
      TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧
      (∀ x, x ∈ R₁.support → x ∉ R₂.support) ∧
      (∀ x, x ∈ R₁.support → x ∉ R₃.support) ∧
      (∀ x, x ∈ R₂.support → x ∉ R₃.support) ∧
      R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
      R₃.support = P₃.support ∧
      R₁.length = P₁.length ∧ R₂.length = P₂.length ∧
      R₃.length = P₃.length ∧
      TreeSequenceInitialSegment
        (HierarchyStarredStage H (Fin.last H.dividerCount)) Bminus ∧
      Bminus.length < C.length ∧ TreeSequenceInitialSegment C T ∧
      C.vertex (Fin.last C.length) = b₃ ∧
      (∃ g, TreeSequenceAdjoinEdge Bminus g C) ∧
      f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta ∧
      f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta ∧
      (∀ u₁ u₂, Incident G u₁ f₁ →
        u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ →
        u₂ ∉ TreeSequenceVertexSet C → u₁ ≠ u₂) ∧
      b₁ ∈ TreeSequenceVertexSet C ∧
      b₂ ∈ TreeSequenceVertexSet C ∧
      b₃ ∈ TreeSequenceVertexSet C := by
-- BODY
  sorry
