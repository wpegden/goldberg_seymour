import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.Degree
import Tablet.ETTFirstAppearanceIndex
import Tablet.ElementaryClosedExitPairExtendsTriple
import Tablet.ElementaryClosedNoninterchangeableExitPair
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyLEMStable
import Tablet.HierarchyOutsideKempeStable
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
import Tablet.ParallelCommonMissingClosed
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
import Tablet.Step1CaseOneInsideStar
import Tablet.Step1CaseOneOutsideStar
import Tablet.Step1CaseTwoInsideStar
import Tablet.Step1CaseTwoOutsideStar
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.Td
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeExitPath
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.interchange
import Tablet.sc2
import Tablet.Step1ZeroDividerAnchor

-- [TABLET NODE: Step1ExitLegGlobalMinimum]
lemma Step1ExitLegGlobalMinimum {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext : TreeSequence G e0 :=
           lower.series.data.tree (Fin.last (lower.rounds + 1))
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tnext
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) →
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                StableColoring (lower.series.data.tree j.castSucc)
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v →
               (∃ w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.PE ∨
                    lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ModColoring lower sigma))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < H.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (i : Fin H.dividerCount) (alpha beta : Fin k)
    (halpha : alpha ∈
      TreeMissingColors phi (H.stage i.succ.castSucc))
    (hne : alpha ≠ beta)
    (hclosed : TreeColorSetClosed G phi
      (H.stage i.succ.castSucc) {alpha})
    (hnot : ¬ TreeInterchangeable G
      (H.stage i.succ.castSucc) phi alpha beta) :
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0)
      (psi : PartialEdgeColoring E k)
      (other : ExtendedTashkinovTree G k e0 input' T' psi)
      (base' : HierarchyBase other psi)
      (K : TashkinovHierarchy other base') (good' : GoodHierarchy K),
      other.rounds = ett.rounds ∧ MaximumProperty other ∧
      K.dividerCount < H.dividerCount ∧
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 ∧
      2 * other.rounds + 11 ≤
        (TreeMissingColors psi
          (other.series.data.tree (Fin.last other.rounds).castSucc)).card ∧
      TreeColorSetMinusClosed G psi T'
        ((HierarchyTerminalStoredColors K).biUnion
          (good'.gamma (Fin.last K.dividerCount))) ∧
      ColoredVertexSetElementary G psi (TreeSequenceVertexSet T') ∧
      ∃ (a b theta : Fin k)
        (a₁ b₁ a₂ b₂ : V)
        (P₁ : (TwoColorIncidenceGraph G psi a b).Walk
          (Sum.inl a₁) (Sum.inl b₁))
        (P₂ : (TwoColorIncidenceGraph G psi a b).Walk
          (Sum.inl a₂) (Sum.inl b₂))
        (f₁ f₂ : E),
        a ≠ b ∧ a ∈ TreeMissingColors psi T' ∧
        TreeColorSetClosed G psi T' {a} ∧
        TreeExitPath T' psi a b a₁ b₁ P₁ ∧
        TreeExitPath T' psi a b a₂ b₂ P₂ ∧
        (∀ x, x ∈ P₁.support → x ∉ P₂.support) ∧
        a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ TreeVertexOrder T' b₁ b₂ ∧
        f₁ ∈ BoundaryColorEdges G psi (TreeSequenceVertexSet T') b ∧
        f₂ ∈ BoundaryColorEdges G psi (TreeSequenceVertexSet T') b ∧
        Incident G b₁ f₁ ∧ Incident G b₂ f₂ ∧
        Sum.inr f₁ ∈ P₁.support ∧ Sum.inr f₂ ∈ P₂.support ∧
        theta ≠ a ∧ theta ≠ b ∧
        theta ∈ TreeMissingColors psi
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        TreeColorSetClosed G psi
          (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta} ∧
        TreeColorSetClosed G psi T' {theta} ∧
        (∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0)
          (corr : CorrespondingExtendedTashkinovTree G k e0 other sigma U),
          IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
          StableColoring
            (other.series.data.tree (Fin.last other.rounds).castSucc)
            (TashkinovStoredColors other.series.data
              (Fin.last other.rounds)) psi sigma →
          MaximumProperty corr.replacementETT →
          ∀ (baseU : HierarchyBase corr.replacementETT sigma)
            (L : TashkinovHierarchy corr.replacementETT baseU)
            (goodU : GoodHierarchy L),
            L.dividerCount < K.dividerCount →
            2 * corr.replacementETT.rounds + 11 ≤
              (TreeMissingColors sigma
                (corr.replacementETT.series.data.tree
                  (Fin.last corr.replacementETT.rounds).castSucc)).card →
            TreeColorSetMinusClosed G sigma U
              ((HierarchyTerminalStoredColors L).biUnion
                (goodU.gamma (Fin.last L.dividerCount))) →
            ∀ (c d : Fin k), c ≠ d →
              c ∈ TreeMissingColors sigma U →
              TreeColorSetClosed G sigma U {c} →
              ∀ (u₁ v₁ u₂ v₂ : V)
                (Q₁ : (TwoColorIncidenceGraph G sigma c d).Walk
                  (Sum.inl u₁) (Sum.inl v₁))
                (Q₂ : (TwoColorIncidenceGraph G sigma c d).Walk
                  (Sum.inl u₂) (Sum.inl v₂)),
                TreeExitPath U sigma c d u₁ v₁ Q₁ →
                TreeExitPath U sigma c d u₂ v₂ Q₂ →
                (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
                u₁ ≠ u₂ → False) ∧
        (b ∈ TreeMissingColors psi T' ∨
          (b ∉ TreeMissingColors psi T' ∧
            ∃ (a₃ b₃ : V)
              (P₃ : (TwoColorIncidenceGraph G psi a b).Walk
                (Sum.inl a₃) (Sum.inl b₃)) (f₃ : E),
              TreeExitPath T' psi a b a₃ b₃ P₃ ∧
              (∀ x, x ∈ P₁.support → x ∉ P₃.support) ∧
              (∀ x, x ∈ P₂.support → x ∉ P₃.support) ∧
              a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
              b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧
              TreeVertexOrder T' b₂ b₃ ∧
              f₃ ∈ BoundaryColorEdges G psi
                (TreeSequenceVertexSet T') b ∧
              Incident G b₃ f₃ ∧ Sum.inr f₃ ∈ P₃.support ∧
              (∀ (sigma : PartialEdgeColoring E k)
                (U : TreeSequence G e0)
                (corr : CorrespondingExtendedTashkinovTree
                  G k e0 other sigma U),
                IsProperEdgeColoring G sigma →
                IsOneEdgeUncolored sigma e0 →
                StableColoring
                  (other.series.data.tree
                    (Fin.last other.rounds).castSucc)
                  (TashkinovStoredColors other.series.data
                    (Fin.last other.rounds)) psi sigma →
                MaximumProperty corr.replacementETT →
                ∀ (baseU : HierarchyBase corr.replacementETT sigma)
                  (L : TashkinovHierarchy corr.replacementETT baseU)
                  (goodU : GoodHierarchy L),
                  L.dividerCount = K.dividerCount →
                  2 * corr.replacementETT.rounds + 11 ≤
                    (TreeMissingColors sigma
                      (corr.replacementETT.series.data.tree
                        (Fin.last corr.replacementETT.rounds).castSucc)).card →
                  TreeColorSetMinusClosed G sigma U
                    ((HierarchyTerminalStoredColors L).biUnion
                      (goodU.gamma (Fin.last L.dividerCount))) →
                  ∀ (c d : Fin k), c ≠ d →
                    c ∈ TreeMissingColors sigma U →
                    TreeColorSetClosed G sigma U {c} →
                    ∀ (u₁ v₁ u₂ v₂ : V)
                      (Q₁ : (TwoColorIncidenceGraph G sigma c d).Walk
                        (Sum.inl u₁) (Sum.inl v₁))
                      (Q₂ : (TwoColorIncidenceGraph G sigma c d).Walk
                        (Sum.inl u₂) (Sum.inl v₂)),
                      TreeExitPath U sigma c d u₁ v₁ Q₁ →
                      TreeExitPath U sigma c d u₂ v₂ Q₂ →
                      (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
                      u₁ ≠ u₂ →
                      (d ∈ TreeMissingColors sigma U ∨
                        (d ∉ TreeMissingColors sigma U ∧
                          ∃ (u₃ v₃ : V)
                            (Q₃ : (TwoColorIncidenceGraph G sigma c d).Walk
                              (Sum.inl u₃) (Sum.inl v₃)),
                            TreeExitPath U sigma c d u₃ v₃ Q₃ ∧
                            (∀ x, x ∈ Q₁.support → x ∉ Q₃.support) ∧
                            (∀ x, x ∈ Q₂.support → x ∉ Q₃.support) ∧
                            u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
                            Q₁.length + Q₂.length + Q₃.length <
                              P₁.length + P₂.length + P₃.length)) →
                      False))) := by
-- BODY
  sorry
