import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.Degree
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyLEMStable
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
import Tablet.P2716_T1_OutsideExitTransport
import Tablet.ParallelCommonMissingClosed
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.Step1ZeroDividerAnchorNonPE
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovSeries
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.interchange
import Tablet.sc2

-- [TABLET NODE: Step1CaseOneInsideZeroNonPE]
lemma Step1CaseOneInsideZeroNonPE {V E : Type*}
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
        (((∀ (q : Fin lower.rounds) (v : V),
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
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
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
           ModColoring lower sigma)))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (hdivider : H.dividerCount < q)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (halpha : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∈ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hpaths : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (horder : TreeVertexOrder T b₁ b₂)
    (f₁ f₂ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hinside : b₂ ∈ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (theta : Fin k) (hthetaAlpha : theta ≠ alpha)
    (hthetaBeta : theta ≠ beta)
    (hthetaMissing : theta ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hthetaClosedStar : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {theta})
    (hthetaClosed : TreeColorSetClosed G phi T {theta})
    (hnoSmaller :
      ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T'),
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
          phi sigma →
        MaximumProperty corr.replacementETT →
        ∀ (base' : HierarchyBase corr.replacementETT sigma)
          (K : TashkinovHierarchy corr.replacementETT base')
          (good' : GoodHierarchy K),
          K.dividerCount < H.dividerCount →
          2 * corr.replacementETT.rounds + 11 ≤
            (TreeMissingColors sigma
              (corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc)).card →
          TreeColorSetMinusClosed G sigma T'
            ((HierarchyTerminalStoredColors K).biUnion
              (good'.gamma (Fin.last K.dividerCount))) →
          ∀ (a b : Fin k), a ≠ b →
            a ∈ TreeMissingColors sigma T' →
            TreeColorSetClosed G sigma T' {a} →
            ∀ (u₁ v₁ u₂ v₂ : V)
              (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₁) (Sum.inl v₁))
              (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₂) (Sum.inl v₂)),
              TreeExitPath T' sigma a b u₁ v₁ Q₁ →
              TreeExitPath T' sigma a b u₂ v₂ Q₂ →
              (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
              u₁ ≠ u₂ → False)
    (hdividerZero : H.dividerCount = 0)
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) : False := by
-- BODY
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hstar : A = base.core := by
    have hlast : Fin.last H.dividerCount =
        (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    change HierarchyStarredStage H (Fin.last H.dividerCount) = base.core
    rw [hlast]
    rfl
  have hprefix : TreeSequenceInitialSegment A T := by
    rw [hstar, base.nonparallel hnonPE]
    exact ett.abovePenultimate
  have hsub : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hprefix
  have hb₁A : b₁ ∈ TreeSequenceVertexSet A := by
    obtain ⟨hlen, hvertices, _⟩ := hprefix
    obtain ⟨i, j, hi, hj, hij⟩ := horder
    obtain ⟨t, ht⟩ : ∃ t : Fin (A.length + 1), A.vertex t = b₂ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] using hinside
    have hjcast : j = Fin.castLE (Nat.succ_le_succ hlen) t :=
      T.vertex_injective (hj.trans ((hvertices t).trans ht).symm)
    have hiBound : i.val < A.length + 1 := by
      have hjval := congrArg Fin.val hjcast
      simp only [Fin.val_castLE] at hjval
      omega
    let iA : Fin (A.length + 1) := ⟨i.val, hiBound⟩
    have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iA = i := by
      apply Fin.ext
      rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨iA, ?_⟩
    calc
      A.vertex iA = T.vertex (Fin.castLE (Nat.succ_le_succ hlen) iA) :=
        (hvertices iA).symm
      _ = T.vertex i := by rw [hiCast]
      _ = b₁ := hi
  obtain ⟨sigma, hrecolor, hproperSigma, honeSigma, hsubset, _, hexits⟩ :=
    P2716_T1_OutsideExitTransport G T phi alpha theta beta hthetaAlpha.symm
      hne hthetaBeta hproper hone hclosed hthetaClosed
  obtain ⟨Q₁, hQ₁, hsupport₁, _⟩ :=
    hexits A hsub a₁ b₁ P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, hsupport₂, _⟩ :=
    hexits A hsub a₂ b₂ P₂ hP₂ hinside
  have hQpaths : ∀ x, x ∈ Q₁.support → x ∉ Q₂.support := by
    simpa only [hsupport₁, hsupport₂] using hpaths
  obtain ⟨_, _, _, _, corr, hMPsigma, baseSigma, K, goodSigma, hsame, _⟩ :=
    HierarchyLEMStable G k e0 input T phi sigma ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  obtain ⟨hcores, hcounts, _, _, _, _⟩ := hsame.1
  have hKzero : K.dividerCount = 0 := hcounts.symm.trans hdividerZero
  have hKstar : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
    have hlast : Fin.last K.dividerCount =
        (0 : Fin (K.dividerCount + 1)) := by
      apply Fin.ext
      simp [hKzero]
    rw [hlast]
    exact hcores.symm.trans hstar.symm
  have hmissingSigma : theta ∈ TreeMissingColors sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) := by
    rw [hKstar, (hsubset A hsub).2.1]
    exact hthetaMissing
  have hclosedSigma : TreeColorSetClosed G sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta} := by
    rw [hKstar]
    exact (hsubset A hsub).2.2 theta hthetaClosedStar
  have lastKindAgreement : ∀ {m n : ℕ}
      (S₁ : TashkinovSeries G k m e0 corr.replacementInput)
      (S₂ : TashkinovSeries G k n e0 corr.replacementInput),
      m = n → HEq S₁ S₂ →
      S₁.data.kind (Fin.last m) = S₂.data.kind (Fin.last n) := by
    intro m n S₁ S₂ hmn hseries
    cases hmn
    cases hseries
    rfl
  have hkind : corr.replacementETT.series.data.kind
      (Fin.last corr.replacementETT.rounds) =
      ett.series.data.kind (Fin.last ett.rounds) :=
    (lastKindAgreement corr.replacementETT.series corr.replacementSeries
      corr.rungAgreement corr.seriesPresentation).trans
      (corr.extensionKindsAgree (Fin.last ett.rounds))
  have hnonSigma : corr.replacementETT.series.data.kind
      (Fin.last corr.replacementETT.rounds) ≠
      some TashkinovExtensionKind.PE := by
    rw [hkind]
    exact hnonPE
  exact Step1ZeroDividerAnchorNonPE G k e0 corr.replacementInput T sigma
    corr.replacementETT hMPsigma
    (by simpa only [corr.rungAgreement] using hpositive)
    hproperSigma honeSigma
    (fun lower hp hlt hmp => hlower lower hp
      (by simpa only [corr.rungAgreement] using hlt) hmp)
    baseSigma K hKzero theta beta hthetaBeta hmissingSigma hclosedSigma
    a₁ b₁ a₂ b₂ Q₁ Q₂
    (by simpa only [hKstar] using hQ₁)
    (by simpa only [hKstar] using hQ₂) hQpaths ha hnonSigma
