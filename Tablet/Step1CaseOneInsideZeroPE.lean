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
import Tablet.OrderedTreeUnion
import Tablet.ParallelCommonMissingClosed
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
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
import Tablet.Step1ZeroDividerAnchorPE

-- [TABLET NODE: Step1CaseOneInsideZeroPE]
lemma Step1CaseOneInsideZeroPE {V E : Type*}
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
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) : False := by
-- BODY
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hstar : A = base.core := by
    have hz : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    simp only [A, hz, HierarchyStarredStage, Fin.cases_zero]
  have hcoreT : TreeSequenceInitialSegment base.core T := by
    have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp [hdividerZero]
    simpa only [hi, H.terminalStage] using H.coreInsideFirst
  have initialVertices : ∀ {S U : TreeSequence G e0},
      TreeSequenceInitialSegment S U →
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet U := by
    intro S U hSU v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, _, rfl⟩ := hv
    obtain ⟨hlen, hverts, _⟩ := hSU
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, hverts i⟩
  have hAT : TreeSequenceInitialSegment A T := by simpa [hstar] using hcoreT
  have hsub := initialVertices hAT
  have hb2A : b₂ ∈ TreeSequenceVertexSet A := hinside
  have hb1A : b₁ ∈ TreeSequenceVertexSet A := by
    obtain ⟨r, s, hr, hs, hrs⟩ := horder
    have hb2 := hb2A
    unfold TreeSequenceVertexSet at hb2
    simp only [Finset.mem_image] at hb2
    obtain ⟨t, _, ht⟩ := hb2
    obtain ⟨hlen, hverts, _⟩ := hAT
    have hts : Fin.castLE (Nat.succ_le_succ hlen) t = s :=
      T.vertex_injective (((hverts t).trans ht).trans hs.symm)
    have hrlt : r.val < A.length + 1 := by
      have hvals := congrArg Fin.val hts
      simp only [Fin.val_castLE] at hvals
      omega
    let i : Fin (A.length + 1) := ⟨r.val, hrlt⟩
    have hir : Fin.castLE (Nat.succ_le_succ hlen) i = r := by
      apply Fin.ext
      rfl
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact (hverts i).symm.trans (hir ▸ hr)
  have noBoundary : ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f ≠ some alpha ∧ phi f ≠ some theta := by
    intro f hf
    constructor
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hclosed alpha (by simp)] at hm
      exact Finset.notMem_empty _ hm
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) theta :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hthetaClosed theta (by simp)] at hm
      exact Finset.notMem_empty _ hm
  have boundaryOutside : ∀ {v : V} {f : E},
      v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro v f hv hvf ⟨w, hw, hwf⟩
    have hwv : w ≠ v := by rintro rfl; exact hv hw
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, v, hv, (Sym2.mem_and_mem_iff hwv).mp ⟨hwf, hvf⟩⟩
  let J := TwoColorIncidenceGraph G phi alpha theta
  let Outside : Set (Sum V E) := {z | match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr f => ¬ TreeIncidentEdge T f}
  have outsideStep : ∀ z, z ∈ Outside → ∀ w, J.Adj z w → w ∈ Outside := by
    intro z hz w hzw
    cases z with
    | inl v =>
      cases w with
      | inl w => exact False.elim hzw
      | inr f =>
        intro hf
        have hn := noBoundary (boundaryOutside hz hzw.1 hf)
        exact hzw.2.elim hn.1 hn.2
    | inr f =>
      cases w with
      | inr g => exact False.elim hzw
      | inl v => exact fun hv => hz ⟨v, hv, hzw.1⟩
  let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
    match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr _ => False
  have hout : ∀ z ∈ roots, ∀ v : V,
      Sum.inl v ∈ TwoColorComponent G phi alpha theta z →
      v ∉ TreeSequenceVertexSet T := by
    intro z hz v hv
    have hzOutside : z ∈ Outside := by
      cases z <;> simpa [roots, Outside] using hz
    have hr : J.Reachable z (Sum.inl v) := by
      change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk z at hv
      exact (SimpleGraph.ConnectedComponent.eq.mp hv).symm
    exact hr.mem_subgraphVerts
      (H := (⊤ : J.Subgraph).induce Outside)
      (fun z hz w hzw => ⟨hz, outsideStep z hz w hzw, hzw⟩) hzOutside
  let selected : E → Prop := fun f => ∃ z ∈ roots,
    Sum.inr f ∈ TwoColorComponent G phi alpha theta z
  let nu : PartialEdgeColoring E k := fun f =>
    if selected f then
      if phi f = some alpha then some theta
      else if phi f = some theta then some alpha
      else phi f
    else phi f
  have hrecolor : OutsideKempeRecoloring T phi nu alpha theta :=
    ⟨hthetaAlpha.symm, roots, hout, fun _ => rfl⟩
  have hdetail := OutsideKempeRecoloringStable G e0 T ∅ phi nu alpha theta
    hproper hone hrecolor
  have hfixed : ∀ f, TreeIncidentEdge T f → nu f = phi f := hdetail.2.2.2.2
  have selectedOutside : ∀ (u : V), u ∉ TreeSequenceVertexSet T → ∀ (f : E),
      Incident G u f → (phi f = some alpha ∨ phi f = some theta) → selected f := by
    intro u hu f huf hc
    refine ⟨Sum.inl u, by simp [roots, hu], ?_⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show J.Adj (Sum.inl u) (Sum.inr f) from ⟨huf, hc⟩)).symm
  have betaFixed : ∀ f, nu f = some beta ↔ phi f = some beta := by
    intro f
    by_cases hsel : selected f
    · by_cases ha : phi f = some alpha
      · simp [nu, hsel, ha, hne, hthetaBeta]
      · by_cases ht : phi f = some theta
        · simp [nu, hsel, ha, ht, hne, hthetaBeta, hthetaAlpha]
        · simp [nu, hsel, ha, ht]
    · simp [nu, hsel]
  have pathEdgeOutside : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P →
      ∀ f, Sum.inr f ∈ P.support →
        ∃ w : V, w ∉ TreeSequenceVertexSet T ∧ Incident G w f := by
    intro u v P hExit f hf
    obtain ⟨m, hm, hmle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hmpos : 0 < m := by
      by_contra h
      have hmzero : m = 0 := by omega
      rw [hmzero] at hm
      simp at hm
    have hmlt : m < P.length := by
      by_contra h
      have hmlast : m = P.length := by omega
      rw [hmlast] at hm
      simp at hm
    have hprev := P.adj_getVert_succ (i := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, hm] at hprev
    obtain ⟨w, hw⟩ : ∃ w : V, P.getVert (m - 1) = Sum.inl w := by
      cases hnode : P.getVert (m - 1) with
      | inl w => exact ⟨w, rfl⟩
      | inr e => rw [hnode] at hprev; exact False.elim hprev
    have hnext := P.adj_getVert_succ (i := m) hmlt
    rw [hm] at hnext
    obtain ⟨z, hz⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
      cases hnode : P.getVert (m + 1) with
      | inl z => exact ⟨z, rfl⟩
      | inr e => rw [hnode] at hnext; exact False.elim hnext
    rw [hw] at hprev
    rw [hz] at hnext
    have hwP : Sum.inl w ∈ P.support := by
      rw [← hw]
      exact P.getVert_mem_support _
    have hzP : Sum.inl z ∈ P.support := by
      rw [← hz]
      exact P.getVert_mem_support _
    by_cases hwT : w ∈ TreeSequenceVertexSet T
    · by_cases hzT : z ∈ TreeSequenceVertexSet T
      · have hwv := (hExit.2.2.2.2.2 w hwT).mp hwP
        have hzv := (hExit.2.2.2.2.2 z hzT).mp hzP
        have hverts : P.getVert (m - 1) = P.getVert (m + 1) := by
          rw [hw, hz, hwv, hzv]
        have hi := hExit.1.getVert_injOn
          (show m - 1 ≤ P.length by omega) (show m + 1 ≤ P.length by omega) hverts
        omega
      · exact ⟨z, hzT, hnext.1⟩
    · exact ⟨w, hwT, hprev.1⟩
  have transportExit : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P → v ∈ TreeSequenceVertexSet A →
      ∃ Q : (TwoColorIncidenceGraph G nu theta beta).Walk (Sum.inl u) (Sum.inl v),
        TreeExitPath A nu theta beta u v Q ∧ Q.support = P.support := by
    intro u v P hExit hvA
    have colors : ∀ f, Sum.inr f ∈ P.support →
        (phi f = some alpha ∨ phi f = some beta) →
        nu f = some theta ∨ nu f = some beta := by
      intro f hf hc
      rcases hc with ha | hb
      · obtain ⟨w, hw, hwf⟩ := pathEdgeOutside u v P hExit f hf
        have hs := selectedOutside w hw f hwf (Or.inl ha)
        exact Or.inl (by simp [nu, hs, ha])
      · exact Or.inr ((betaFixed f).mpr hb)
    have hedges : ∀ z, z ∈ P.edges →
        z ∈ (TwoColorIncidenceGraph G nu theta beta).edgeSet := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
        have hadj := (SimpleGraph.mem_edgeSet _).mp (P.edges_subset_edgeSet hz)
        have hx := P.fst_mem_support_of_mem_edges hz
        have hy := P.snd_mem_support_of_mem_edges hz
        apply (SimpleGraph.mem_edgeSet _).mpr
        cases x with
        | inl w =>
          cases y with
          | inl z => exact False.elim hadj
          | inr f => exact ⟨hadj.1, colors f hy hadj.2⟩
        | inr f =>
          cases y with
          | inr g => exact False.elim hadj
          | inl w => exact ⟨hadj.1, colors f hx hadj.2⟩
    let Q := P.transfer (TwoColorIncidenceGraph G nu theta beta) hedges
    have hmissing : theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u := by
      rcases hExit.2.2.2.2.1 with ha | hb
      · left
        have hn : ∀ f, Incident G u f → phi f ≠ some alpha := by
          simpa [MissingColors, PresentColors] using ha
        have hn' : ∀ f, Incident G u f → nu f ≠ some theta := by
          intro f huf hnf
          have hna := hn f huf
          by_cases hs : selected f
          · by_cases ht : phi f = some theta
            · have hnalpha : nu f = some alpha := by simp [nu, hs, hna, ht]
              exact hthetaAlpha (Option.some.inj (hnf.symm.trans hnalpha))
            · exact ht (by simpa [nu, hs, hna, ht] using hnf)
          · have ht : phi f = some theta := by simpa [nu, hs] using hnf
            exact hs (selectedOutside u hExit.2.2.1 f huf (Or.inr ht))
        simpa [MissingColors, PresentColors] using hn'
      · right
        have hn : ∀ f, Incident G u f → phi f ≠ some beta := by
          simpa [MissingColors, PresentColors] using hb
        have hn' : ∀ f, Incident G u f → nu f ≠ some beta := by
          intro f huf hnf
          exact hn f huf ((betaFixed f).mp hnf)
        simpa [MissingColors, PresentColors] using hn'
    refine ⟨Q, ?_, by simp [Q]⟩
    refine ⟨hExit.1.transfer hedges, by simpa [Q] using hExit.2.1,
      (fun hu => hExit.2.2.1 (hsub hu)), hvA, hmissing, ?_⟩
    intro w hw
    simpa [Q] using hExit.2.2.2.2.2 w (hsub hw)
  obtain ⟨Q₁, hQ₁, hQ₁Support⟩ := transportExit a₁ b₁ P₁ hP₁ hb1A
  obtain ⟨Q₂, hQ₂, hQ₂Support⟩ := transportExit a₂ b₂ P₂ hP₂ hb2A
  have hQpaths : ∀ z, z ∈ Q₁.support → z ∉ Q₂.support := by
    simpa only [hQ₁Support, hQ₂Support] using hpaths
  obtain ⟨_, _, _, _, corr, hMPnu, baseNu, K, goodNu, hsame, _⟩ :=
    HierarchyLEMStable G k e0 input T phi nu ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  rcases hsame.1 with ⟨hcore, hcount, _, _, hkind, _⟩
  have hKzero : K.dividerCount = 0 := hcount.symm.trans hdividerZero
  have hstarNu : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
    have hz : Fin.last K.dividerCount = (0 : Fin (K.dividerCount + 1)) := by
      apply Fin.ext
      simp [hKzero]
    rw [hz]
    change baseNu.core = A
    exact hcore.symm.trans hstar.symm
  have hmissingA : TreeMissingColors nu A = TreeMissingColors phi A := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hdetail.2.2.1.2 v (hsub hv)
  have hthetaMissingNu : theta ∈ TreeMissingColors nu A := by
    rw [hmissingA]
    exact hthetaMissing
  have hthetaClosedNu : TreeColorSetClosed G nu A {theta} := by
    intro c hc
    have hclosedOld := hthetaClosedStar c hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hfBoundary, hfColor⟩ := Finset.mem_filter.mp hf
    obtain ⟨u, hu, v, hv, hends⟩ := by
      simpa [BoundaryEdges] using hfBoundary
    have hinc : TreeIncidentEdge T f :=
      ⟨u, hsub hu, by simp [Incident, hends]⟩
    have hfOld : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet A) c :=
      Finset.mem_filter.mpr ⟨hfBoundary, (hfixed f hinc).symm.trans hfColor⟩
    rw [hclosedOld] at hfOld
    exact Finset.notMem_empty _ hfOld
  apply Step1ZeroDividerAnchorPE G k e0 corr.replacementInput T nu
    corr.replacementETT hMPnu (by rw [corr.rungAgreement]; exact hpositive)
    hdetail.1 hdetail.2.1
    (by
      intro input' T' generating' lower hp hlt hm
      apply hlower lower hp _ hm
      rw [← corr.rungAgreement]
      exact hlt)
    baseNu K hKzero theta beta hthetaBeta
    (by simpa only [hstarNu] using hthetaMissingNu)
    (by simpa only [hstarNu] using hthetaClosedNu)
    a₁ b₁ a₂ b₂ Q₁ Q₂
    (by simpa only [hstarNu] using hQ₁)
    (by simpa only [hstarNu] using hQ₂) hQpaths ha
    (hkind.mp hPE)
