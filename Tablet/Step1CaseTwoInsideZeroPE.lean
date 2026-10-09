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
import Tablet.OrderedTreeUnion
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
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
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: Step1CaseTwoInsideZeroPE]
lemma Step1CaseTwoInsideZeroPE {V E : Type*}
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
    (hinside : b₃ ∈ TreeSequenceVertexSet
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
  have hlast : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
    Fin.ext (by simp [hdividerZero])
  have hAcore : A = base.core := by
    simp [A, hlast, HierarchyStarredStage]
  have hfirst : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
      Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hdividerZero])
  have hAT : TreeSequenceInitialSegment A T := by
    simpa only [hAcore, hfirst, H.terminalStage] using H.coreInsideFirst
  have hAsub := TreeSequenceInitialSegmentVertexSetSubset hAT
  have beforeInside : ∀ {u v : V}, TreeVertexOrder T u v →
      v ∈ TreeSequenceVertexSet A → u ∈ TreeSequenceVertexSet A := by
    intro u v huv hv
    obtain ⟨i, j, hi, hj, hij⟩ := huv
    obtain ⟨r, hr⟩ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] using hv
    have hrj : Fin.castLE (Nat.succ_le_succ hAT.1) r = j :=
      T.vertex_injective ((hAT.2.1 r).trans (hr.trans hj.symm))
    have hval : r.val = j.val := congrArg Fin.val hrj
    let s : Fin (A.length + 1) := ⟨i.val, by have := r.isLt; omega⟩
    have hsi : Fin.castLE (Nat.succ_le_succ hAT.1) s = i := Fin.ext rfl
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨s, (hAT.2.1 s).symm.trans (hsi ▸ hi)⟩
  have hb₃A : b₃ ∈ TreeSequenceVertexSet A := hinside
  have hb₂A := beforeInside horder₂₃ hb₃A
  have hb₁A := beforeInside horder₁₂ hb₂A
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
  have boundaryOfOutside : ∀ {v : V} {f : E},
      v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro v f hv hvf ⟨w, hw, hwf⟩
    have hwv : w ≠ v := by intro h; exact hv (h ▸ hw)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, v, hv, (Sym2.mem_and_mem_iff hwv).mp ⟨hwf, hvf⟩⟩
  let J := TwoColorIncidenceGraph G phi alpha theta
  let S : Set (Sum V E) := {z | match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr f => ¬ TreeIncidentEdge T f}
  have outsideStep : ∀ z, z ∈ S → ∀ w, J.Adj z w → w ∈ S := by
    intro z hz w hzw
    cases z with
    | inl v =>
        cases w with
        | inl u => exact False.elim hzw
        | inr f =>
            intro hfT
            have hb := noBoundary (boundaryOfOutside hz hzw.1 hfT)
            exact hzw.2.elim hb.1 hb.2
    | inr f =>
        cases w with
        | inr g => exact False.elim hzw
        | inl v => exact fun hv => hz ⟨v, hv, hzw.1⟩
  let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
    match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr _ => False
  let selected : E → Prop := fun f =>
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z
  let nu : PartialEdgeColoring E k := fun f =>
    if selected f then
      if phi f = some alpha then some theta
      else if phi f = some theta then some alpha else phi f
    else phi f
  have outsideComponents : ∀ z ∈ roots, ∀ v : V,
      Sum.inl v ∈ TwoColorComponent G phi alpha theta z →
      v ∉ TreeSequenceVertexSet T := by
    intro z hz v hv
    have hzS : z ∈ S := by
      cases z <;> simpa [roots, S] using hz
    have hr : J.Reachable z (Sum.inl v) := by
      change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk z at hv
      exact (SimpleGraph.ConnectedComponent.eq.mp hv).symm
    exact hr.mem_subgraphVerts
      (H := (⊤ : J.Subgraph).induce S)
      (fun x hx y hxy => ⟨hx, outsideStep x hx y hxy, hxy⟩) hzS
  have hrecolor : OutsideKempeRecoloring T phi nu alpha theta :=
    ⟨hthetaAlpha.symm, roots, outsideComponents, fun _ => rfl⟩
  have selectedOfOutside : ∀ (u : V), u ∉ TreeSequenceVertexSet T →
      ∀ (f : E), Incident G u f →
      (phi f = some alpha ∨ phi f = some theta) → selected f := by
    intro u hu f huf hcolor
    refine ⟨Sum.inl u, by simp [roots, hu], ?_⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show J.Adj (Sum.inl u) (Sum.inr f) from ⟨huf, hcolor⟩)).symm
  have betaFixed : ∀ f : E, nu f = some beta ↔ phi f = some beta := by
    intro f
    by_cases hs : selected f <;> by_cases ha : phi f = some alpha <;>
      by_cases ht : phi f = some theta <;>
      simp [nu, hs, ha, ht, hne, hthetaBeta, hthetaAlpha]
  have thetaPreimage : ∀ (u : V), u ∉ TreeSequenceVertexSet T →
      ∀ (f : E), Incident G u f →
      (nu f = some theta ↔ phi f = some alpha) := by
    intro u hu f huf
    by_cases ha : phi f = some alpha
    · have hs := selectedOfOutside u hu f huf (Or.inl ha)
      simp [nu, hs, ha]
    · by_cases ht : phi f = some theta
      · have hs := selectedOfOutside u hu f huf (Or.inr ht)
        simp [nu, hs, ha, ht, hthetaAlpha.symm]
      · by_cases hs : selected f <;> simp [nu, hs, ha, ht]
  have missingIff : ∀ (p : PartialEdgeColoring E k) (v : V) (c : Fin k),
      c ∈ MissingColors G p v ↔ ∀ f, Incident G v f → p f ≠ some c := by
    intro p v c
    simp [MissingColors, PresentColors]
  have remoteMissing : ∀ u, u ∉ TreeSequenceVertexSet T →
      (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) →
      theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u := by
    intro u hu hm
    rcases hm with hm | hm
    · left
      apply (missingIff nu u theta).mpr
      intro f huf hf
      exact (missingIff phi u alpha).mp hm f huf
        ((thetaPreimage u hu f huf).mp hf)
    · right
      apply (missingIff nu u beta).mpr
      intro f huf hf
      exact (missingIff phi u beta).mp hm f huf ((betaFixed f).mp hf)
  have pathEdgeOutside : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P →
      ∀ f : E, Sum.inr f ∈ P.support →
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
    obtain ⟨w, hwPrev⟩ : ∃ w : V, P.getVert (m - 1) = Sum.inl w := by
      cases hnode : P.getVert (m - 1) with
      | inl w => exact ⟨w, rfl⟩
      | inr e => rw [hnode] at hprev; exact False.elim hprev
    have hnext := P.adj_getVert_succ (i := m) hmlt
    rw [hm] at hnext
    obtain ⟨z, hzNext⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
      cases hnode : P.getVert (m + 1) with
      | inl z => exact ⟨z, rfl⟩
      | inr e => rw [hnode] at hnext; exact False.elim hnext
    rw [hwPrev] at hprev
    rw [hzNext] at hnext
    by_cases hwT : w ∈ TreeSequenceVertexSet T
    · by_cases hzT : z ∈ TreeSequenceVertexSet T
      · have hwv : w = v := (hExit.2.2.2.2.2 w hwT).mp (by
          rw [← hwPrev]; exact P.getVert_mem_support _)
        have hzv : z = v := (hExit.2.2.2.2.2 z hzT).mp (by
          rw [← hzNext]; exact P.getVert_mem_support _)
        have heq : P.getVert (m - 1) = P.getVert (m + 1) := by
          rw [hwPrev, hzNext, hwv, hzv]
        have hindices := hExit.1.getVert_injOn
          (show m - 1 ≤ P.length by omega) (show m + 1 ≤ P.length by omega) heq
        omega
      · exact ⟨z, hzT, hnext.1⟩
    · exact ⟨w, hwT, hprev.1⟩
  have transferExit : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P → v ∈ TreeSequenceVertexSet A →
      ∃ Q : (TwoColorIncidenceGraph G nu theta beta).Walk
          (Sum.inl u) (Sum.inl v),
        TreeExitPath A nu theta beta u v Q ∧ Q.support = P.support := by
    intro u v P hExit hvA
    have colors : ∀ f, Sum.inr f ∈ P.support →
        (phi f = some alpha ∨ phi f = some beta) →
        nu f = some theta ∨ nu f = some beta := by
      intro f hf hc
      rcases hc with ha | hb
      · obtain ⟨w, hwT, hwf⟩ := pathEdgeOutside u v P hExit f hf
        have hs := selectedOfOutside w hwT f hwf (Or.inl ha)
        exact Or.inl (by simp [nu, hs, ha])
      · exact Or.inr ((betaFixed f).mpr hb)
    have edges : ∀ z, z ∈ P.edges → z ∈ (TwoColorIncidenceGraph G nu theta beta).edgeSet := by
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
    let Q := P.transfer (TwoColorIncidenceGraph G nu theta beta) edges
    refine ⟨Q, ?_, by simp [Q]⟩
    refine ⟨hExit.1.transfer edges, by simpa [Q] using hExit.2.1,
      fun huA => hExit.2.2.1 (hAsub huA), hvA,
      remoteMissing u hExit.2.2.1 hExit.2.2.2.2.1, ?_⟩
    intro w hw
    simpa [Q] using hExit.2.2.2.2.2 w (hAsub hw)
  obtain ⟨Q₁, hQ₁, hs₁⟩ := transferExit a₁ b₁ P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, hs₂⟩ := transferExit a₂ b₂ P₂ hP₂ hb₂A
  obtain ⟨Q₃, hQ₃, hs₃⟩ := transferExit a₃ b₃ P₃ hP₃ hb₃A
  obtain ⟨hnuProper, hnuOne, hnuStable, hnuInvariant,
    corr, hnuMP, baseNu, K, goodNu, hsame, _⟩ :=
    HierarchyLEMStable G k e0 input T phi nu ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  have hfixed := (OutsideKempeRecoloringStable G e0 T ∅ phi nu alpha theta
    hproper hone hrecolor).2.2.2.2
  rcases hsame.1 with ⟨hcore, hcount, _, _, hkind, _⟩
  have hKzero : K.dividerCount = 0 := hcount.symm.trans hdividerZero
  have hKlast : Fin.last K.dividerCount = (0 : Fin (K.dividerCount + 1)) :=
    Fin.ext (by simp [hKzero])
  have hKcore : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
    rw [hKlast]
    change baseNu.core = A
    exact hcore.symm.trans hAcore.symm
  have hthetaNu : theta ∈ TreeMissingColors nu A := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hthetaMissing
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, ?_⟩
    rw [hnuInvariant.2 v (hAsub hv)]
    exact hm
  have hthetaNuClosed : TreeColorSetClosed G nu A {theta} := by
    intro c hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet A) ∧
        nu f = some c := by simpa [BoundaryColorEdges] using hf
    obtain ⟨u, hu, v, hv, he⟩ := by
      simpa [BoundaryEdges] using hboundary.1
    have huf : Incident G u f := by simp [Incident, he]
    have hold : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet A) c := by
      apply Finset.mem_filter.mpr
      exact ⟨hboundary.1, (hfixed f ⟨u, hAsub hu, huf⟩).symm.trans hboundary.2⟩
    rw [hthetaClosedStar c hc] at hold
    exact Finset.notMem_empty _ hold
  -- The closed PE anchor performs the second exchange on this transported base.
  apply Step1ZeroDividerAnchorPE G k e0 corr.replacementInput T nu
    corr.replacementETT hnuMP (by simpa [corr.rungAgreement] using hpositive)
    hnuProper hnuOne (fun lower hp hr hm =>
      hlower lower hp (by simpa [corr.rungAgreement] using hr) hm)
    baseNu K hKzero theta beta hthetaBeta
    (by simpa only [hKcore] using hthetaNu)
    (by simpa only [hKcore] using hthetaNuClosed)
    a₂ b₂ a₃ b₃ Q₂ Q₃
    (by simpa only [hKcore] using hQ₂)
    (by simpa only [hKcore] using hQ₃)
    (fun z hz => by rw [hs₂] at hz; rw [hs₃]; exact hpaths₂₃ z hz)
    ha₂₃ (hkind.mp hPE)
