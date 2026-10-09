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
import Tablet.OutsideTreeColorSwap
import Tablet.ParallelCommonMissingClosed
import Tablet.PresentColors
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

-- [TABLET NODE: Step1CaseTwoInsideZeroNonPE]
lemma Step1CaseTwoInsideZeroNonPE {V E : Type*}
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
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) : False := by
-- BODY
  classical
  let r : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hr : r.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [r]
    omega
  let N := ett.series.data.tree r.succ.castSucc
  let D := TashkinovStoredColors ett.series.data r.castSucc
  let previous := ett.series.data.coloring r.castSucc
  have hcolor : ett.series.data.coloring r.succ = phi := by
    rw [hr]
    exact ett.generatingColoring.symm
  have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) = N := by
    have hz : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    rw [hz]
    change base.core = N
    simpa only [N, hr] using base.nonparallel hnonPE
  have hprefix : TreeSequenceInitialSegment N T := by
    convert ett.abovePenultimate using 1
    change ett.series.data.tree r.succ.castSucc = _
    congr 1
    apply Fin.ext
    simp [r]
    omega
  have hsub : TreeSequenceVertexSet N ⊆ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hprefix
  have earlier_inside : ∀ {u v : V}, TreeVertexOrder T u v →
      v ∈ TreeSequenceVertexSet N → u ∈ TreeSequenceVertexSet N := by
    intro u v huv hv
    obtain ⟨hlen, hvertices, _⟩ := hprefix
    obtain ⟨i, j, hi, hj, hij⟩ := huv
    obtain ⟨t, ht⟩ : ∃ t, N.vertex t = v := by
      simpa [TreeSequenceVertexSet] using hv
    have hjt : j = Fin.castLE (Nat.succ_le_succ hlen) t :=
      T.vertex_injective (hj.trans ((hvertices t).trans ht).symm)
    have hil : i.val < N.length + 1 := by
      have htlt := t.isLt
      rw [hjt] at hij
      simp only [Fin.val_castLE] at hij
      omega
    let s : Fin (N.length + 1) := ⟨i.val, hil⟩
    have hsi : Fin.castLE (Nat.succ_le_succ hlen) s = i := by
      apply Fin.ext
      rfl
    have hs : N.vertex s = u := by
      rw [← hvertices s, hsi]
      exact hi
    simpa [TreeSequenceVertexSet] using (show ∃ s, N.vertex s = u from ⟨s, hs⟩)
  have hb3 : b₃ ∈ TreeSequenceVertexSet N := by simpa only [hstar] using hinside
  have hb2 := earlier_inside horder₂₃ hb3
  have hb1 := earlier_inside horder₁₂ hb2
  have boundary_crossing : ∀ {S : TreeSequence G e0} {f : E} {v w : V},
      v ∈ TreeSequenceVertexSet S → w ∉ TreeSequenceVertexSet S →
      Incident G v f → Incident G w f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
    intro S f v w hv hw hvf hwf
    have hvw : v ≠ w := by intro he; exact hw (he ▸ hv)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, w, hw, (Sym2.mem_and_mem_iff hvw).mp ⟨hvf, hwf⟩⟩
  have no_boundary : ∀ {S : TreeSequence G e0} {psi : PartialEdgeColoring E k}
      {d : Fin k}, TreeColorSetClosed G psi S {d} →
      ∀ {f}, f ∈ BoundaryEdges G (TreeSequenceVertexSet S) → psi f ≠ some d := by
    intro S psi d hc f hf hfd
    have hm : f ∈ BoundaryColorEdges G psi (TreeSequenceVertexSet S) d :=
      Finset.mem_filter.mpr ⟨hf, hfd⟩
    rw [hc d (Finset.mem_singleton_self d)] at hm
    simpa using hm
  -- The pointwise outside swap is an exchange of full outside components.
  have outside_recolor : ∀ (S : TreeSequence G e0) (psi : PartialEdgeColoring E k)
      (a c : Fin k), a ≠ c → TreeColorSetClosed G psi S {a} →
      TreeColorSetClosed G psi S {c} →
      OutsideKempeRecoloring S psi (OutsideTreeColorSwap S psi a c) a c := by
    intro S psi a c hac hca hcc
    let J := TwoColorIncidenceGraph G psi a c
    let Outside : Sum V E → Prop
      | Sum.inl v => v ∉ TreeSequenceVertexSet S
      | Sum.inr f => ¬ TreeIncidentEdge S f
    have step {z z' : Sum V E} (hzz' : J.Adj z z') (hz : Outside z) : Outside z' := by
      cases z with
      | inl v =>
        cases z' with
        | inl w => simpa [J, TwoColorIncidenceGraph] using hzz'
        | inr f =>
          obtain ⟨hinc, hcol⟩ := hzz'
          intro hf
          obtain ⟨w, hw, hwf⟩ := hf
          have hb := boundary_crossing hw hz hwf hinc
          exact hcol.elim (no_boundary hca hb) (no_boundary hcc hb)
      | inr f =>
        cases z' with
        | inl v => exact fun hv => hz ⟨v, hv, hzz'.1⟩
        | inr g => simpa [J, TwoColorIncidenceGraph] using hzz'
    have component_outside : ∀ (u : V), u ∉ TreeSequenceVertexSet S →
        ∀ z, z ∈ TwoColorComponent G psi a c (Sum.inl u) → Outside z := by
      intro u hu z hz
      have hreach : J.Reachable (Sum.inl u) z := by
        apply SimpleGraph.ConnectedComponent.exact
        change J.connectedComponentMk z = J.connectedComponentMk (Sum.inl u) at hz
        exact hz.symm
      clear hz
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      induction hreach with
      | refl => exact hu
      | tail hreach hlast ih => exact step hlast ih
    let roots : Finset (Sum V E) :=
      (Finset.univ.filter fun v : V => v ∉ TreeSequenceVertexSet S).image Sum.inl
    have selected {f : E} (hcol : psi f = some a ∨ psi f = some c) :
        (∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G psi a c z) ↔
          ¬ TreeIncidentEdge S f := by
      constructor
      · rintro ⟨z, hz, hf⟩
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        exact component_outside u (Finset.mem_filter.mp hu).2 (Sum.inr f) hf
      · intro hf
        induction he : G.ends f using Sym2.inductionOn with
        | _ u v =>
          have hinc : Incident G u f := by simp [Incident, he]
          have hu : u ∉ TreeSequenceVertexSet S := fun hu => hf ⟨u, hu, hinc⟩
          refine ⟨Sum.inl u, Finset.mem_image.mpr ⟨u, by simp [hu], rfl⟩, ?_⟩
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              (show J.Adj (Sum.inl u) (Sum.inr f) from ⟨hinc, hcol⟩)).symm
    refine ⟨hac, roots, ?_, ?_⟩
    · intro z hz v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact component_outside u (Finset.mem_filter.mp hu).2 (Sum.inl v) hv
    · intro f
      by_cases ha : psi f = some a
      · have hs := selected (Or.inl ha)
        by_cases ht : TreeIncidentEdge S f <;>
          simp [OutsideTreeColorSwap, ht, ha, hs]
      · by_cases hc : psi f = some c
        · have hs := selected (Or.inr hc)
          by_cases ht : TreeIncidentEdge S f <;>
            simp [OutsideTreeColorSwap, ht, ha, hc, hs]
        · simp [OutsideTreeColorSwap, ha, hc]
  have stable_outside : ∀ (S : TreeSequence G e0) (C : Finset (Fin k))
      (psi : PartialEdgeColoring E k) (a c : Fin k),
      IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 →
      TreeColorSetClosed G psi S {a} → TreeColorSetClosed G psi S {c} →
      IsProperEdgeColoring G (OutsideTreeColorSwap S psi a c) ∧
      IsOneEdgeUncolored (OutsideTreeColorSwap S psi a c) e0 ∧
      StableColoring S C psi (OutsideTreeColorSwap S psi a c) ∧
      ∀ f, TreeIncidentEdge S f → OutsideTreeColorSwap S psi a c f = psi f := by
    intro S C psi a c hp ho ha hc
    by_cases hac : a = c
    · have he : OutsideTreeColorSwap S psi a c = psi := by
        funext f
        by_cases ht : TreeIncidentEdge S f <;> by_cases hf : psi f = some c <;>
          simp [OutsideTreeColorSwap, ht, hac, hf]
      rw [he]
      exact ⟨hp, ho, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    · obtain ⟨hp', ho', hs, _, hf⟩ := OutsideKempeRecoloringStable G e0 S C psi
        (OutsideTreeColorSwap S psi a c) a c hp ho (outside_recolor S psi a c hac ha hc)
      exact ⟨hp', ho', hs, hf⟩
  have path_boundary : ∀ {S : TreeSequence G e0} {psi : PartialEdgeColoring E k}
      {a d : Fin k} {u v : V}
      (P : (TwoColorIncidenceGraph G psi a d).Walk (Sum.inl u) (Sum.inl v)),
      TreeExitPath S psi a d u v P → ∀ {f}, Sum.inr f ∈ P.support →
      TreeIncidentEdge S f → f ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
    intro S psi a d u v P he f hf hftree
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hnpos : 0 < n := by
      by_contra h
      have hz : n = 0 := by omega
      rw [hz] at hn
      simp at hn
    have hnlt : n < P.length := by
      by_contra h
      have hz : n = P.length := by omega
      rw [hz] at hn
      simp at hn
    have hprev := P.adj_getVert_succ (i := n - 1) (by omega)
    have hnext := P.adj_getVert_succ (i := n) hnlt
    have hnsub : n - 1 + 1 = n := by omega
    rw [hnsub, hn] at hprev
    rw [hn] at hnext
    cases hy : P.getVert (n - 1) with
    | inr g => rw [hy] at hprev; simp [TwoColorIncidenceGraph] at hprev
    | inl y =>
      rw [hy] at hprev
      cases hz : P.getVert (n + 1) with
      | inr g => rw [hz] at hnext; simp [TwoColorIncidenceGraph] at hnext
      | inl z =>
        rw [hz] at hnext
        have hyz : y ≠ z := by
          intro hyz
          have heq : P.getVert (n - 1) = P.getVert (n + 1) := by rw [hy, hz, hyz]
          have hi := he.1.getVert_injOn (show n - 1 ≤ P.length by omega)
            (show n + 1 ≤ P.length by omega) heq
          omega
        have hyS : Sum.inl y ∈ P.support := by rw [← hy]; exact P.getVert_mem_support _
        have hzS : Sum.inl z ∈ P.support := by rw [← hz]; exact P.getVert_mem_support _
        have hends : G.ends f = Sym2.mk y z :=
          (Sym2.mem_and_mem_iff hyz).mp ⟨hprev.1, hnext.1⟩
        obtain ⟨x, hx, hxf⟩ := hftree
        have hxy : x = y ∨ x = z := by simpa [Incident, hends] using hxf
        rcases hxy with hxy | hxz
        · subst x
          refine boundary_crossing hx ?_ hprev.1 hnext.1
          intro hzT
          exact hyz (((he.2.2.2.2.2 y hx).mp hyS).trans
            ((he.2.2.2.2.2 z hzT).mp hzS).symm)
        · subst x
          refine boundary_crossing hx ?_ hnext.1 hprev.1
          intro hyT
          exact hyz (((he.2.2.2.2.2 y hyT).mp hyS).trans
            ((he.2.2.2.2.2 z hx).mp hzS).symm)
  have transfer_exit : ∀ (S U : TreeSequence G e0)
      (psi : PartialEdgeColoring E k) (a c d : Fin k),
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet U → a ≠ d → c ≠ d →
      TreeColorSetClosed G psi U {a} → TreeColorSetClosed G psi U {c} →
      ∀ {u v : V}
        (P : (TwoColorIncidenceGraph G psi a d).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath U psi a d u v P → v ∈ TreeSequenceVertexSet S →
        ∃ Q : (TwoColorIncidenceGraph G (OutsideTreeColorSwap U psi a c) c d).Walk
            (Sum.inl u) (Sum.inl v),
          TreeExitPath S (OutsideTreeColorSwap U psi a c) c d u v Q ∧
          Q.support = P.support := by
    intro S U psi a c d hSU had hcd ha hc u v P he hv
    let mu := OutsideTreeColorSwap U psi a c
    have fixed {f : E} (hf : TreeIncidentEdge U f) : mu f = psi f := by
      simp [mu, OutsideTreeColorSwap, hf]
    have outside_color (f : E) (hf : ¬ TreeIncidentEdge U f) :
        (mu f = some c → psi f = some a) ∧
        (mu f = some d ↔ psi f = some d) := by
      constructor
      · intro hmc
        by_cases hfa : psi f = some a
        · exact hfa
        · by_cases hfc : psi f = some c
          · have hca : c ≠ a := by
              intro heq
              exact hfa (hfc.trans (congrArg some heq))
            have hac : a = c := by
              apply Option.some.inj
              simpa [mu, OutsideTreeColorSwap, hf, hfa, hfc, hca] using hmc
            exact hfc.trans (congrArg some hac.symm)
          · have hfc' : psi f = some c := by
              simpa [mu, OutsideTreeColorSwap, hf, hfa, hfc] using hmc
            exact (hfc hfc').elim
      · by_cases hfa : psi f = some a
        · simp [mu, OutsideTreeColorSwap, hf, hfa, had, hcd]
        · by_cases hfc : psi f = some c
          · have hca : c ≠ a := by
              intro heq
              exact hfa (hfc.trans (congrArg some heq))
            simp [mu, OutsideTreeColorSwap, hf, hfa, hfc, hca, had, hcd]
          · simp [mu, OutsideTreeColorSwap, hf, hfa, hfc]
    have remote_missing : c ∈ MissingColors G mu u ∨ d ∈ MissingColors G mu u := by
      rcases he.2.2.2.2.1 with hua | hud
      · left
        have hnot : a ∉ PresentColors G psi u := by simpa [MissingColors] using hua
        change c ∈ Finset.univ \ PresentColors G mu u
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hpres
        obtain ⟨f, hinc, hfc⟩ : ∃ f, Incident G u f ∧ mu f = some c := by
          simpa [PresentColors] using hpres
        by_cases hf : TreeIncidentEdge U f
        · obtain ⟨w, hw, hwf⟩ := hf
          exact no_boundary hc (boundary_crossing hw he.2.2.1 hwf hinc)
            ((fixed ⟨w, hw, hwf⟩).symm.trans hfc)
        · apply hnot
          simpa [PresentColors] using (show ∃ f, Incident G u f ∧ psi f = some a from
            ⟨f, hinc, (outside_color f hf).1 hfc⟩)
      · right
        have hnot : d ∉ PresentColors G psi u := by simpa [MissingColors] using hud
        change d ∈ Finset.univ \ PresentColors G mu u
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hpres
        obtain ⟨f, hinc, hfd⟩ : ∃ f, Incident G u f ∧ mu f = some d := by
          simpa [PresentColors] using hpres
        have hfd' : psi f = some d := by
          by_cases hf : TreeIncidentEdge U f
          · exact (fixed hf).symm.trans hfd
          · exact (outside_color f hf).2.mp hfd
        apply hnot
        simpa [PresentColors] using (show ∃ f, Incident G u f ∧ psi f = some d from
          ⟨f, hinc, hfd'⟩)
    have preserve : ∀ {v : V} {f : E}, Sum.inr f ∈ P.support →
        (TwoColorIncidenceGraph G psi a d).Adj (Sum.inl v) (Sum.inr f) →
        (TwoColorIncidenceGraph G mu c d).Adj (Sum.inl v) (Sum.inr f) := by
      intro w f hf hadj
      refine ⟨hadj.1, ?_⟩
      by_cases ht : TreeIncidentEdge U f
      · have hfd := hadj.2.resolve_left (no_boundary ha (path_boundary P he hf ht))
        exact Or.inr ((fixed ht).trans hfd)
      · rcases hadj.2 with hfa | hfd
        · exact Or.inl (by simp [mu, OutsideTreeColorSwap, ht, hfa])
        · exact Or.inr ((outside_color f ht).2.mpr hfd)
    have hedges : ∀ z, z ∈ P.edges → z ∈ (TwoColorIncidenceGraph G mu c d).edgeSet := by
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
          | inl w' => simpa [TwoColorIncidenceGraph] using hadj
          | inr f => exact preserve hy hadj
        | inr f =>
          cases y with
          | inl w => exact (preserve hx hadj.symm).symm
          | inr g => simpa [TwoColorIncidenceGraph] using hadj
    let Q := P.transfer (TwoColorIncidenceGraph G mu c d) hedges
    have hlength : Q.length = P.length := P.length_transfer hedges
    have hsupport : Q.support = P.support := P.support_transfer hedges
    refine ⟨Q, ⟨he.1.transfer hedges, ?_, ?_, hv, remote_missing, ?_⟩, ?_⟩
    · change 2 ≤ Q.length
      rw [hlength]
      exact he.2.1
    · exact fun hu => he.2.2.1 (hSU hu)
    · intro w hw
      change Sum.inl w ∈ Q.support ↔ w = v
      rw [hsupport]
      exact he.2.2.2.2.2 w (hSU hw)
    · exact hsupport
  let nu := OutsideTreeColorSwap T phi alpha theta
  obtain ⟨hnuProper, hnuOne, hnuStable, hnuFixed⟩ :=
    stable_outside T D phi alpha theta hproper hone hclosed hthetaClosed
  have hnuStableN : StableColoring N D phi nu :=
    ⟨fun f hf _ => by
      obtain ⟨v, hv, hinc⟩ := hf
      exact hnuFixed f ⟨v, hsub hv, hinc⟩,
      fun v hv => hnuStable.2 v (hsub hv)⟩
  obtain ⟨Q1, hQ1, hsQ1⟩ := transfer_exit N T phi alpha theta beta hsub hne
    hthetaBeta hclosed hthetaClosed P₁ hP₁ hb1
  obtain ⟨Q2, hQ2, hsQ2⟩ := transfer_exit N T phi alpha theta beta hsub hne
    hthetaBeta hclosed hthetaClosed P₂ hP₂ hb2
  obtain ⟨Q3, hQ3, hsQ3⟩ := transfer_exit N T phi alpha theta beta hsub hne
    hthetaBeta hclosed hthetaClosed P₃ hP₃ hb3
  -- Read the actual terminal certificate to obtain the previous control set.
  have terminal : IsProperEdgeColoring G previous ∧ IsOneEdgeUncolored previous e0 ∧
      ColoredVertexSetClosed G previous (TreeSequenceVertexSet N) ∧
      StableColoring N D previous phi := by
    have cert := ett.series.certified r.succ
    generalize hslot : r.succ = slot at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero r hslot).elim
    | SE i previousProper previousOne previousClosed previousNotStronglyClosed noRevisiting
        choice seriesAlternative currentColoring currentStored currentEdges currentKind
        currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have h := congrArg Fin.val hslot
        simp only [Fin.val_succ] at h
        omega
      subst i
      have hselected : choice.selected = phi := currentColoring.symm.trans hcolor
      refine ⟨previousProper, previousOne, previousClosed, ?_⟩
      rw [← hselected]
      exact choice.selectedStable
    | RE i previousProper previousOne previousClosed previousNotStronglyClosed available
        currentColoring currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have h := congrArg Fin.val hslot
        simp only [Fin.val_succ] at h
        omega
      subst i
      have he : previous = phi := currentColoring.symm.trans hcolor
      refine ⟨previousProper, previousOne, previousClosed, ?_⟩
      rw [he]
      exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    | PE i previousProper previousOne previousClosed previousNotStronglyClosed noRevisiting
        choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
        secondStableOne secondStableRelation exitWitness currentColoring currentProper
        currentOne currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have h := congrArg Fin.val hslot
        simp only [Fin.val_succ] at h
        omega
      subst i
      exact (hnonPE (by simpa only [hr] using currentKind)).elim
  have hnuPrevious : StableColoring N D previous nu :=
    (sc2 G e0 N D).trans (x := ⟨previous, terminal.1, terminal.2.1⟩)
      (y := ⟨phi, hproper, hone⟩) (z := ⟨nu, hnuProper, hnuOne⟩)
      terminal.2.2.2 hnuStableN
  have hreverse : StableColoring N D nu previous :=
    (sc2 G e0 N D).symm (x := ⟨previous, terminal.1, terminal.2.1⟩)
      (y := ⟨nu, hnuProper, hnuOne⟩) hnuPrevious
  have hnuClosed : ColoredVertexSetClosed G nu (TreeSequenceVertexSet N) := by
    intro f d v hf hv hfd hmissing
    obtain ⟨w, hw, z, hz, he⟩ : ∃ w ∈ TreeSequenceVertexSet N,
        ∃ z ∉ TreeSequenceVertexSet N, G.ends f = Sym2.mk w z := by
      simpa [BoundaryEdges] using hf
    have hinc : TreeIncidentEdge N f := ⟨w, hw, by simp [Incident, he]⟩
    have hd : d ∈ TreeMissingColors nu N := Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩
    have hprevious : previous f = some d :=
      (hreverse.1 f hinc ⟨d, Finset.mem_union_left _ hd, hfd⟩).trans hfd
    exact (terminal.2.2.1 hf hv hprevious) (by rw [hreverse.2 v hv]; exact hmissing)
  have missing_closed : ∀ d ∈ TreeMissingColors nu N, TreeColorSetClosed G nu N {d} := by
    intro d hd a ha
    have had : a = d := Finset.mem_singleton.mp ha
    subst a
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hb, hfd⟩ := Finset.mem_filter.mp hf
    exact (hnuClosed hb hv hfd) hm
  have hlargeN : 2 * ett.rounds + 11 ≤ (TreeMissingColors phi N).card := by
    simpa only [N, hr] using hlarge
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (TreeMissingColors phi N).card by omega)
  obtain ⟨x, hx, hcx⟩ := Finset.mem_biUnion.mp hc
  have hcxNu : c ∈ MissingColors G nu x := by rw [hnuStableN.2 x hx]; exact hcx
  have hcNu : c ∈ TreeMissingColors nu N := Finset.mem_biUnion.mpr ⟨x, hx, hcxNu⟩
  have hcClosed := missing_closed c hcNu
  have hthetaClosedN : TreeColorSetClosed G nu N {theta} := by
    intro d hd
    have hold : TreeColorSetClosed G phi N {theta} := by
      simpa only [hstar] using hthetaClosedStar
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hb, hfd⟩ := Finset.mem_filter.mp hf
    obtain ⟨v, hv, w, hw, he⟩ : ∃ v ∈ TreeSequenceVertexSet N,
        ∃ w ∉ TreeSequenceVertexSet N, G.ends f = Sym2.mk v w := by
      simpa [BoundaryEdges] using hb
    have hfixed := hnuFixed f ⟨v, hsub hv, by simp [Incident, he]⟩
    have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet N) d :=
      Finset.mem_filter.mpr ⟨hb, hfixed.symm.trans hfd⟩
    rw [hold d hd] at hm
    simpa using hm
  have hf3N : f₃ ∈ BoundaryColorEdges G nu (TreeSequenceVertexSet N) beta := by
    obtain ⟨hb, hfc⟩ := Finset.mem_filter.mp hf₃
    obtain ⟨v, hv, w, hw, he⟩ : ∃ v ∈ TreeSequenceVertexSet T,
        ∃ w ∉ TreeSequenceVertexSet T, G.ends f₃ = Sym2.mk v w := by
      simpa [BoundaryEdges] using hb
    have hbends : b₃ = v ∨ b₃ = w := by simpa [Incident, he] using hif₃
    have hbv := hbends.resolve_right (fun h => hw (h ▸ hsub hb3))
    refine Finset.mem_filter.mpr ⟨?_, (hnuFixed f₃ ⟨b₃, hsub hb3, hif₃⟩).trans hfc⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b₃, hb3, w, fun h => hw (hsub h), by rw [hbv]; exact he⟩
  have hcb : c ≠ beta := by
    intro he
    have hm := hf3N
    rw [← he, hcClosed c (Finset.mem_singleton_self c)] at hm
    simpa using hm
  have hbetaNu : beta ∈ PresentColors G nu x := by
    by_contra h
    have hm : beta ∈ MissingColors G nu x := by simpa [MissingColors] using h
    have hc' := missing_closed beta (Finset.mem_biUnion.mpr ⟨x, hx, hm⟩)
    have hf := hf3N
    rw [hc' beta (Finset.mem_singleton_self beta)] at hf
    simpa using hf
  let rho := OutsideTreeColorSwap N nu theta c
  obtain ⟨hrhoProper, hrhoOne, hrhoStable, hrhoFixed⟩ :=
    stable_outside N D nu theta c hnuProper hnuOne hthetaClosedN hcClosed
  obtain ⟨L1, hL1, hsL1⟩ := transfer_exit N N nu theta c beta (fun _ h => h)
    hthetaBeta hcb hthetaClosedN hcClosed Q1 hQ1 hb1
  obtain ⟨L2, hL2, hsL2⟩ := transfer_exit N N nu theta c beta (fun _ h => h)
    hthetaBeta hcb hthetaClosedN hcClosed Q2 hQ2 hb2
  obtain ⟨L3, hL3, hsL3⟩ := transfer_exit N N nu theta c beta (fun _ h => h)
    hthetaBeta hcb hthetaClosedN hcClosed Q3 hQ3 hb3
  have hdisjoint12 : ∀ z, z ∈ L1.support → z ∉ L2.support := by
    simpa only [hsL1, hsL2, hsQ1, hsQ2] using hpaths₁₂
  have hdisjoint13 : ∀ z, z ∈ L1.support → z ∉ L3.support := by
    simpa only [hsL1, hsL3, hsQ1, hsQ3] using hpaths₁₃
  have hdisjoint23 : ∀ z, z ∈ L2.support → z ∉ L3.support := by
    simpa only [hsL2, hsL3, hsQ2, hsQ3] using hpaths₂₃
  have hcxRho : c ∈ MissingColors G rho x := by rw [hrhoStable.2 x hx]; exact hcxNu
  have hcRho : c ∈ TreeMissingColors rho N := Finset.mem_biUnion.mpr ⟨x, hx, hcxRho⟩
  have hstablePrevious : StableColoring N D previous rho :=
    (sc2 G e0 N D).trans (x := ⟨previous, terminal.1, terminal.2.1⟩)
      (y := ⟨nu, hnuProper, hnuOne⟩) (z := ⟨rho, hrhoProper, hrhoOne⟩)
      hnuPrevious hrhoStable
  have hinter : TreeInterchangeable G N rho c beta := by
    by_cases hn : ett.rounds = 1
    · have hi : r.succ.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
        apply Fin.ext
        simp [r, hn]
      have hz : r.castSucc = (0 : Fin (ett.rounds + 1)) := by
        apply Fin.ext
        simp [r, hn]
      have hb := (TechnicalTheoremBase G k ett.rounds e0 input ett.series).2
      dsimp only at hb
      have hs : StableColoring (ett.series.data.tree ⟨1, by omega⟩)
          (TashkinovStoredColors ett.series.data 0) (ett.series.data.coloring 0) rho := by
        simpa only [N, D, previous, hi, hz] using hstablePrevious
      simpa only [N, hi] using hb rho hrhoProper hrhoOne hs c beta
        (Or.inl (by simpa only [N, hi] using hcRho))
    · have hn' : 1 < ett.rounds := by omega
      obtain ⟨lower, hlr, hlMP, htrees, hdata⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett hMP hn'
      let lt : Fin (lower.rounds + 1) := Fin.last lower.rounds
      have hcast : Fin.castLE (by omega) lt = r.castSucc := by
        apply Fin.ext
        simp [lt, r, hlr]
      have ht : lower.series.data.tree (Fin.last (lower.rounds + 1)) = N := by
        rw [htrees]
        congr 1
        apply Fin.ext
        simp [N, hlr, r]
      obtain ⟨hco, _, _, _, _, _, _, _, hst, _⟩ := hdata lt
      have hs : StableColoring (lower.series.data.tree (Fin.last (lower.rounds + 1)))
          (TashkinovStoredColors lower.series.data lt) (lower.series.data.coloring lt) rho := by
        rw [ht, hco, hst, hcast]
        exact hstablePrevious
      have hh := (hlower lower (by omega) (by omega) hlMP).2.1
      dsimp only at hh
      simpa only [ht] using hh rho hrhoProper hrhoOne hs c beta
        (Or.inl (by simpa only [ht] using hcRho))
  -- Missing colors give degree at most one; the retained beta edge makes x a leaf.
  let J := TwoColorIncidenceGraph G rho c beta
  have leaf (v : V) (hm : c ∈ MissingColors G rho v ∨ beta ∈ MissingColors G rho v) :
      Set.Subsingleton (J.neighborSet (Sum.inl v)) := by
    intro z hz w hw
    cases z with
    | inl y => simp [J, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
    | inr e =>
      cases w with
      | inl y => simp [J, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
      | inr f =>
        have he : Incident G v e ∧ (rho e = some c ∨ rho e = some beta) := by
          simpa [J, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using hz
        have hf : Incident G v f ∧ (rho f = some c ∨ rho f = some beta) := by
          simpa [J, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using hw
        apply congrArg Sum.inr
        by_contra hef
        have absent (d : Fin k) (hd : d ∈ MissingColors G rho v) :
            ∀ e, Incident G v e → rho e ≠ some d := by
          intro e he hco
          have hn : d ∉ PresentColors G rho v := by simpa [MissingColors] using hd
          exact hn (by simpa [PresentColors] using
            (show ∃ f, Incident G v f ∧ rho f = some d from ⟨e, he, hco⟩))
        rcases hm with hm | hm
        · exact (hrhoProper hef ⟨v, he.1, hf.1⟩
            (he.2.resolve_left (absent c hm e he.1)))
            (hf.2.resolve_left (absent c hm f hf.1))
        · exact (hrhoProper hef ⟨v, he.1, hf.1⟩
            (he.2.resolve_right (absent beta hm e he.1)))
            (hf.2.resolve_right (absent beta hm f hf.1))
  have lx := leaf x (Or.inl hcxRho)
  have l1 := leaf a₁ hL1.2.2.2.2.1
  have l2 := leaf a₂ hL2.2.2.2.2.1
  have l3 := leaf a₃ hL3.2.2.2.2.1
  have x_neighbor : ∃ z, J.Adj (Sum.inl x) z := by
    obtain ⟨f, hinc, hf⟩ : ∃ f, Incident G x f ∧ nu f = some beta := by
      simpa [PresentColors] using hbetaNu
    exact ⟨Sum.inr f, hinc, Or.inr ((hrhoFixed f ⟨x, hx, hinc⟩).trans hf)⟩
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G rho c beta (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have px : TwoColorPathComponent G rho c beta (Sum.inl x) :=
    ⟨hcb, Sum.inl x, self x, lx⟩
  have p1 : TwoColorPathComponent G rho c beta (Sum.inl a₁) :=
    ⟨hcb, Sum.inl a₁, self _, l1⟩
  have p2 : TwoColorPathComponent G rho c beta (Sum.inl a₂) :=
    ⟨hcb, Sum.inl a₂, self _, l2⟩
  have p3 : TwoColorPathComponent G rho c beta (Sum.inl a₃) :=
    ⟨hcb, Sum.inl a₃, self _, l3⟩
  have meet1 : Sum.inl b₁ ∈ TwoColorComponent G rho c beta (Sum.inl a₁) :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      (SimpleGraph.ConnectedComponent.eq.mpr L1.reachable.symm)
  have meet2 : Sum.inl b₂ ∈ TwoColorComponent G rho c beta (Sum.inl a₂) :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      (SimpleGraph.ConnectedComponent.eq.mpr L2.reachable.symm)
  have meet3 : Sum.inl b₃ ∈ TwoColorComponent G rho c beta (Sum.inl a₃) :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      (SimpleGraph.ConnectedComponent.eq.mpr L3.reachable.symm)
  have eq1 := hinter (Sum.inl x) (Sum.inl a₁) px p1 ⟨x, hx, self x⟩ ⟨b₁, hb1, meet1⟩
  have eq2 := hinter (Sum.inl x) (Sum.inl a₂) px p2 ⟨x, hx, self x⟩ ⟨b₂, hb2, meet2⟩
  have eq3 := hinter (Sum.inl x) (Sum.inl a₃) px p3 ⟨x, hx, self x⟩ ⟨b₃, hb3, meet3⟩
  obtain ⟨u, v, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G rho c beta hrhoProper (Sum.inl x)
  have endpoint (w : V) (hw : Sum.inl w ∈ TwoColorComponent G rho c beta (Sum.inl x))
      (hl : Set.Subsingleton (J.neighborSet (Sum.inl w))) :
      Sum.inl w = u ∨ Sum.inl w = v := by
    by_contra hn
    push Not at hn
    apply hp.isTrail.not_mem_support_of_subsingleton_neighborSet hn.1 hn.2 hl
    change Sum.inl w ∈ {z | z ∈ p.support}
    rw [hsupport]
    exact hw
  have e1 := endpoint a₁ (by rw [eq1]; exact self _) l1
  have e2 := endpoint a₂ (by rw [eq2]; exact self _) l2
  have e3 := endpoint a₃ (by rw [eq3]; exact self _) l3
  have ha12 : (Sum.inl a₁ : Sum V E) ≠ Sum.inl a₂ := by simpa using ha₁₂
  have ha13 : (Sum.inl a₁ : Sum V E) ≠ Sum.inl a₃ := by simpa using ha₁₃
  have ha23 : (Sum.inl a₂ : Sum V E) ≠ Sum.inl a₃ := by simpa using ha₂₃
  rcases e1 with e1 | e1
  · rcases e2 with e2 | e2
    · exact ha12 (e1.trans e2.symm)
    · rcases e3 with e3 | e3
      · exact ha13 (e1.trans e3.symm)
      · exact ha23 (e2.trans e3.symm)
  · rcases e2 with e2 | e2
    · rcases e3 with e3 | e3
      · exact ha23 (e2.trans e3.symm)
      · exact ha13 (e1.trans e3.symm)
    · exact ha12 (e1.trans e2.symm)
