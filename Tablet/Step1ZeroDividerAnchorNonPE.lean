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
import Tablet.HierarchyOutsideKempeStable
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStoredColorsCardinality
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
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

set_option maxHeartbeats 800000

-- [TABLET NODE: Step1ZeroDividerAnchorNonPE]
lemma Step1ZeroDividerAnchorNonPE {V E : Type*}
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
           ModColoring lower sigma))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hdividerZero : H.dividerCount = 0)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hclosed : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {alpha})
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (hP₁ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₂ b₂ P₂)
    (hpaths : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (ha : a₁ ≠ a₂)
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) : False := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let p : Fin (ett.rounds + 1) := ⟨ett.rounds - 1, by omega⟩
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let X : Finset V := TreeSequenceVertexSet Tn
  let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p
  have hphi : phi = ett.series.data.coloring n := by
    simpa [n] using ett.generatingColoring
  have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) =
      base.core := by
    have hlast : Fin.last H.dividerCount =
        (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    rw [hlast]
    rfl
  have hcore : base.core = Tn := by
    simpa [n, Tn] using base.nonparallel hnonPE
  have hterminal :
      IsProperEdgeColoring G (ett.series.data.coloring p) ∧
      IsOneEdgeUncolored (ett.series.data.coloring p) e0 ∧
      ColoredVertexSetClosed G (ett.series.data.coloring p)
        (TreeSequenceVertexSet Tn) ∧
      StableColoring Tn Dp (ett.series.data.coloring p) phi := by
    as_aux_lemma =>
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hn : n ≠ 0 := by simp [n]; omega
      exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hp : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by
        rw [targetEq]
        exact currentKind
      exact (hnonPE (by simpa [n] using hp)).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      have hip : i.castSucc = p := by
        apply Fin.ext
        simp [p, n] at hi ⊢
        have hv := congrArg Fin.val hi
        simp at hv
        omega
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hip] using previousProper
      · simpa [hip] using previousOneUncolored
      · rw [← htree, ← hip]
        exact previousClosed
      · have hselected : choice.selected = phi :=
          currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans hphi.symm)
        have hs : StableColoring Tn Dp
            (ett.series.data.coloring p) choice.selected := by
          simpa only [Dp, htree, hip] using choice.selectedStable
        exact Eq.mp
          (congrArg (fun q => StableColoring Tn Dp
            (ett.series.data.coloring p) q) hselected) hs
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      have hip : i.castSucc = p := by
        apply Fin.ext
        have hv := congrArg Fin.val hi
        simp [p, n] at hv ⊢
        omega
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      have hcol : ett.series.data.coloring p = phi := by
        exact (congrArg ett.series.data.coloring hip.symm).trans
          (currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans hphi.symm))
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hip] using previousProper
      · simpa [hip] using previousOneUncolored
      · rw [← htree, ← hip]
        exact previousClosed
      · have hs : StableColoring Tn Dp
            (ett.series.data.coloring p) (ett.series.data.coloring p) :=
          (sc2 G e0 Tn Dp).refl
            ⟨ett.series.data.coloring p, by simpa [hip] using previousProper,
              by simpa [hip] using previousOneUncolored⟩
        exact Eq.mp
          (congrArg (fun q => StableColoring Tn Dp
            (ett.series.data.coloring p) q) hcol) hs
  have missingClosed : ∀ d : Fin k,
      d ∈ TreeMissingColors phi Tn →
        BoundaryColorEdges G phi (TreeSequenceVertexSet Tn) d = ∅ := by
    intro d hd
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hfData : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
        phi f = some d := by
      simpa [BoundaryColorEdges] using hf
    obtain ⟨y, hyT, hyd⟩ := Finset.mem_biUnion.mp hd
    have hfIncident : TreeIncidentEdge Tn f := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at hfData
      obtain ⟨u, huT, v, hvT, huv⟩ := hfData.1
      refine ⟨u, huT, ?_⟩
      unfold Incident
      rw [huv]
      exact Sym2.mem_mk_left _ _
    have hydPrev : d ∈ MissingColors G (ett.series.data.coloring p) y := by
      rw [← hterminal.2.2.2.2 y hyT]
      exact hyd
    have hdPrev : d ∈ TreeMissingColors (ett.series.data.coloring p) Tn := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨y, hyT, hydPrev⟩
    have hfFixed : phi f = ett.series.data.coloring p f := by
      apply (sc1 G e0 Tn Dp (ett.series.data.coloring p) phi
        hterminal.1 hterminal.2.1 hproper hone).mp
        hterminal.2.2.2 f hfIncident
      exact Or.inr ⟨d, Finset.mem_union_left _ hdPrev, hfData.2⟩
    exact (hterminal.2.2.1 hfData.1 hyT
      (hfFixed.symm.trans hfData.2)) hydPrev
  have hP1 : TreeExitPath Tn phi alpha beta a₁ b₁ P₁ := by
    simpa [hstar, hcore] using hP₁
  have hP2 : TreeExitPath Tn phi alpha beta a₂ b₂ P₂ := by
    simpa [hstar, hcore] using hP₂
  have halphaT : alpha ∈ TreeMissingColors phi Tn := by
    simpa [hstar, hcore] using halpha
  have halphaClosed : TreeColorSetClosed G phi Tn {alpha} := by
    simpa [hstar, hcore] using hclosed
  obtain ⟨f₁, hf₁Boundary, hf₁Incident, hf₁Support⟩ :=
    ClosedColorExitPathBoundaryEdge G Tn phi alpha beta halphaClosed
      a₁ b₁ P₁ hP1
  obtain ⟨f₂, hf₂Boundary, hf₂Incident, hf₂Support⟩ :=
    ClosedColorExitPathBoundaryEdge G Tn phi alpha beta halphaClosed
      a₂ b₂ P₂ hP2
  have hbetaNotMissing : beta ∉ TreeMissingColors phi Tn := by
    intro hbeta
    have hempty := missingClosed beta hbeta
    rw [hempty] at hf₁Boundary
    simpa using hf₁Boundary
  let x : V := Tn.vertex 0
  have hxT : x ∈ TreeSequenceVertexSet Tn := by
    simp [x, TreeSequenceVertexSet]
  have degreeBound : MaximumDegree G + 1 ≤ k := by
    have step := ett.series.certified 0
    cases step with
    | initial triple => exact triple.2.2.1
  have presentBound : (PresentColors G phi x).card ≤ Degree G x := by
    have chooseEdge (d : {d : Fin k // d ∈ PresentColors G phi x}) :
        ∃ f, Incident G x f ∧ phi f = some d.1 := by
      simpa [PresentColors] using d.property
    let select : {d : Fin k // d ∈ PresentColors G phi x} →
        {f : E // Incident G x f} := fun d =>
      ⟨Classical.choose (chooseEdge d),
        (Classical.choose_spec (chooseEdge d)).1⟩
    have selectColor : ∀ d, phi (select d).1 = some d.1 := by
      intro d
      exact (Classical.choose_spec (chooseEdge d)).2
    have selectInjective : Function.Injective select := by
      intro d e hde
      apply Subtype.ext
      apply Option.some.inj
      calc
        some (d : Fin k) = phi (select d).1 := (selectColor d).symm
        _ = phi (select e).1 := by rw [hde]
        _ = some (e : Fin k) := selectColor e
    letI : Fintype {d : Fin k // d ∈ PresentColors G phi x} :=
      Fintype.ofFinite _
    have hcard := Fintype.card_le_of_injective select selectInjective
    change (PresentColors G phi x).card ≤
      (Finset.univ.filter (fun f => Incident G x f)).card
    simpa [Fintype.card_subtype] using hcard
  have degreeAt : Degree G x ≤ MaximumDegree G := by
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨x, by simp⟩)))
  have missingAtX : (MissingColors G phi x).Nonempty := by
    by_contra hempty
    have hmissingEmpty : MissingColors G phi x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hall : PresentColors G phi x = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro d
      by_contra hd
      have hm : d ∈ MissingColors G phi x := by
        simp [MissingColors, hd]
      rw [hmissingEmpty] at hm
      exact Finset.notMem_empty d hm
    have hk : k ≤ Degree G x := by
      have := presentBound
      simpa [hall] using this
    omega
  obtain ⟨c, hcxMissing⟩ := missingAtX
  have hcT : c ∈ TreeMissingColors phi Tn := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨x, hxT, hcxMissing⟩
  have hcClosed : TreeColorSetClosed G phi Tn {c} := by
    unfold TreeColorSetClosed
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    exact missingClosed c hcT
  have hbetaPresent : beta ∈ PresentColors G phi x := by
    by_contra hb
    apply hbetaNotMissing
    unfold TreeMissingColors
    refine Finset.mem_biUnion.mpr ⟨x, hxT, ?_⟩
    simpa [MissingColors] using hb
  have hcNeBeta : c ≠ beta := by
    intro hcb
    subst c
    have hnot : beta ∉ PresentColors G phi x := by
      simpa [MissingColors] using hcxMissing
    exact hnot hbetaPresent
  have treeMissingEq : TreeMissingColors phi Tn =
      TreeMissingColors (ett.series.data.coloring p) Tn := by
    ext d
    unfold TreeMissingColors
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hd⟩
      refine ⟨v, hv, ?_⟩
      rw [← hterminal.2.2.2.2 v hv]
      exact hd
    · rintro ⟨v, hv, hd⟩
      refine ⟨v, hv, ?_⟩
      rw [hterminal.2.2.2.2 v hv]
      exact hd
  have finalInterchange : ∀ (sigma : PartialEdgeColoring E k),
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn Dp phi sigma →
      ∀ a b : Fin k,
        (a ∈ TreeMissingColors sigma Tn ∨
          b ∈ TreeMissingColors sigma Tn) →
        TreeInterchangeable G Tn sigma a b := by
    intro sigma hsProper hsOne hsStable a b hmissing
    have hsComposed : StableColoring Tn Dp
        (ett.series.data.coloring p) sigma := by
      constructor
      · intro f hf hcolor
        obtain ⟨d, hd, hdf⟩ := hcolor
        have hdPhi : d ∈ TreeMissingColors phi Tn ∪ Dp := by
          rcases Finset.mem_union.mp hd with hdMissing | hdControl
          · exact Finset.mem_union_left _ (by
              rw [treeMissingEq]
              exact hdMissing)
          · exact Finset.mem_union_right _ hdControl
        have hphiFixed : phi f = ett.series.data.coloring p f := by
          exact hterminal.2.2.2.1 f hf ⟨d, hd, hdf⟩
        have hsigmaFixed : sigma f = phi f := by
          apply hsStable.1 f hf
          exact ⟨d, hdPhi, hphiFixed.trans hdf⟩
        exact hsigmaFixed.trans hphiFixed
      · intro v hv
        exact (hsStable.2 v hv).trans (hterminal.2.2.2.2 v hv)
    by_cases honeRound : ett.rounds = 1
    · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
      have hidx1 : (⟨1, by omega⟩ : Fin (ett.rounds + 2)) =
          n.castSucc := by
        apply Fin.ext
        simp [n, honeRound]
      have hT1 : ett.series.data.tree ⟨1, by omega⟩ = Tn := by
        rw [hidx1]
      have hs0 : StableColoring
          (ett.series.data.tree ⟨1, by omega⟩)
          (TashkinovStoredColors ett.series.data 0)
          (ett.series.data.coloring 0) sigma := by
        rw [hT1]
        simpa [p, Dp, honeRound] using hsComposed
      have hm0 : a ∈ TreeMissingColors sigma
            (ett.series.data.tree ⟨1, by omega⟩) ∨
          b ∈ TreeMissingColors sigma
            (ett.series.data.tree ⟨1, by omega⟩) := by
        rw [hT1]
        exact hmissing
      have hinter := htech.2 sigma hsProper hsOne hs0 a b hm0
      rw [hT1] at hinter
      exact hinter
    · have hgt : 1 < ett.rounds := by omega
      obtain ⟨pred, predRound, predMP, predTrees, predData⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett hMP hgt
      have low := (hlower pred (by omega) (by omega) predMP).2.1
      have hpredNext : pred.series.data.tree
          (Fin.last (pred.rounds + 1)) = Tn := by
        have hh := predTrees (Fin.last (pred.rounds + 1))
        have hidx : Fin.castLE (by omega) (Fin.last (pred.rounds + 1)) =
            n.castSucc := by
          apply Fin.ext
          simp [predRound, n]
          omega
        simpa [Tn] using hh.trans (congrArg ett.series.data.tree hidx)
      have hpredColor : pred.series.data.coloring (Fin.last pred.rounds) =
          ett.series.data.coloring p := by
        have hh := (predData (Fin.last pred.rounds)).1
        have hidx : Fin.castLE (by omega) (Fin.last pred.rounds) = p := by
          apply Fin.ext
          simp [predRound, p]
        rw [hidx] at hh
        exact hh
      have hpredStored : TashkinovStoredColors pred.series.data
          (Fin.last pred.rounds) = Dp := by
        have hh := (predData (Fin.last pred.rounds)).2.2.2.2.2.2.2.2.1
        have hidx : Fin.castLE (by omega) (Fin.last pred.rounds) = p := by
          apply Fin.ext
          simp [predRound, p]
        rw [hidx] at hh
        simpa [Dp] using hh
      have hsPred : StableColoring
          (pred.series.data.tree (Fin.last (pred.rounds + 1)))
          (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
          (pred.series.data.coloring (Fin.last pred.rounds)) sigma := by
        rw [hpredNext, hpredStored, hpredColor]
        exact hsComposed
      have hmPred : a ∈ TreeMissingColors sigma
            (pred.series.data.tree (Fin.last (pred.rounds + 1))) ∨
          b ∈ TreeMissingColors sigma
            (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
        rw [hpredNext]
        exact hmissing
      have hinter := low sigma hsProper hsOne hsPred a b hmPred
      rw [hpredNext] at hinter
      exact hinter
  have finish : ∀ (sigma : PartialEdgeColoring E k),
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn Dp phi sigma →
      c ∈ TreeMissingColors sigma Tn →
      ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk
          (Sum.inl a₁) (Sum.inl b₁))
        (Q₂ : (TwoColorIncidenceGraph G sigma c beta).Walk
          (Sum.inl a₂) (Sum.inl b₂)),
        TreeExitPath Tn sigma c beta a₁ b₁ Q₁ →
        TreeExitPath Tn sigma c beta a₂ b₂ Q₂ → False := by
    intro sigma hsProper hsOne hsStable hcMissing Q₁ Q₂ hQ₁ hQ₂
    let graph := TwoColorIncidenceGraph G sigma c beta
    have missingLeaf : ∀ (v : V),
        (c ∈ MissingColors G sigma v ∨ beta ∈ MissingColors G sigma v) →
        Set.Subsingleton (graph.neighborSet (Sum.inl v)) := by
      intro v hmissing z hz w hw
      cases hzv : z with
      | inl u =>
          rw [hzv] at hz
          simpa [graph, SimpleGraph.mem_neighborSet,
            TwoColorIncidenceGraph] using hz
      | inr e =>
          cases hwv : w with
          | inl u =>
              rw [hwv] at hw
              simpa [graph, SimpleGraph.mem_neighborSet,
                TwoColorIncidenceGraph] using hw
          | inr f =>
              rw [hzv] at hz
              rw [hwv] at hw
              have he : Incident G v e ∧
                  (sigma e = some c ∨ sigma e = some beta) := by
                simpa [graph, SimpleGraph.mem_neighborSet,
                  TwoColorIncidenceGraph] using hz
              have hf : Incident G v f ∧
                  (sigma f = some c ∨ sigma f = some beta) := by
                simpa [graph, SimpleGraph.mem_neighborSet,
                  TwoColorIncidenceGraph] using hw
              apply congrArg Sum.inr
              by_contra hef
              rcases hmissing with hcm | hbm
              · have hnc : c ∉ PresentColors G sigma v := by
                  simpa [MissingColors] using hcm
                have hec : sigma e = some beta := he.2.resolve_left (by
                  intro hec
                  apply hnc
                  simpa [PresentColors] using
                    (show ∃ q, Incident G v q ∧ sigma q = some c from
                      ⟨e, he.1, hec⟩))
                have hfc : sigma f = some beta := hf.2.resolve_left (by
                  intro hfc
                  apply hnc
                  simpa [PresentColors] using
                    (show ∃ q, Incident G v q ∧ sigma q = some c from
                      ⟨f, hf.1, hfc⟩))
                exact (hsProper hef ⟨v, he.1, hf.1⟩ hec) hfc
              · have hnb : beta ∉ PresentColors G sigma v := by
                  simpa [MissingColors] using hbm
                have heb : sigma e = some c := he.2.resolve_right (by
                  intro heb
                  apply hnb
                  simpa [PresentColors] using
                    (show ∃ q, Incident G v q ∧ sigma q = some beta from
                      ⟨e, he.1, heb⟩))
                have hfb : sigma f = some c := hf.2.resolve_right (by
                  intro hfb
                  apply hnb
                  simpa [PresentColors] using
                    (show ∃ q, Incident G v q ∧ sigma q = some beta from
                      ⟨f, hf.1, hfb⟩))
                exact (hsProper hef ⟨v, he.1, hf.1⟩ heb) hfb
    have hcxSigma : c ∈ MissingColors G sigma x := by
      rw [hsStable.2 x hxT]
      exact hcxMissing
    have hxLeaf : Set.Subsingleton (graph.neighborSet (Sum.inl x)) :=
      missingLeaf x (Or.inl hcxSigma)
    have ha₁Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₁)) :=
      missingLeaf a₁ hQ₁.2.2.2.2.1
    have ha₂Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₂)) :=
      missingLeaf a₂ hQ₂.2.2.2.2.1
    have hpathX : TwoColorPathComponent G sigma c beta (Sum.inl x) :=
      ⟨hcNeBeta, Sum.inl x, rfl, hxLeaf⟩
    have hpath₁ : TwoColorPathComponent G sigma c beta (Sum.inl a₁) :=
      ⟨hcNeBeta, Sum.inl a₁, rfl, ha₁Leaf⟩
    have hpath₂ : TwoColorPathComponent G sigma c beta (Sum.inl a₂) :=
      ⟨hcNeBeta, Sum.inl a₂, rfl, ha₂Leaf⟩
    have hmeetX : ∃ v ∈ TreeSequenceVertexSet Tn,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl x) :=
      ⟨x, hxT, rfl⟩
    have hmeet₁ : ∃ v ∈ TreeSequenceVertexSet Tn,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₁) := by
      refine ⟨b₁, hQ₁.2.2.2.1, ?_⟩
      change graph.connectedComponentMk (Sum.inl b₁) =
        graph.connectedComponentMk (Sum.inl a₁)
      exact (SimpleGraph.ConnectedComponent.sound Q₁.reachable).symm
    have hmeet₂ : ∃ v ∈ TreeSequenceVertexSet Tn,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₂) := by
      refine ⟨b₂, hQ₂.2.2.2.1, ?_⟩
      change graph.connectedComponentMk (Sum.inl b₂) =
        graph.connectedComponentMk (Sum.inl a₂)
      exact (SimpleGraph.ConnectedComponent.sound Q₂.reachable).symm
    have ha₁x : a₁ ≠ x := by
      intro h
      exact hQ₁.2.2.1 (h ▸ hxT)
    have ha₂x : a₂ ≠ x := by
      intro h
      exact hQ₂.2.2.1 (h ▸ hxT)
    have hdistinct :
        TwoColorComponent G sigma c beta (Sum.inl x) ≠
            TwoColorComponent G sigma c beta (Sum.inl a₁) ∨
        TwoColorComponent G sigma c beta (Sum.inl x) ≠
            TwoColorComponent G sigma c beta (Sum.inl a₂) := by
      by_contra hnot
      push_neg at hnot
      obtain ⟨u, v, R, hRpath, hRsupport⟩ :=
        TwoColorComponentSpanningPath G sigma c beta hsProper (Sum.inl x)
      have hxR : Sum.inl x ∈ R.support := by
        change Sum.inl x ∈ {z | z ∈ R.support}
        rw [hRsupport]
        rfl
      have ha₁R : Sum.inl a₁ ∈ R.support := by
        change Sum.inl a₁ ∈ {z | z ∈ R.support}
        rw [hRsupport, hnot.1]
        rfl
      have ha₂R : Sum.inl a₂ ∈ R.support := by
        change Sum.inl a₂ ∈ {z | z ∈ R.support}
        rw [hRsupport, hnot.2]
        rfl
      have endpointOfLeaf : ∀ (z : Sum V E),
          Set.Subsingleton (graph.neighborSet z) → z ∈ R.support →
            z = u ∨ z = v := by
        intro z hzLeaf hzR
        by_contra hzEnds
        push Not at hzEnds
        exact (hRpath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hzEnds.1 hzEnds.2 hzLeaf) hzR
      have hxEnds := endpointOfLeaf (Sum.inl x) hxLeaf hxR
      have ha₁Ends := endpointOfLeaf (Sum.inl a₁) ha₁Leaf ha₁R
      have ha₂Ends := endpointOfLeaf (Sum.inl a₂) ha₂Leaf ha₂R
      rcases hxEnds with hxu | hxv <;>
        rcases ha₁Ends with h₁u | h₁v <;>
        rcases ha₂Ends with h₂u | h₂v
      · exact ha₁x (Sum.inl.inj (h₁u.trans hxu.symm))
      · exact ha₁x (Sum.inl.inj (h₁u.trans hxu.symm))
      · exact ha₂x (Sum.inl.inj (h₂u.trans hxu.symm))
      · exact ha (Sum.inl.inj (h₁v.trans h₂v.symm))
      · exact ha (Sum.inl.inj (h₁u.trans h₂u.symm))
      · exact ha₂x (Sum.inl.inj (h₂v.trans hxv.symm))
      · exact ha₁x (Sum.inl.inj (h₁v.trans hxv.symm))
      · exact ha₁x (Sum.inl.inj (h₁v.trans hxv.symm))
    have hinter := finalInterchange sigma hsProper hsOne hsStable c beta
      (Or.inl hcMissing)
    rcases hdistinct with hneComp | hneComp
    · exact hneComp (hinter (Sum.inl x) (Sum.inl a₁)
        hpathX hpath₁ hmeetX hmeet₁)
    · exact hneComp (hinter (Sum.inl x) (Sum.inl a₂)
        hpathX hpath₂ hmeetX hmeet₂)
  by_cases hac : alpha = c
  · subst alpha
    have hsRefl : StableColoring Tn Dp phi phi := by
      constructor
      · intro f hf hcolor
        rfl
      · intro v hv
        rfl
    exact finish phi hproper hone hsRefl hcT P₁ P₂ hP1 hP2
  · have componentOutside : ∀ (u : V), u ∉ X → ∀ (v : V),
        Sum.inl v ∈ TwoColorComponent G phi alpha c (Sum.inl u) →
          v ∉ X := by
      intro u hu v hvComponent hv
      let graph := TwoColorIncidenceGraph G phi alpha c
      change graph.connectedComponentMk (Sum.inl v) =
        graph.connectedComponentMk (Sum.inl u) at hvComponent
      have reach : graph.Reachable (Sum.inl u) (Sum.inl v) :=
        (SimpleGraph.ConnectedComponent.eq.mp hvComponent).symm
      apply reach.elim
      intro P
      let S : Set (Sum V E) := {y | match y with
        | Sum.inl q => q ∈ X
        | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
      have hSv : Sum.inl v ∈ S := by simpa [S] using hv
      have hSu : Sum.inl u ∉ S := by simpa [S] using hu
      obtain ⟨d, hd, hds, hdt⟩ :=
        P.reverse.exists_boundary_dart S hSv hSu
      have hadj := d.adj
      have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧ q ∈ X := by
        cases h : d.toProd.1 with
        | inl q =>
            rw [h] at hds
            exact ⟨q, rfl, by simpa [S] using hds⟩
        | inr f =>
            exfalso
            cases h2 : d.toProd.2 with
            | inl r =>
                rw [h, h2] at hadj
                change Incident G r f ∧
                  (phi f = some alpha ∨ phi f = some c) at hadj
                rw [h] at hds
                have hall : ∀ q, Incident G q f → q ∈ X := by
                  simpa [S] using hds
                have hrnot : r ∉ X := by
                  intro hr
                  apply hdt
                  simpa [S, h2] using hr
                exact hrnot (hall r hadj.1)
            | inr e =>
                rw [h, h2] at hadj
                exact hadj.elim
      obtain ⟨q, hq, hqX⟩ := hfirst
      have hsecond : ∃ f : E, d.toProd.2 = Sum.inr f := by
        cases h : d.toProd.2 with
        | inl r =>
            rw [hq, h] at hadj
            exact False.elim hadj
        | inr f => exact ⟨f, rfl⟩
      obtain ⟨f, hf⟩ := hsecond
      have hfadj : graph.Adj (Sum.inl q) (Sum.inr f) := by
        rw [hq, hf] at hadj
        exact hadj
      have hfdata : Incident G q f ∧
          (phi f = some alpha ∨ phi f = some c) := by
        simpa [graph, TwoColorIncidenceGraph] using hfadj
      have hnotall : ¬ ∀ r, Incident G r f → r ∈ X := by
        intro hall
        apply hdt
        simpa [S, hf, hall]
      obtain ⟨r, hrf, hrX⟩ : ∃ r, Incident G r f ∧ r ∉ X := by
        push Not at hnotall
        exact hnotall
      have hqr : q ≠ r := by
        intro h
        exact hrX (h ▸ hqX)
      have hend : G.ends f = Sym2.mk q r :=
        (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
      have hfb : f ∈ BoundaryEdges G X := by
        simp [BoundaryEdges]
        exact ⟨q, hqX, r, hrX, hend⟩
      rcases hfdata.2 with hfa | hfc
      · have hfalpha : f ∈ BoundaryColorEdges G phi X alpha := by
          simp [BoundaryColorEdges, hfb, hfa]
        have hempty := halphaClosed alpha (by simp)
        rw [show X = TreeSequenceVertexSet Tn by rfl] at hfalpha
        rw [hempty] at hfalpha
        simpa using hfalpha
      · have hfcolor : f ∈ BoundaryColorEdges G phi X c := by
          simp [BoundaryColorEdges, hfb, hfc]
        have hempty := hcClosed c (by simp)
        rw [show X = TreeSequenceVertexSet Tn by rfl] at hfcolor
        rw [hempty] at hfcolor
        simpa using hfcolor
    let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
      match z with
      | Sum.inl u => u ∉ X
      | Sum.inr _ => False
    let rho : PartialEdgeColoring E k := fun f =>
      if ∃ z ∈ roots,
          Sum.inr f ∈ TwoColorComponent G phi alpha c z then
        if phi f = some alpha then some c
        else if phi f = some c then some alpha
        else phi f
      else phi f
    have hrecolor : OutsideKempeRecoloring Tn phi rho alpha c := by
      unfold OutsideKempeRecoloring
      refine ⟨hac, roots, ?_, ?_⟩
      · intro z hz v hvComponent
        simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        cases z with
        | inl u =>
            exact componentOutside u hz v hvComponent
        | inr f =>
            exact False.elim hz
      · intro f
        rfl
    have hstable := OutsideKempeRecoloringStable G e0 Tn Dp
      phi rho alpha c hproper hone hrecolor
    have hrhoProper : IsProperEdgeColoring G rho := hstable.1
    have hrhoOne : IsOneEdgeUncolored rho e0 := hstable.2.1
    have hrhoStable : StableColoring Tn Dp phi rho := hstable.2.2.1
    let selected : E → Prop := fun f => ∃ z ∈ roots,
      Sum.inr f ∈ TwoColorComponent G phi alpha c z
    have hbetaFixed : ∀ f : E,
        rho f = some beta ↔ phi f = some beta := by
      intro f
      by_cases hsel : selected f
      · change ∃ z ∈ roots,
          Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
        simp only [rho]
        rw [if_pos hsel]
        by_cases hfa : phi f = some alpha
        · rw [if_pos hfa, hfa]
          simp [hcNeBeta, hne]
        · rw [if_neg hfa]
          by_cases hfc : phi f = some c
          · rw [if_pos hfc, hfc]
            simp [hne, hcNeBeta]
          · rw [if_neg hfc]
      · change ¬ ∃ z ∈ roots,
          Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
        simp only [rho]
        rw [if_neg hsel]
    have selectedOfOutside : ∀ (u : V), u ∉ X → ∀ (f : E),
        Incident G u f →
        (phi f = some alpha ∨ phi f = some c) → selected f := by
      intro u hu f huf hfcolor
      refine ⟨Sum.inl u, ?_, ?_⟩
      · simp [roots, hu]
      · change (TwoColorIncidenceGraph G phi alpha c).connectedComponentMk
            (Sum.inr f) =
          (TwoColorIncidenceGraph G phi alpha c).connectedComponentMk
            (Sum.inl u)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (TwoColorIncidenceGraph G phi alpha c).Adj
              (Sum.inl u) (Sum.inr f) from ⟨huf, hfcolor⟩)).symm
    have pathEdgeOutside : ∀ (u v : V)
        (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
          (Sum.inl u) (Sum.inl v)),
        TreeExitPath Tn phi alpha beta u v P →
        ∀ f : E, Sum.inr f ∈ P.support →
          ∃ w : V, Sum.inl w ∈ P.support ∧ w ∉ X ∧
            Incident G w f := by
      intro u v P hExit f hfSupport
      rcases hExit with ⟨hPath, hLength, huX, hvX, hMissing, honly⟩
      obtain ⟨m, hm, hmle⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfSupport
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
        | inr e =>
            rw [hnode] at hprev
            simp [TwoColorIncidenceGraph] at hprev
      have hnext := P.adj_getVert_succ (i := m) hmlt
      rw [hm] at hnext
      obtain ⟨z, hzNext⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
        cases hnode : P.getVert (m + 1) with
        | inl z => exact ⟨z, rfl⟩
        | inr e =>
            rw [hnode] at hnext
            simp [TwoColorIncidenceGraph] at hnext
      have hwIncident : Incident G w f := by
        rw [hwPrev] at hprev
        simpa [TwoColorIncidenceGraph] using hprev.1
      have hzIncident : Incident G z f := by
        rw [hzNext] at hnext
        simpa [TwoColorIncidenceGraph] using hnext.1
      have hwSupport : Sum.inl w ∈ P.support := by
        rw [← hwPrev]
        exact P.getVert_mem_support (m - 1)
      have hzSupport : Sum.inl z ∈ P.support := by
        rw [← hzNext]
        exact P.getVert_mem_support (m + 1)
      by_cases hwX : w ∈ X
      · by_cases hzX : z ∈ X
        · have hwv : w = v :=
            (honly w (by simpa [X] using hwX)).mp hwSupport
          have hzv : z = v :=
            (honly z (by simpa [X] using hzX)).mp hzSupport
          have hverts : P.getVert (m - 1) = P.getVert (m + 1) := by
            rw [hwPrev, hzNext, hwv, hzv]
          have hindices := hPath.getVert_injOn
            (show m - 1 ≤ P.length by omega)
            (show m + 1 ≤ P.length by omega) hverts
          omega
        · exact ⟨z, hzSupport, hzX, hzIncident⟩
      · exact ⟨w, hwSupport, hwX, hwIncident⟩
    have transportExit : ∀ (u v : V)
        (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
          (Sum.inl u) (Sum.inl v)),
        TreeExitPath Tn phi alpha beta u v P →
        ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk
            (Sum.inl u) (Sum.inl v),
          TreeExitPath Tn rho c beta u v Q ∧
            Q.support = P.support := by
      intro u v P hExit
      have selectedAlphaEdge : ∀ f : E, Sum.inr f ∈ P.support →
          phi f = some alpha → selected f := by
        intro f hfP hfa
        obtain ⟨w, hwP, hwX, hwf⟩ := pathEdgeOutside u v P hExit f hfP
        exact selectedOfOutside w hwX f hwf (Or.inl hfa)
      have adjacencyTransport : ∀ (z w : Sum V E),
          z ∈ P.support → w ∈ P.support →
          (TwoColorIncidenceGraph G phi alpha beta).Adj z w →
          (TwoColorIncidenceGraph G rho c beta).Adj z w := by
        intro z w hzP hwP hadj
        cases z with
        | inl z =>
            cases w with
            | inl w => exact False.elim hadj
            | inr f =>
                rcases hadj with ⟨hzf, hcolor⟩
                refine ⟨hzf, ?_⟩
                rcases hcolor with hfa | hfb
                · left
                  have hsel := selectedAlphaEdge f hwP hfa
                  change ∃ z ∈ roots,
                    Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
                  simp only [rho]
                  rw [if_pos hsel, if_pos hfa]
                · right
                  exact (hbetaFixed f).2 hfb
        | inr f =>
            cases w with
            | inl w =>
                rcases hadj with ⟨hwf, hcolor⟩
                refine ⟨hwf, ?_⟩
                rcases hcolor with hfa | hfb
                · left
                  have hsel := selectedAlphaEdge f hzP hfa
                  change ∃ z ∈ roots,
                    Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
                  simp only [rho]
                  rw [if_pos hsel, if_pos hfa]
                · right
                  exact (hbetaFixed f).2 hfb
            | inr e => exact False.elim hadj
      have rebuild : ∀ {s t : Sum V E}
          (R : (TwoColorIncidenceGraph G phi alpha beta).Walk s t),
          (∀ z, z ∈ R.support → z ∈ P.support) →
          ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk s t,
            Q.support = R.support ∧ Q.length = R.length := by
        intro s t R
        induction R with
        | nil =>
            intro hsub
            exact ⟨.nil, rfl, rfl⟩
        | @cons s w t hsw R ih =>
            intro hsub
            have hsP : s ∈ P.support := hsub s (by simp)
            have hwP : w ∈ P.support := hsub w (by simp)
            obtain ⟨Q, hQsupport, hQlength⟩ := ih (by
              intro z hz
              exact hsub z (by simp [hz]))
            have hsw' := adjacencyTransport s w hsP hwP hsw
            refine ⟨.cons hsw' Q, ?_, ?_⟩
            · simp [hQsupport]
            · simp [hQlength]
      obtain ⟨Q, hQsupport, hQlength⟩ := rebuild P (by
        intro z hz
        exact hz)
      have hQpath : Q.IsPath := by
        apply SimpleGraph.Walk.IsPath.mk'
        rw [hQsupport]
        exact hExit.1.support_nodup
      have hmissing : c ∈ MissingColors G rho u ∨
          beta ∈ MissingColors G rho u := by
        rcases hExit.2.2.2.2.1 with halphaMissing | hbetaMissing
        · left
          have huX : u ∉ X := by simpa [X] using hExit.2.2.1
          have hnotAlpha : alpha ∉ PresentColors G phi u := by
            simpa [MissingColors] using halphaMissing
          have hnotC : c ∉ PresentColors G rho u := by
            intro hcPresent
            obtain ⟨f, huf, hrhof⟩ := by
              simpa [PresentColors] using hcPresent
            by_cases hsel : selected f
            · change ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              by_cases hfa : phi f = some alpha
              · apply hnotAlpha
                simpa [PresentColors] using
                  (show ∃ q, Incident G u q ∧ phi q = some alpha from
                    ⟨f, huf, hfa⟩)
              · by_cases hfc : phi f = some c
                · have hrhoAlpha : rho f = some alpha := by
                    simp only [rho]
                    rw [if_pos hsel, if_neg hfa, if_pos hfc]
                  have : some alpha = some c := hrhoAlpha.symm.trans hrhof
                  exact hac (Option.some.inj this)
                · have hrhoOld : rho f = phi f := by
                    simp only [rho]
                    rw [if_pos hsel, if_neg hfa, if_neg hfc]
                  exact hfc (hrhoOld.symm.trans hrhof)
            · change ¬ ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              have hfc : phi f = some c := by
                have hrhoOld : rho f = phi f := by
                  simp only [rho]
                  rw [if_neg hsel]
                exact hrhoOld.symm.trans hrhof
              have hchosen := selectedOfOutside u huX f huf (Or.inr hfc)
              exact hsel hchosen
          simpa [MissingColors] using hnotC
        · right
          have hnotBeta : beta ∉ PresentColors G phi u := by
            simpa [MissingColors] using hbetaMissing
          have hnotBetaRho : beta ∉ PresentColors G rho u := by
            intro hbPresent
            obtain ⟨f, huf, hrf⟩ := by
              simpa [PresentColors] using hbPresent
            apply hnotBeta
            simpa [PresentColors] using
              (show ∃ q, Incident G u q ∧ phi q = some beta from
                ⟨f, huf, (hbetaFixed f).1 hrf⟩)
          simpa [MissingColors] using hnotBetaRho
      refine ⟨Q, ?_, hQsupport⟩
      refine ⟨hQpath, ?_, hExit.2.2.1, hExit.2.2.2.1, hmissing, ?_⟩
      · rw [hQlength]
        exact hExit.2.1
      · intro w hw
        rw [hQsupport]
        exact hExit.2.2.2.2.2 w hw
    obtain ⟨Q₁, hQ₁, hQ₁Support⟩ := transportExit a₁ b₁ P₁ hP1
    obtain ⟨Q₂, hQ₂, hQ₂Support⟩ := transportExit a₂ b₂ P₂ hP2
    have hcMissingRho : c ∈ TreeMissingColors rho Tn := by
      unfold TreeMissingColors
      refine Finset.mem_biUnion.mpr ⟨x, hxT, ?_⟩
      rw [hrhoStable.2 x hxT]
      exact hcxMissing
    exact finish rho hrhoProper hrhoOne hrhoStable hcMissingRho
      Q₁ Q₂ hQ₁ hQ₂
