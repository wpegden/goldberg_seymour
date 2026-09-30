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

-- [TABLET NODE: Step1ZeroDividerAnchorPE]
lemma Step1ZeroDividerAnchorPE {V E : Type*}
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
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) : False := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let X : Finset V := TreeSequenceVertexSet base.core
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
  have hparallel := base.parallel hPE
  rcases hparallel with ⟨hsupport, hclosure, hunion⟩
  obtain ⟨unionCert⟩ := hunion
  let x : V := Tn.vertex base.supportPosition
  have hxT : x ∈ TreeSequenceVertexSet Tn := by
    simp [x, TreeSequenceVertexSet]
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab y hy
    unfold TreeSequenceVertexSet at hy ⊢
    simp only [Finset.mem_image] at hy ⊢
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i
  have augmentationVertices : ∀ {A B : TreeSequence G e0},
      TashkinovAugmentationSequence phi A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab
    unfold TashkinovAugmentationSequence at hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | @head A B hstep htail ih =>
        intro y hy
        apply ih
        exact initialVertices hstep.2.1 hy
  have hxPrefix : x ∈ TreeSequenceVertexSet
      (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt)) := by
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image]
    let i : Fin (base.supportPosition.val + 1) :=
      ⟨base.supportPosition.val, Nat.lt_succ_self _⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [TreeSequencePrefix, i, x]
  have hxR : x ∈ TreeSequenceVertexSet base.closure := by
    exact augmentationVertices hclosure.1 hxPrefix
  have hcoreVertices : X =
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
    simpa [X, Tn, n] using unionCert.vertexSet
  have hxX : x ∈ X := by
    rw [hcoreVertices]
    exact Finset.mem_union_left _ hxT
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
  have hcR : c ∈ TreeMissingColors phi base.closure := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨x, hxR, hcxMissing⟩
  have hlowerElem : ColoredVertexSetElementary G
      (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
      (TreeSequenceVertexSet Tn) := by
    by_cases honeRound : ett.rounds = 1
    · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
      have hTn : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
        apply congrArg (fun i : Fin (ett.rounds + 2) => ett.series.data.tree i)
        apply Fin.ext
        simp [Tn, n, honeRound]
      have hcol : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
        apply Fin.ext
        simp [honeRound]
      rw [hTn, hcol]
      exact htech.1
    · have hgt : 1 < ett.rounds := by omega
      obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett hMP hgt
      have hpredElem := hlower pred (by omega) (by omega) hpredMP
      have hp : ColoredVertexSetElementary G
          (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
          (TreeSequenceVertexSet
            (ett.series.data.tree ⟨ett.rounds, by omega⟩)) := hpredElem.1
      have heq : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
          (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        rfl
      rw [heq] at hp
      simpa [Tn, n] using hp
  have hcommon := ParallelCommonMissingClosed G k e0 input T phi phi ett
    hpositive base hphi hPE hlowerElem
  have hcClosed : TreeColorSetClosed G phi base.core {c} := by
    unfold TreeColorSetClosed at hcommon ⊢
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    exact hcommon c (Finset.mem_inter.mpr ⟨hcT, hcR⟩)
  have halphaClosed : TreeColorSetClosed G phi base.core {alpha} := by
    simpa [hstar] using hclosed
  have hP1 : TreeExitPath base.core phi alpha beta a₁ b₁ P₁ := by
    simpa [hstar] using hP₁
  have hP2 : TreeExitPath base.core phi alpha beta a₂ b₂ P₂ := by
    simpa [hstar] using hP₂
  have exitBoundary : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl u) (Sum.inl v)),
      TreeExitPath base.core phi alpha beta u v P →
      ∃ f : E,
        f ∈ BoundaryColorEdges G phi X beta ∧
        Incident G v f ∧ Sum.inr f ∈ P.support := by
    intro u v P hP
    rcases hP with ⟨_, _, huX, hvX, _, honly⟩
    let graph := TwoColorIncidenceGraph G phi alpha beta
    let S : Set (Sum V E) := {y | match y with
      | Sum.inl q => q ∈ X
      | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
    have hSv : Sum.inl v ∈ S := by
      simpa [S, X] using hvX
    have hSu : Sum.inl u ∉ S := by
      simpa [S, X] using huX
    obtain ⟨d, hd, hds, hdt⟩ :=
      P.reverse.exists_boundary_dart S hSv hSu
    have hadj := d.adj
    have hdmem : d.toProd.1 ∈ P.reverse.support :=
      P.reverse.dart_fst_mem_support_of_mem_darts hd
    have hdtmem : d.toProd.2 ∈ P.reverse.support :=
      P.reverse.dart_snd_mem_support_of_mem_darts hd
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
                (phi f = some alpha ∨ phi f = some beta) at hadj
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
        (phi f = some alpha ∨ phi f = some beta) := by
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
    have hfcolor : phi f = some beta := by
      rcases hfdata.2 with hfa | hfbeta
      · have hfalpha : f ∈ BoundaryColorEdges G phi X alpha := by
          simp [BoundaryColorEdges, hfb, hfa]
        have hempty := halphaClosed alpha (by simp)
        rw [hempty] at hfalpha
        simpa using hfalpha
      · exact hfbeta
    have hqP : Sum.inl q ∈ P.support := by
      have hqrev : Sum.inl q ∈ P.reverse.support := by
        rw [← hq]
        exact hdmem
      simpa [SimpleGraph.Walk.support_reverse] using hqrev
    have hqv : q = v := (honly q (by simpa [X] using hqX)).mp hqP
    have hfP : Sum.inr f ∈ P.support := by
      have hfrev : Sum.inr f ∈ P.reverse.support := by
        rw [← hf]
        exact hdtmem
      simpa [SimpleGraph.Walk.support_reverse] using hfrev
    subst q
    exact ⟨f, by simp [BoundaryColorEdges, hfb, hfcolor], hfdata.1, hfP⟩
  obtain ⟨f₁, hf₁Boundary, hf₁Incident, hf₁Support⟩ :=
    exitBoundary a₁ b₁ P₁ hP1
  obtain ⟨f₂, hf₂Boundary, hf₂Incident, hf₂Support⟩ :=
    exitBoundary a₂ b₂ P₂ hP2
  have hbetaPresent : beta ∈ PresentColors G phi x := by
    have hbetaNotMissing : beta ∉ MissingColors G phi x := by
      intro hbetaMissing
      have hbetaT : beta ∈ TreeMissingColors phi Tn := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨x, hxT, hbetaMissing⟩
      have hbetaR : beta ∈ TreeMissingColors phi base.closure := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨x, hxR, hbetaMissing⟩
      have hbetaClosed : TreeColorSetClosed G phi base.core {beta} := by
        unfold TreeColorSetClosed at hcommon ⊢
        intro d hd
        have hdb : d = beta := Finset.mem_singleton.mp hd
        subst d
        exact hcommon beta (Finset.mem_inter.mpr ⟨hbetaT, hbetaR⟩)
      have hempty := hbetaClosed beta (by simp)
      rw [hempty] at hf₁Boundary
      simpa using hf₁Boundary
    simpa [MissingColors] using hbetaNotMissing
  have hcNeBeta : c ≠ beta := by
    intro hcb
    subst c
    have hnot : beta ∉ PresentColors G phi x := by
      simpa [MissingColors] using hcxMissing
    exact hnot hbetaPresent
  have finish : ∀ (sigma : PartialEdgeColoring E k),
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi sigma →
      c ∈ TreeMissingColors sigma base.core →
      TreeColorSetClosed G sigma base.core {c} →
      ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk
          (Sum.inl a₁) (Sum.inl b₁))
        (Q₂ : (TwoColorIncidenceGraph G sigma c beta).Walk
          (Sum.inl a₂) (Sum.inl b₂)),
        TreeExitPath base.core sigma c beta a₁ b₁ Q₁ →
        TreeExitPath base.core sigma c beta a₂ b₂ Q₂ → False := by
    intro sigma hsProper hsOne hsCombined hcMissingCore hcClosedCore
      Q₁ Q₂ hQ₁ hQ₂
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
      rw [hsCombined.1.2 x hxT]
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
    have hmeetX : ∃ v ∈ TreeSequenceVertexSet base.core,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl x) :=
      ⟨x, by simpa [X] using hxX, rfl⟩
    have hmeet₁ : ∃ v ∈ TreeSequenceVertexSet base.core,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₁) := by
      refine ⟨b₁, hQ₁.2.2.2.1, ?_⟩
      change graph.connectedComponentMk (Sum.inl b₁) =
        graph.connectedComponentMk (Sum.inl a₁)
      exact (SimpleGraph.ConnectedComponent.sound Q₁.reachable).symm
    have hmeet₂ : ∃ v ∈ TreeSequenceVertexSet base.core,
        Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₂) := by
      refine ⟨b₂, hQ₂.2.2.2.1, ?_⟩
      change graph.connectedComponentMk (Sum.inl b₂) =
        graph.connectedComponentMk (Sum.inl a₂)
      exact (SimpleGraph.ConnectedComponent.sound Q₂.reachable).symm
    have ha₁x : a₁ ≠ x := by
      intro h
      exact hQ₁.2.2.1 (h ▸ (by simpa [X] using hxX))
    have ha₂x : a₂ ≠ x := by
      intro h
      exact hQ₂.2.2.1 (h ▸ (by simpa [X] using hxX))
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
    have hinter := (interchange G k e0 input T phi sigma ett hMP hpositive
      hlower hPE base hsProper hsOne hsCombined c beta).2.2.1
      hcMissingCore hcClosedCore
    rcases hdistinct with hneComp | hneComp
    · exact hneComp (hinter (Sum.inl x) (Sum.inl a₁)
        hpathX hpath₁ hmeetX hmeet₁)
    · exact hneComp (hinter (Sum.inl x) (Sum.inl a₂)
        hpathX hpath₂ hmeetX hmeet₂)
  by_cases hac : alpha = c
  · subst alpha
    have stableRefl : ∀ (S : TreeSequence G e0) (C : Finset (Fin k)),
        StableColoring S C phi phi := by
      intro S C
      constructor
      · intro f hf hcolor
        rfl
      · intro v hv
        rfl
    have hcombined : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi phi :=
      ⟨stableRefl Tn _, stableRefl base.closure ∅⟩
    have hcMissingCore : c ∈ TreeMissingColors phi base.core := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr
        ⟨x, by simpa [X] using hxX, hcxMissing⟩
    exact finish phi hproper hone hcombined hcMissingCore hcClosed P₁ P₂ hP1 hP2
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
        rw [hempty] at hfalpha
        simpa using hfalpha
      · have hfcolor : f ∈ BoundaryColorEdges G phi X c := by
          simp [BoundaryColorEdges, hfb, hfc]
        have hempty := hcClosed c (by simp)
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
    have hrecolorCore : OutsideKempeRecoloring base.core phi rho alpha c := by
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
    have hTsubset : TreeSequenceVertexSet Tn ⊆ X := by
      rw [hcoreVertices]
      exact Finset.subset_union_left
    have hRsubset : TreeSequenceVertexSet base.closure ⊆ X := by
      rw [hcoreVertices]
      exact Finset.subset_union_right
    have restrictRecolor : ∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ X →
        OutsideKempeRecoloring S phi rho alpha c := by
      intro S hsub
      rcases hrecolorCore with ⟨hneac, roots', hout, hformula⟩
      refine ⟨hneac, roots', ?_, hformula⟩
      intro z hz v hvComponent hvS
      exact hout z hz v hvComponent (hsub hvS)
    have hrecolorT := restrictRecolor Tn hTsubset
    have hrecolorR := restrictRecolor base.closure hRsubset
    have hstableCore := OutsideKempeRecoloringStable G e0 base.core ∅
      phi rho alpha c hproper hone hrecolorCore
    have hstableT := OutsideKempeRecoloringStable G e0 Tn
      (TashkinovStoredColors ett.series.data n)
      phi rho alpha c hproper hone hrecolorT
    have hstableR := OutsideKempeRecoloringStable G e0 base.closure ∅
      phi rho alpha c hproper hone hrecolorR
    have hrhoProper : IsProperEdgeColoring G rho := hstableCore.1
    have hrhoOne : IsOneEdgeUncolored rho e0 := hstableCore.2.1
    have hrhoCombined : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi rho := by
      exact ⟨hstableT.2.2.1, hstableR.2.2.1⟩
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
        TreeExitPath base.core phi alpha beta u v P →
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
        TreeExitPath base.core phi alpha beta u v P →
        ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk
            (Sum.inl u) (Sum.inl v),
          TreeExitPath base.core rho c beta u v Q ∧
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
    have hcMissingRho : c ∈ TreeMissingColors rho base.core := by
      unfold TreeMissingColors
      refine Finset.mem_biUnion.mpr ⟨x, by simpa [X] using hxX, ?_⟩
      rw [hstableT.2.2.1.2 x hxT]
      exact hcxMissing
    have hcClosedRho : TreeColorSetClosed G rho base.core {c} := by
      unfold TreeColorSetClosed
      intro d hd
      have hdc : d = c := Finset.mem_singleton.mp hd
      subst d
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      have hfBoundary : f ∈ BoundaryEdges G X ∧ rho f = some c := by
        simpa [BoundaryColorEdges] using hf
      have hfIncident : TreeIncidentEdge base.core f := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hfBoundary
        obtain ⟨u, huX, v, hvX, hends⟩ := hfBoundary.1
        exact ⟨u, by simpa [X] using huX, by
          unfold Incident
          rw [hends]
          exact Sym2.mem_mk_left _ _⟩
      have hfixed := hstableCore.2.2.2.2 f hfIncident
      have hfOld : f ∈ BoundaryColorEdges G phi X c := by
        have hcolor : phi f = some c := by
          rw [← hfixed]
          exact hfBoundary.2
        simp [BoundaryColorEdges, hfBoundary.1, hcolor]
      have hempty := hcClosed c (by simp)
      rw [hempty] at hfOld
      simpa using hfOld
    exact finish rho hrhoProper hrhoOne hrhoCombined hcMissingRho hcClosedRho
      Q₁ Q₂ hQ₁ hQ₂
