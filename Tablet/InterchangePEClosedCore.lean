import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.DefectiveColor
import Tablet.Degree
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.Incident
import Tablet.InterchangePEClosureConstituent
import Tablet.InterchangePECommonMissingClosed
import Tablet.InterchangePETreeAwayFromDelta
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.OutsideTreeColorSwap
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelExtensionColor
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColorSetClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent
import Tablet.sc2
import Tablet.ElementaryClosedNoninterchangeableDisjointExitPaths
import Tablet.ParallelBaseFourCommonMissingColors
import Tablet.P2634_T1_PETerminalFacts
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TwoColorComponentNearestSegment
import Tablet.MissingColorIncidenceEndpoint

-- [TABLET NODE: InterchangePEClosedCore]
theorem InterchangePEClosedCore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
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
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    alpha ∈ TreeMissingColors sigma base.core →
      TreeColorSetClosed G sigma base.core {alpha} →
      TreeInterchangeable G base.core sigma alpha beta := by
-- BODY
  classical
  intro halpha hclosed
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let X := TreeSequenceVertexSet Tn
  let Y := TreeSequenceVertexSet base.closure
  let U := TreeSequenceVertexSet base.core
  obtain ⟨hchosen, hclosure, ⟨hunion⟩⟩ := base.parallel hPE
  have hU : U = X ∪ Y := hunion.vertexSet
  have hgen := ett.generatingColoring
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hpreserved := CombinedStableClosurePreserved G k e0 input T
    generating generating sigma ett hpositive base hgen hPE
    hproperGen honeGen hproper hone hstable
  let baseSigma : HierarchyBase ett sigma := {
    core := base.core
    closure := base.closure
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← hstable.1.2 v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [hstable.1.2 v hv]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1,
      hpreserved.2.2, (base.parallel hp).2.2⟩
    nonparallel := base.nonparallel }
  have helem : ColoredVertexSetElementary G sigma U :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE sigma hproper hone hstable.1 baseSigma
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have htriple : KTriple G k e0 input := by
      cases ett.series.certified 0 with
      | initial => assumption
    exact htriple.2.2.1
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  have hterminal : ∃ (gamma delta : Fin k) (f : E),
      ett.series.data.gamma n = some gamma ∧
      ett.series.data.delta n = some delta ∧
      ett.series.data.connectingEdges n = {f} ∧
      ett.series.data.stored n = {delta, gamma} := by
    have hp : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by simpa [hq, n] using hPE
    generalize ht : q.succ = slot at hp
    have cert := ett.series.certified slot
    cases cert with
    | initial => exact (Fin.succ_ne_zero q ht).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      rw [currentKind] at hp
      cases hp
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      rw [currentKind] at hp
      cases hp
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hh := congrArg Fin.val ht
        simp at hh
        omega
      subst i
      exact ⟨gamma, choice.color, choice.edge,
        by simpa [hq] using currentGamma,
        by simpa [hq] using currentDelta,
        by simpa [hq] using currentEdges,
        by simpa [hq] using currentStored⟩
  obtain ⟨gamma, delta, f, hgamma, hdelta, hf, hstored⟩ := hterminal
  have hdeltaControl : delta ∈ TreeMissingColors generating Tn ∪
      TashkinovStoredColors ett.series.data n := by
    by_cases hm : delta ∈ TreeMissingColors generating Tn
    · exact Finset.mem_union_left _ hm
    · apply Finset.mem_union_right
      simp only [TashkinovStoredColors]
      rw [if_neg (show n.val ≠ 0 by simp [n]; omega)]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [hstored]
      · simpa [Tn, n, ← hgen] using hm
  let seed := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hseedY : TreeSequenceVertexSet seed ⊆ Y :=
    TreeSequenceInitialSegmentVertexSetSubset
      (TashkinovAugmentationSequenceInitialSegment generating seed base.closure
        hclosure.1)
  have hdeltaBoundary : ∀ g ∈ BoundaryColorEdges G sigma X delta,
      ∃ w ∈ Y, Incident G w g := by
    intro g hg
    have hgb := (Finset.mem_filter.mp hg).1
    have hgc := (Finset.mem_filter.mp hg).2
    obtain ⟨v, hv, r, hr, hend⟩ := by
      simpa [BoundaryEdges] using hgb
    have hinc : TreeIncidentEdge Tn g :=
      ⟨v, hv, by simp [Incident, hend]⟩
    have hfix := (sc1 G e0 Tn (TashkinovStoredColors ett.series.data n)
      generating sigma hproperGen honeGen hproper hone).mp hstable.1 g hinc
      (Or.inr ⟨delta, hdeltaControl, hgc⟩)
    have hgg : g ∈ BoundaryColorEdges G generating X delta := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨hgb, hfix.symm.trans hgc⟩
    have hb := (HkuParallelBoundaryStructure G k ett.rounds e0 input
      ett.series q f delta gamma (Tn.vertex base.supportPosition)
      (by simpa [hq, n] using hPE) (by simpa [hq] using hf)
      (by simpa [hq] using hdelta) (by simpa [hq] using hgamma)
      (by simpa [hq] using hchosen)).2.1
    have hgg' : g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) delta := by
      simpa [hq, Tn, n, ← hgen] using hgg
    obtain ⟨w, hw, hwi⟩ := hb g hgg'
    have hw' : TreeVertexOrder Tn w (Tn.vertex base.supportPosition) := by
      simpa [hq, Tn] using hw
    obtain ⟨i, j, hi, hj, hij⟩ := hw'
    have hj' : j = base.supportPosition := Tn.vertex_injective hj
    subst j
    have hwseed : w ∈ TreeSequenceVertexSet seed := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      refine ⟨(⟨i.val, by omega⟩ : Fin (base.supportPosition.val + 1)), ?_⟩
      simpa [seed, TreeSequencePrefix] using hi
    exact ⟨w, hseedY hwseed, hwi⟩
  by_cases hab : alpha = beta
  · intro z w hz
    exact (hz.1 hab).elim
  change alpha ≠ beta at hab
  by_contra hnot
  obtain ⟨u1, s1, u2, s2, P1, P2, hP1, hP2, hdisjoint, hu12, hs12⟩ :=
    ElementaryClosedNoninterchangeableDisjointExitPaths G base.core sigma
      hproper helem alpha beta hab hclosed hnot
  have stableMissing {A : TreeSequence G e0} {C : Finset (Fin k)}
      {rho tau : PartialEdgeColoring E k} (hh : StableColoring A C rho tau) :
      TreeMissingColors tau A = TreeMissingColors rho A := by
    ext d
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hd⟩
      exact ⟨x, hx, by rw [← hh.2 x hx]; exact hd⟩
    · rintro ⟨x, hx, hd⟩
      exact ⟨x, hx, by rw [hh.2 x hx]; exact hd⟩
  have missingGen (x : V) (hx : x ∈ U) :
      MissingColors G sigma x = MissingColors G generating x := by
    rw [hU] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hstable.1.2 x hx
    · exact hstable.2.2 x hx
  have helemGen : ColoredVertexSetElementary G generating U := by
    intro x hx y hy hxy
    rw [← missingGen x hx, ← missingGen y hy]
    exact helem hx hy hxy
  have hfour : 4 ≤ (TreeMissingColors sigma Tn ∩
      TreeMissingColors sigma base.closure).card := by
    rw [stableMissing hstable.1, stableMissing hstable.2]
    exact ParallelBaseFourCommonMissingColors ett base hPE
      hproperGen honeGen hdegree helemGen
  have hcolor : ∃ c ∈ TreeMissingColors sigma Tn ∩
      TreeMissingColors sigma base.closure,
      c ≠ alpha ∧ c ≠ beta ∧ c ≠ delta := by
    by_contra hn
    push Not at hn
    have hsubset : TreeMissingColors sigma Tn ∩
        TreeMissingColors sigma base.closure ⊆ {alpha, beta, delta} := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases ha : c = alpha
      · exact Or.inl ha
      by_cases hb : c = beta
      · exact Or.inr (Or.inl hb)
      exact Or.inr (Or.inr (hn c hc ha hb))
    have hle := Finset.card_le_card hsubset
    have hthree : ({alpha, beta, delta} : Finset (Fin k)).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans
          (by simp)) 1)
    omega
  obtain ⟨c, hc, hca, hcb, hcd⟩ := hcolor
  obtain ⟨v, hvX, hcv⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hc).1
  obtain ⟨w, hwY, hcw⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hc).2
  have hvY : v ∈ Y := by
    have hvU : v ∈ U := by rw [hU]; exact Finset.mem_union_left _ hvX
    have hwU : w ∈ U := by rw [hU]; exact Finset.mem_union_right _ hwY
    have hvw : v = w := by
      by_contra hvw
      exact (Finset.disjoint_left.mp (helem hvU hwU hvw)) hcv hcw
    exact hvw ▸ hwY
  have hcclosed := InterchangePECommonMissingClosed G k e0 input T
    generating sigma ett hMP hpositive hlower hPE base hproper hone hstable c
    (Finset.mem_inter.mp hc).1 (Finset.mem_inter.mp hc).2
  let psi := OutsideTreeColorSwap base.core sigma alpha c
  let flip := Equiv.swap (some alpha) (some c)
  have fixed (e : E) (he : TreeIncidentEdge base.core e) :
      psi e = sigma e := by
    simp [psi, OutsideTreeColorSwap, he]
  have boundaryOutside {r : V} {e : E} (hr : r ∉ U)
      (hre : Incident G r e) (he : TreeIncidentEdge base.core e) :
      e ∈ BoundaryEdges G U := by
    obtain ⟨x, hx, hxe⟩ := he
    have hxr : x ≠ r := by rintro rfl; exact hr hx
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, r, hr, (Sym2.mem_and_mem_iff hxr).mp ⟨hxe, hre⟩⟩
  have boundaryAvoid {e : E} (he : e ∈ BoundaryEdges G U) :
      sigma e ≠ some alpha ∧ sigma e ≠ some c := by
    constructor
    · intro ha
      have hm : e ∈ BoundaryColorEdges G sigma U alpha :=
        Finset.mem_filter.mpr ⟨he, ha⟩
      rw [hclosed alpha (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty e hm
    · intro hc'
      have hm : e ∈ BoundaryColorEdges G sigma U c :=
        Finset.mem_filter.mpr ⟨he, hc'⟩
      rw [hcclosed c (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty e hm
  have outside (r : V) (hr : r ∉ U) (e : E) (hre : Incident G r e) :
      psi e = flip (sigma e) := by
    by_cases he : TreeIncidentEdge base.core e
    · obtain ⟨ha, hc'⟩ := boundaryAvoid (boundaryOutside hr hre he)
      simp [fixed e he, flip, Equiv.swap_apply_def, ha, hc']
    · simp [psi, OutsideTreeColorSwap, he, flip, Equiv.swap_apply_def]
  have hproperPsi : IsProperEdgeColoring G psi := by
    intro e g d heg hadj hed hgd
    obtain ⟨r, hre, hrg⟩ := hadj
    have hold : sigma e = sigma g := by
      by_cases hr : r ∈ U
      · rw [← fixed e ⟨r, hr, hre⟩, ← fixed g ⟨r, hr, hrg⟩]
        exact hed.trans hgd.symm
      · apply flip.injective
        rw [← outside r hr e hre, ← outside r hr g hrg]
        exact hed.trans hgd.symm
    cases he : sigma e with
    | none =>
      by_cases hr : r ∈ U
      · rw [fixed e ⟨r, hr, hre⟩, he] at hed
        cases hed
      · rw [outside r hr e hre, he] at hed
        simp [flip, Equiv.swap_apply_def] at hed
    | some d' =>
      exact hproper heg ⟨r, hre, hrg⟩ he (hold.symm.trans he)
  have hnone (e : E) : psi e = none ↔ sigma e = none := by
    by_cases he : TreeIncidentEdge base.core e
    · rw [fixed e he]
    · simp only [psi, OutsideTreeColorSwap, he, if_false]
      by_cases ha : sigma e = some alpha
      · simp [ha]
      by_cases hc' : sigma e = some c
      · simp [ha, hc', hca]
      · simp [ha, hc']
  have honePsi : IsOneEdgeUncolored psi e0 := by
    refine ⟨(hnone e0).mpr hone.1, ?_⟩
    intro e he
    obtain ⟨d, hd⟩ := hone.2 e he
    cases hpsi : psi e with
    | none =>
      have hn := (hnone e).mp hpsi
      rw [hd] at hn
      cases hn
    | some d' => exact ⟨d', rfl⟩
  have missingFixed (x : V) (hx : x ∈ U) :
      MissingColors G psi x = MissingColors G sigma x := by
    ext d
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hn ⟨e, hxe, hed⟩
      exact hn ⟨e, hxe, (fixed e ⟨x, hx, hxe⟩).trans hed⟩
    · intro hn ⟨e, hxe, hed⟩
      exact hn ⟨e, hxe, (fixed e ⟨x, hx, hxe⟩).symm.trans hed⟩
  have hstablePsi : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) generating psi := by
    constructor
    · constructor
      · intro e he hc'
        obtain ⟨x, hx, hxe⟩ := he
        have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_left _ hx
        exact (fixed e ⟨x, hxU, hxe⟩).trans
          (hstable.1.1 e ⟨x, hx, hxe⟩ hc')
      · intro x hx
        have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_left _ hx
        exact (missingFixed x hxU).trans (hstable.1.2 x hx)
    · constructor
      · intro e he hc'
        obtain ⟨x, hx, hxe⟩ := he
        have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_right _ hx
        exact (fixed e ⟨x, hxU, hxe⟩).trans
          (hstable.2.1 e ⟨x, hx, hxe⟩ hc')
      · intro x hx
        have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_right _ hx
        exact (missingFixed x hxU).trans (hstable.2.2 x hx)
  have colorOutside (r : V) (hr : r ∉ U) (e : E) (hre : Incident G r e) :
      (psi e = some c ↔ sigma e = some alpha) ∧
      (psi e = some beta ↔ sigma e = some beta) := by
    rw [outside r hr e hre]
    by_cases ha : sigma e = some alpha <;>
      by_cases hc' : sigma e = some c <;>
      simp [flip, Equiv.swap_apply_def, ha, hc', hca, hca.symm,
        hcb, hcb.symm, hab, hab.symm]
  have missingOutside (r : V) (hr : r ∉ U)
      (hm : alpha ∈ MissingColors G sigma r ∨ beta ∈ MissingColors G sigma r) :
      c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r := by
    rcases hm with hm | hm
    · left
      have hn : ∀ e, Incident G r e → sigma e ≠ some alpha := by
        simpa [MissingColors, PresentColors] using hm
      have hn' : ∀ e, Incident G r e → psi e ≠ some c := by
        intro e he hd
        exact hn e he ((colorOutside r hr e he).1.mp hd)
      simpa [MissingColors, PresentColors] using hn'
    · right
      have hn : ∀ e, Incident G r e → sigma e ≠ some beta := by
        simpa [MissingColors, PresentColors] using hm
      have hn' : ∀ e, Incident G r e → psi e ≠ some beta := by
        intro e he hd
        exact hn e he ((colorOutside r hr e he).2.mp hd)
      simpa [MissingColors, PresentColors] using hn'
  let H := TwoColorIncidenceGraph G psi c beta
  have leaf (r : V)
      (hm : c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r) :
      Set.Subsingleton (H.neighborSet (Sum.inl r)) := by
    have hd : @SimpleGraph.degree _ H (Sum.inl r) (Fintype.ofFinite _) ≤ 1 := by
      rcases hm with hm | hm
      · exact MissingColorIncidenceEndpoint G psi c beta hcb hproperPsi r hm
      · have hgraph : H = TwoColorIncidenceGraph G psi beta c := by
          ext x y
          cases x <;> cases y <;> simp [H, TwoColorIncidenceGraph, or_comm]
        rw [hgraph]
        exact MissingColorIncidenceEndpoint G psi beta c hcb.symm hproperPsi r hm
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx y hy
    exact Finset.card_le_one_iff.mp hd
      (by simpa [SimpleGraph.mem_neighborFinset] using hx)
      (by simpa [SimpleGraph.mem_neighborFinset] using hy)
  -- Transport exact incidence segments; no old full component is reused after the swap.
  have transport (r : V) (hr : r ∉ U)
      (hmeet : ∃ x ∈ U,
        Sum.inl x ∈ TwoColorComponent G sigma alpha beta (Sum.inl r)) :
      ∃ s ∈ U, (beta = delta → s ∈ Y) ∧
        H.Reachable (Sum.inl r) (Sum.inl s) := by
    obtain ⟨m, hm, pv, pe, hpv, hpe, hs, hlast, hout, hvcomp,
      hecomp, hcolors, hends, hfresh⟩ :=
      TwoColorComponentNearestSegment G sigma base.core alpha beta r
        hproper hab hr hmeet
    let s := pv 0
    let z : Fin m := ⟨0, by omega⟩
    have hend0 : G.ends (pe z) = s(s, pv z.succ) := by
      simpa [s, z] using hends z
    have hb0 : pe z ∈ BoundaryEdges G U := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨s, hs, pv z.succ, hout z, hend0⟩
    have hcolor0 : sigma (pe z) = some beta :=
      (hcolors z).resolve_left (boundaryAvoid hb0).1
    have hinc0 : TreeIncidentEdge base.core (pe z) :=
      ⟨s, hs, by simp [Incident, hend0]⟩
    have hsY : beta = delta → s ∈ Y := by
      intro hbd
      by_cases hsX : s ∈ X
      · have hoX : pv z.succ ∉ X := by
          intro hx
          apply hout z
          change pv z.succ ∈ U
          rw [hU]
          exact Finset.mem_union_left _ hx
        have hbX : pe z ∈ BoundaryColorEdges G sigma X delta := by
          apply Finset.mem_filter.mpr
          refine ⟨?_, by simpa [hbd] using hcolor0⟩
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨s, hsX, pv z.succ, hoX, hend0⟩
        obtain ⟨w, hwY, hwi⟩ := hdeltaBoundary (pe z) hbX
        have hw : w = s := by
          simp only [Incident, hend0, Sym2.mem_iff] at hwi
          rcases hwi with hw | hw
          · exact hw
          · exfalso
            apply hout z
            change pv z.succ ∈ U
            rw [← hw, hU]
            exact Finset.mem_union_right _ hwY
        exact hw ▸ hwY
      · have hsU : s ∈ U := hs
        rw [hU] at hsU
        exact (Finset.mem_union.mp hsU).resolve_left hsX
    have newColors (i : Fin m) :
        psi (pe i) = some c ∨ psi (pe i) = some beta := by
      by_cases hi : i.val = 0
      · have hiz : i = z := by apply Fin.ext; exact hi
        subst i
        exact Or.inr ((fixed (pe z) hinc0).trans hcolor0)
      · let j : Fin m := ⟨i.val - 1, by omega⟩
        have hji : j.succ = i.castSucc := by
          apply Fin.ext
          simp [j]
          omega
        have hleftout : pv i.castSucc ∉ U := by
          rw [← hji]
          exact hout j
        have hnotinc : ¬ TreeIncidentEdge base.core (pe i) := by
          rintro ⟨x, hx, hxi⟩
          simp only [Incident, hends i, Sym2.mem_iff] at hxi
          rcases hxi with hxi | hxi
          · exact hleftout (hxi ▸ hx)
          · exact hout i (hxi ▸ hx)
        rcases hcolors i with ha | hb
        · exact Or.inl (by simp [psi, OutsideTreeColorSwap, hnotinc, ha])
        · exact Or.inr (by
            simp [psi, OutsideTreeColorSwap, hnotinc, hb, hab.symm, hcb.symm])
    have stepLeft (i : Fin m) : H.Adj (Sum.inl (pv i.castSucc)) (Sum.inr (pe i)) :=
      ⟨by simp [Incident, hends i], newColors i⟩
    have stepRight (i : Fin m) : H.Adj (Sum.inr (pe i)) (Sum.inl (pv i.succ)) :=
      ⟨by simp [Incident, hends i], newColors i⟩
    have reach : ∀ t (ht : t ≤ m),
        H.Reachable (Sum.inl s) (Sum.inl (pv ⟨t, by omega⟩)) := by
      intro t
      induction t with
      | zero => intro ht; exact SimpleGraph.Reachable.refl _
      | succ t ih =>
        intro ht
        let i : Fin m := ⟨t, by omega⟩
        exact (ih (by omega)).trans
          ((stepLeft i).reachable.trans (stepRight i).reachable)
    refine ⟨s, hs, hsY, ?_⟩
    have hr' := (reach m le_rfl).symm
    change H.Reachable (Sum.inl (pv (Fin.last m))) (Sum.inl s) at hr'
    rw [hlast] at hr'
    exact hr'
  have oldMeet (u s : V)
      (P : (TwoColorIncidenceGraph G sigma alpha beta).Walk (Sum.inl u) (Sum.inl s))
      (hs : s ∈ U) :
      ∃ x ∈ U, Sum.inl x ∈ TwoColorComponent G sigma alpha beta (Sum.inl u) := by
    refine ⟨s, hs, ?_⟩
    exact SimpleGraph.ConnectedComponent.eq.mpr P.reachable.symm
  obtain ⟨t1, ht1, ht1Y, hr1⟩ := transport u1 hP1.2.2.1
    (oldMeet u1 s1 P1 hP1.2.2.2.1)
  obtain ⟨t2, ht2, ht2Y, hr2⟩ := transport u2 hP2.2.2.1
    (oldMeet u2 s2 P2 hP2.2.2.2.1)
  have hm1 := missingOutside u1 hP1.2.2.1 hP1.2.2.2.2.1
  have hm2 := missingOutside u2 hP2.2.2.1 hP2.2.2.2.2.1
  have hvU : v ∈ U := by rw [hU]; exact Finset.mem_union_left _ hvX
  have hcvPsi : c ∈ MissingColors G psi v := by
    rw [missingFixed v hvU]
    exact hcv
  have hcX : c ∈ TreeMissingColors psi Tn :=
    Finset.mem_biUnion.mpr ⟨v, hvX, hcvPsi⟩
  have hcY : c ∈ TreeMissingColors psi base.closure :=
    Finset.mem_biUnion.mpr ⟨v, hvY, hcvPsi⟩
  have hinterY := InterchangePEClosureConstituent G k e0 input T
    generating psi ett hMP hpositive hlower hPE base hproperPsi honePsi
    hstablePsi c beta hcY
  have selfMem (r : V) : Sum.inl r ∈ TwoColorComponent G psi c beta (Sum.inl r) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have hvPath : TwoColorPathComponent G psi c beta (Sum.inl v) :=
    ⟨hcb, Sum.inl v, selfMem v, leaf v (Or.inl hcvPsi)⟩
  have equalRoot (r s : V) (hs : s ∈ U)
      (hsY : beta = delta → s ∈ Y)
      (hr : H.Reachable (Sum.inl r) (Sum.inl s))
      (hm : c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r) :
      TwoColorComponent G psi c beta (Sum.inl r) =
        TwoColorComponent G psi c beta (Sum.inl v) := by
    have hrPath : TwoColorPathComponent G psi c beta (Sum.inl r) :=
      ⟨hcb, Sum.inl r, selfMem r, leaf r hm⟩
    have hsC : Sum.inl s ∈ TwoColorComponent G psi c beta (Sum.inl r) :=
      SimpleGraph.ConnectedComponent.eq.mpr hr.symm
    by_cases hbd : beta = delta
    · exact hinterY _ _ hrPath hvPath ⟨s, hsY hbd, hsC⟩
        ⟨v, hvY, selfMem v⟩
    · rw [hU] at hs
      rcases Finset.mem_union.mp hs with hsX | hsY'
      · have hinterX := InterchangePETreeAwayFromDelta G k e0 input T
          generating psi ett hMP hpositive hlower hPE base hproperPsi honePsi
          hstablePsi (Tn.vertex base.supportPosition) gamma delta c beta
          hchosen hgamma hdelta hcX hcd hbd
        exact hinterX _ _ hrPath hvPath ⟨s, hsX, hsC⟩
          ⟨v, hvX, selfMem v⟩
      · exact hinterY _ _ hrPath hvPath ⟨s, hsY', hsC⟩
          ⟨v, hvY, selfMem v⟩
  have heq1 := equalRoot u1 t1 ht1 ht1Y hr1 hm1
  have heq2 := equalRoot u2 t2 ht2 ht2Y hr2 hm2
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G psi c beta hproperPsi (Sum.inl v)
  have endpoint (r : V)
      (hr : Sum.inl r ∈ TwoColorComponent G psi c beta (Sum.inl v))
      (hleaf : Set.Subsingleton (H.neighborSet (Sum.inl r))) :
      Sum.inl r = a ∨ Sum.inl r = b := by
    have hrp : Sum.inl r ∈ p.support := by
      change Sum.inl r ∈ {x | x ∈ p.support}
      rw [hsupport]
      exact hr
    by_contra hn
    push Not at hn
    exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hleaf) hrp
  have hu1C : Sum.inl u1 ∈ TwoColorComponent G psi c beta (Sum.inl v) := by
    rw [← heq1]
    exact selfMem u1
  have hu2C : Sum.inl u2 ∈ TwoColorComponent G psi c beta (Sum.inl v) := by
    rw [← heq2]
    exact selfMem u2
  have end1 := endpoint u1 hu1C (leaf u1 hm1)
  have end2 := endpoint u2 hu2C (leaf u2 hm2)
  have endv := endpoint v (selfMem v) (leaf v (Or.inl hcvPsi))
  have hu1v : u1 ≠ v := by rintro rfl; exact hP1.2.2.1 hvU
  have hu2v : u2 ≠ v := by rintro rfl; exact hP2.2.2.1 hvU
  have hn12 : (Sum.inl u1 : Sum V E) ≠ Sum.inl u2 := by simpa using hu12
  have hn1v : (Sum.inl u1 : Sum V E) ≠ Sum.inl v := by simpa using hu1v
  have hn2v : (Sum.inl u2 : Sum V E) ≠ Sum.inl v := by simpa using hu2v
  rcases end1 with h1 | h1
  · rcases end2 with h2 | h2
    · exact hn12 (h1.trans h2.symm)
    · rcases endv with hv | hv
      · exact hn1v (h1.trans hv.symm)
      · exact hn2v (h2.trans hv.symm)
  · rcases end2 with h2 | h2
    · rcases endv with hv | hv
      · exact hn2v (h2.trans hv.symm)
      · exact hn1v (h1.trans hv.symm)
    · exact hn12 (h1.trans h2.symm)
