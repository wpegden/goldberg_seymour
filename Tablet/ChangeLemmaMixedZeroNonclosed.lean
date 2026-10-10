import Tablet.BoundaryColorEdges
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.GoodHierarchyNewMissingClosed
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyLEMStable
import Tablet.HierarchyPathNumber
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchySplitter
import Tablet.HkuTreeColorsControlled
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.OutsideKempeRecoloringStable
import Tablet.ParallelCommonMissingClosed
import Tablet.PresentColors
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
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
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.interchange
import Tablet.rutcor
import Tablet.sc2
import Tablet.step1
import Tablet.InterchangePECommonMissingClosed
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.HierarchyFirstMissingPositionPrefixCutoff

-- [TABLET NODE: ChangeLemmaMixedZeroNonclosed]
theorem ChangeLemmaMixedZeroNonclosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
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
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (horderedUnused :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))
    (hlocation :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      va ∈ TreeSequenceVertexSet A ∧
        vb ∉ TreeSequenceVertexSet A)
    (hbranch :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      H.dividerCount = 0 ∧
        ¬ TreeColorSetClosed G phi A {alpha} ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn))
 :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    sameComponent := by
-- BODY
  set_option maxHeartbeats 4000000 in
  · classical
    clear hfewer hlarge
    let H := C.hierarchy
    let A := base.core
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let ia := HierarchyFirstMissingPosition phi T alpha
    let ib := HierarchyFirstMissingPosition phi T beta
    let va := T.vertex ia
    let vb := T.vertex ib
    have hzero : H.dividerCount = 0 := hbranch.1
    have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) = A := by
      have hz : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
        Fin.ext hzero
      rw [hz]
      rfl
    have hstarC : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A := hstar
    have hfirst : H.stage ⟨1, by omega⟩ = T := by
      have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [hi]
      exact H.terminalStage
    have hAT : TreeSequenceInitialSegment A T := by
      simpa only [hfirst] using H.coreInsideFirst
    have hvaA : va ∈ TreeSequenceVertexSet A := by
      simpa only [hstarC] using hlocation.1
    have hvbA : vb ∉ TreeSequenceVertexSet A := by
      simpa only [hstarC] using hlocation.2
    have prefixPosition {X Y : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y) (i : Fin (Y.length + 1)) :
        Y.vertex i ∈ TreeSequenceVertexSet X ↔ i.val ≤ X.length := by
      clear * - hXY
      constructor
      · intro hv
        obtain ⟨j, _, hj⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
        have he := Y.vertex_injective ((hXY.2.1 j).trans hj)
        have hv := congrArg Fin.val he
        simp only [Fin.val_castLE] at hv
        have := j.isLt
        omega
      · intro hi
        let j : Fin (X.length + 1) := ⟨i.val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hXY.1) j = i := Fin.ext rfl
        exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨j, Finset.mem_univ _,
          (hXY.2.1 j).symm.trans (congrArg Y.vertex he)⟩
    have hAlen : A.length < T.length := by
      have hi : ¬ ib.val ≤ A.length := fun h => hvbA ((prefixPosition hAT ib).2 h)
      have := ib.isLt
      omega
    let Ty := TreeSequencePrefix T
      (min (A.length + (T.length - A.length - 1)) T.length)
      (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
    have hTy : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty) := by
      have hp := @hprefixElementary
      dsimp only at hp
      simp only [hstarC] at hp
      exact @hp
    have hTyT : TreeSequenceInitialSegment Ty T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have hATy : TreeSequenceInitialSegment A Ty := by
      refine ⟨?_, fun i => hAT.2.1 i, fun i => hAT.2.2 i⟩
      change A.length ≤ min (A.length + (T.length - A.length - 1)) T.length
      omega
    have hAElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
      intro u hu v hv huv
      exact hTy (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
        (TreeSequenceInitialSegmentVertexSetSubset hATy hv) huv
    have firstMissing (c : Fin k) (hc : c ∈ TreeMissingColors phi Ty) :
        c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ Ty.length ∧
        (∀ j : Fin (T.length + 1), c ∈ MissingColors G phi (T.vertex j) →
          (HierarchyFirstMissingPosition phi T c).val ≤ j.val) := by
      clear * - hc hTyT
      obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨i, _, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      let iT := Fin.castLE (Nat.succ_le_succ hTyT.1) i
      let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
        c ∈ MissingColors G phi (T.vertex j)
      have him : iT ∈ candidates := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hTyT.2.1 i, hi]; exact hvc⟩
      have hnonempty : candidates.Nonempty := ⟨iT, him⟩
      have hpos : HierarchyFirstMissingPosition phi T c = candidates.min' hnonempty := by
        simp only [HierarchyFirstMissingPosition, candidates, dif_pos hnonempty]
      rw [hpos]
      refine ⟨(Finset.mem_filter.mp (Finset.min'_mem candidates hnonempty)).2, ?_, ?_⟩
      · have hle := Finset.min'_le candidates iT him
        change (candidates.min' hnonempty).val ≤ i.val at hle
        have := i.isLt
        omega
      · intro j hj
        exact Finset.min'_le candidates j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    have hmissingTy : alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty := by
      simpa only [hstarC] using hmissingPrefix
    have ha := firstMissing alpha hmissingTy.1
    have hb := firstMissing beta hmissingTy.2
    have hvaTy : va ∈ TreeSequenceVertexSet Ty := (prefixPosition hTyT ia).2 ha.2.1
    have hvbTy : vb ∈ TreeSequenceVertexSet Ty := (prefixPosition hTyT ib).2 hb.2.1
    have hab : va ≠ vb := by intro he; exact hvbA (he ▸ hvaA)
    have hbetaA : beta ∉ TreeMissingColors phi A := by
      intro hm
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨i, _, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      have hle := hb.2.2 (Fin.castLE (Nat.succ_le_succ hAT.1) i)
        (by rw [hAT.2.1 i, hi]; exact hvm)
      apply hvbA
      apply (prefixPosition hAT ib).2
      have := i.isLt
      simp only [Fin.val_castLE] at hle
      omega
    have halphaA : alpha ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨va, hvaA, ha.1⟩
    have hnotclosed : ¬ TreeColorSetClosed G phi A {alpha} := by
      simpa only [hstarC] using hbranch.2.1
    have stableClosed (X : TreeSequence G e0) (D : Finset (Fin k))
        (psi pi : PartialEdgeColoring E k)
        (hpsi : IsProperEdgeColoring G psi) (hpsiOne : IsOneEdgeUncolored psi e0)
        (hpi : IsProperEdgeColoring G pi) (hpiOne : IsOneEdgeUncolored pi e0)
        (hs : StableColoring X D psi pi)
        (hc : ColoredVertexSetClosed G psi (TreeSequenceVertexSet X)) :
        ColoredVertexSetClosed G pi (TreeSequenceVertexSet X) := by
      clear * - hpsi hpsiOne hpi hpiOne hs hc
      have hr : StableColoring X D pi psi :=
        (sc2 G e0 X D).symm
          (x := ⟨psi, hpsi, hpsiOne⟩) (y := ⟨pi, hpi, hpiOne⟩) hs
      intro f c v hf hv hfc hvm
      have hboundary := hf
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hboundary
      obtain ⟨u, hu, w, hw, he⟩ := hboundary
      have hinc : TreeIncidentEdge X f := by
        refine ⟨u, hu, ?_⟩
        change u ∈ G.ends f
        rw [he]
        exact Sym2.mem_mk_left _ _
      have hm : c ∈ TreeMissingColors pi X := Finset.mem_biUnion.mpr ⟨v, hv, hvm⟩
      have hfixed := hr.1 f hinc ⟨c, Finset.mem_union_left _ hm, hfc⟩
      exact hc hf hv (hfixed.trans hfc) (by rw [hr.2 v hv]; exact hvm)
    have closedSingleton (hc : ColoredVertexSetClosed G phi (TreeSequenceVertexSet A)) :
        TreeColorSetClosed G phi A {alpha} := by
      clear * - hc hvaA ha
      intro c hcs
      have he : c = alpha := Finset.mem_singleton.mp hcs
      subst c
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hf, hfc⟩ := Finset.mem_filter.mp hf
      exact hc hf hvaA hfc ha.1
    have terminalPE : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
      clear * - hnotclosed closedSingleton stableClosed
      let p : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      have hp : p.succ = n := by
        apply Fin.ext
        change p.val + 1 = ett.rounds
        dsimp [p]
        have := ett.roundsPositive
        omega
      have hphi : phi = ett.series.data.coloring p.succ := by
        rw [hp]
        exact ett.generatingColoring
      generalize heq : p.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        exact (Fin.succ_ne_zero p heq).elim
      | PE ci pp po pc pn nr choice alt gamma gr second sp so sr ew
          cc cp cu cs ce ck cv co cd cg cl oe st =>
        have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
        subst ci
        rw [← hp]
        exact ck
      | RE ci pp po pc pn available cc cs ce ck cv co cd cg ad ae cl oe st =>
        have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
        subst ci
        have hnot : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
          rw [← hp, ck]
          simp
        have hcore : A = ett.series.data.tree p.succ.castSucc :=
          (base.nonparallel hnot).trans (by rw [hp])
        exact False.elim (hnotclosed (closedSingleton (by
          simp only [hcore, hphi, cc]
          exact @pc)))
      | SE ci pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
        have hci : ci = p := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
        subst ci
        have hnot : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
          rw [← hp, ck]
          simp
        have hcore : A = ett.series.data.tree p.succ.castSucc :=
          (base.nonparallel hnot).trans (by rw [hp])
        apply False.elim
        apply hnotclosed
        apply closedSingleton
        simp only [hcore, hphi, cc]
        exact stableClosed _ _ _ _ pp po choice.selectedProper
          choice.selectedOneUncolored choice.selectedStable pc
    obtain ⟨union⟩ := (base.parallel terminalPE).2.2
    have hTnA : TreeSequenceInitialSegment Tn A := union.leftSegment
    have hRA : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
      rw [union.vertexSet]
      exact Finset.subset_union_right
    have hidentity : CombinedStableColoring Tn base.closure Dn phi phi :=
      ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl⟩,
        ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩
    have hnotcommon : ¬ (va ∈ TreeSequenceVertexSet Tn ∧
        va ∈ TreeSequenceVertexSet base.closure) := by
      rintro ⟨hvT, hvR⟩
      exact hnotclosed (InterchangePECommonMissingClosed G k e0 input T phi phi
        ett C.maximum C.positive hlower terminalPE base hproper hone hidentity alpha
        (Finset.mem_biUnion.mpr ⟨va, hvT, ha.1⟩)
        (Finset.mem_biUnion.mpr ⟨va, hvR, ha.1⟩))
    have hsplit : (va ∈ TreeSequenceVertexSet Tn ∧ va ∉ TreeSequenceVertexSet base.closure) ∨
        (va ∈ TreeSequenceVertexSet base.closure ∧ va ∉ TreeSequenceVertexSet Tn) := by
      have hv : va ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
        rw [← union.vertexSet]
        exact hvaA
      rcases Finset.mem_union.mp hv with ht | hr
      · exact Or.inl ⟨ht, fun hr => hnotcommon ⟨ht, hr⟩⟩
      · exact Or.inr ⟨hr, fun ht => hnotcommon ⟨ht, hr⟩⟩
    have pathMissing (c d : Fin k) (hcd : c ≠ d) (v : V)
        (hvm : c ∈ MissingColors G phi v) :
        TwoColorPathComponent G phi c d (Sum.inl v) := by
      clear * - hproper hcd hvm
      refine ⟨hcd, Sum.inl v, ?_, ?_⟩
      · change (TwoColorIncidenceGraph G phi c d).connectedComponentMk (Sum.inl v) =
          (TwoColorIncidenceGraph G phi c d).connectedComponentMk (Sum.inl v)
        rfl
      · letI : Fintype ((TwoColorIncidenceGraph G phi c d).neighborSet (Sum.inl v)) :=
          Fintype.ofFinite _
        intro x hx y hy
        have hcard : Fintype.card ((TwoColorIncidenceGraph G phi c d).neighborSet
            (Sum.inl v)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact MissingColorIncidenceEndpoint G phi c d hcd hproper v hvm
        exact congrArg Subtype.val
          (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
    have hpathA : TwoColorPathComponent G phi alpha beta (Sum.inl va) :=
      pathMissing alpha beta hne va ha.1
    have hpathB : TwoColorPathComponent G phi alpha beta (Sum.inl vb) := by
      have hbpath := pathMissing beta alpha hne.symm vb hb.1
      have hgraph : TwoColorIncidenceGraph G phi beta alpha =
          TwoColorIncidenceGraph G phi alpha beta := by
        ext x y
        cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
      refine ⟨hne, ?_⟩
      have hp := hbpath.2
      change ∃ x ∈ ((TwoColorIncidenceGraph G phi beta alpha).connectedComponentMk
        (Sum.inl vb) : Set (Sum V E)),
        ((TwoColorIncidenceGraph G phi beta alpha).neighborSet x).Subsingleton at hp
      rw [hgraph] at hp
      exact hp
    change TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    by_contra hdistinct
    let root : Sum V E := Sum.inl vb
    let sigma := TwoColorComponentSwap G phi alpha beta root
    let component := TwoColorComponent G phi alpha beta root
    have hsProper : IsProperEdgeColoring G sigma :=
      TwoColorComponentSwapProper G phi alpha beta hne hproper root
    have hsOne : IsOneEdgeUncolored sigma e0 := by
      clear * - hone hne component
      constructor
      · simp [sigma, TwoColorComponentSwap, hone.1]
      · intro f hf
        obtain ⟨c, hc⟩ := hone.2 f hf
        by_cases hcomp : Sum.inr f ∈ component
        · by_cases hca : c = alpha
          · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, component, hcomp, hc, hca]⟩
          · by_cases hcb : c = beta
            · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, component, hcomp, hc, hca, hcb]⟩
            · exact ⟨c, by simp [sigma, TwoColorComponentSwap, component, hcomp, hc, hca, hcb]⟩
        · exact ⟨c, by simp [sigma, TwoColorComponentSwap, component, hcomp, hc]⟩
    have hbehavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper root
    have edgeVertex (f : E) (v : V) (hvf : Incident G v f)
        (hc : phi f = some alpha ∨ phi f = some beta)
        (hf : Sum.inr f ∈ component) : Sum.inl v ∈ component := by
      clear * - hvf hc hf component
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) (Sum.inr f)
          from ⟨hvf, hc⟩)).trans hf
    have vertexEdge (f : E) (v : V) (hvf : Incident G v f)
        (hc : phi f = some alpha ∨ phi f = some beta)
        (hv : Sum.inl v ∈ component) : Sum.inr f ∈ component := by
      clear * - hvf hc hv component
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v)
          from ⟨hvf, hc⟩)).trans hv
    have hgraph : TwoColorIncidenceGraph G sigma alpha beta =
        TwoColorIncidenceGraph G phi alpha beta := by
      clear * - hne component
      ext x y
      cases x with
      | inl v =>
        cases y with
        | inl w => rfl
        | inr f =>
          by_cases hm : Sum.inr f ∈ component <;>
            by_cases ha : phi f = some alpha <;> by_cases hb : phi f = some beta <;>
            simp [TwoColorIncidenceGraph, sigma, TwoColorComponentSwap, component,
              hm, ha, hb, hne, hne.symm]
      | inr f =>
        cases y with
        | inr g => rfl
        | inl v =>
          by_cases hm : Sum.inr f ∈ component <;>
            by_cases ha : phi f = some alpha <;> by_cases hb : phi f = some beta <;>
            simp [TwoColorIncidenceGraph, sigma, TwoColorComponentSwap, component,
              hm, ha, hb, hne, hne.symm]
    have hcomponents (z : Sum V E) : TwoColorComponent G sigma alpha beta z =
        TwoColorComponent G phi alpha beta z := by
      exact congrArg (fun g : SimpleGraph (Sum V E) =>
        (g.connectedComponentMk z : Set (Sum V E))) hgraph
    have hinvolution : TwoColorComponentSwap G sigma alpha beta root = phi := by
      clear * - hne hcomponents component
      funext f
      unfold TwoColorComponentSwap
      rw [hcomponents]
      change (if Sum.inr f ∈ component then
        if sigma f = some alpha then some beta else if sigma f = some beta then some alpha
        else sigma f else sigma f) = phi f
      by_cases hm : Sum.inr f ∈ component <;>
        by_cases ha : phi f = some alpha <;> by_cases hb : phi f = some beta <;>
        simp [sigma, TwoColorComponentSwap, component, hm, ha, hb, hne, hne.symm]
    have hreverse := TwoColorComponentSwapMissingBehavior G sigma alpha beta hne hsProper root
    rw [hinvolution] at hreverse
    have hmissingSwap (v : V) (hv : Sum.inl v ∈ component) :
        (alpha ∈ MissingColors G sigma v ↔ beta ∈ MissingColors G phi v) ∧
        (beta ∈ MissingColors G sigma v ↔ alpha ∈ MissingColors G phi v) := by
      have hvs : Sum.inl v ∈ TwoColorComponent G sigma alpha beta root := by
        rw [hcomponents]
        exact hv
      exact ⟨⟨hreverse.2.1 v hvs, hbehavior.2.2.1 v hv⟩,
        ⟨hreverse.2.2.1 v hvs, hbehavior.2.1 v hv⟩⟩
    have hself : Sum.inl vb ∈ component := by
      change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl vb) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl vb)
      rfl
    have hvaOutside : Sum.inl va ∉ component := by
      intro hv
      have he : TwoColorComponent G phi alpha beta (Sum.inl va) = component :=
        congrArg SimpleGraph.ConnectedComponent.supp hv
      exact hdistinct he
    have haSigma : alpha ∈ MissingColors G sigma va := by
      rw [hbehavior.1 va hvaOutside]
      exact ha.1
    have hbSigma : alpha ∈ MissingColors G sigma vb := hbehavior.2.2.1 vb hself hb.1
    have noMissing (X : TreeSequence G e0)
        (hXA : TreeSequenceVertexSet X ⊆ TreeSequenceVertexSet A)
        (hva : va ∉ TreeSequenceVertexSet X) :
        alpha ∉ TreeMissingColors phi X ∧ beta ∉ TreeMissingColors phi X := by
      constructor
      · intro hm
        obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
        exact Finset.disjoint_left.mp (hAElementary hvaA (hXA hv)
          (by intro he; exact hva (he ▸ hv))) ha.1 hvm
      · intro hm
        obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
        exact hbetaA (Finset.mem_biUnion.mpr ⟨v, hXA hv, hvm⟩)
    have stableNoMissing (X : TreeSequence G e0) (D : Finset (Fin k))
        (hna : alpha ∉ TreeMissingColors phi X)
        (hnb : beta ∉ TreeMissingColors phi X)
        (hda : alpha ∉ D) (hdb : beta ∉ D) : StableColoring X D phi sigma := by
      clear * - hna hnb hda hdb hbehavior hmissingSwap
      constructor
      · intro f hf hc
        obtain ⟨c, hc, hfc⟩ := hc
        have hca : c ≠ alpha := by
          intro he; subst c; exact (Finset.notMem_union.mpr ⟨hna, hda⟩) hc
        have hcb : c ≠ beta := by
          intro he; subst c; exact (Finset.notMem_union.mpr ⟨hnb, hdb⟩) hc
        simp [sigma, TwoColorComponentSwap, hfc, hca, hcb]
      · intro v hv
        by_cases hvc : Sum.inl v ∈ component
        · apply Finset.ext
          intro c
          by_cases hca : c = alpha
          · subst c
            have hva : alpha ∉ MissingColors G phi v := fun hm =>
              hna (Finset.mem_biUnion.mpr ⟨v, hv, hm⟩)
            have hvb : beta ∉ MissingColors G phi v := fun hm =>
              hnb (Finset.mem_biUnion.mpr ⟨v, hv, hm⟩)
            simp only [hmissingSwap v hvc, hva, hvb]
          · by_cases hcb : c = beta
            · subst c
              have hva : alpha ∉ MissingColors G phi v := fun hm =>
                hna (Finset.mem_biUnion.mpr ⟨v, hv, hm⟩)
              have hvb : beta ∉ MissingColors G phi v := fun hm =>
                hnb (Finset.mem_biUnion.mpr ⟨v, hv, hm⟩)
              simp only [hmissingSwap v hvc, hva, hvb]
            · exact hbehavior.2.2.2 v c hca hcb
        · exact hbehavior.1 v hvc
    have stableOutside (X : TreeSequence G e0) (D : Finset (Fin k))
        (hout : ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ component) :
        StableColoring X D phi sigma := by
      clear * - hout hbehavior edgeVertex
      constructor
      · intro f hf hc
        obtain ⟨v, hv, hvf⟩ := hf
        by_cases hm : Sum.inr f ∈ component
        · have hfa : phi f ≠ some alpha := fun he => hout v hv (edgeVertex f v hvf (Or.inl he) hm)
          have hfb : phi f ≠ some beta := fun he => hout v hv (edgeVertex f v hvf (Or.inr he) hm)
          simp [sigma, TwoColorComponentSwap, component, hm, hfa, hfb]
        · simp [sigma, TwoColorComponentSwap, component, hm]
      · intro v hv
        exact hbehavior.1 v (hout v hv)
    have outsideFromInterchange (X : TreeSequence G e0)
        (hva : va ∈ TreeSequenceVertexSet X)
        (hinter : TreeInterchangeable G X phi alpha beta) :
        ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ component := by
      intro v hv hvc
      exact hdistinct (hinter (Sum.inl va) root hpathA hpathB
        ⟨va, hva, by change _ = _; rfl⟩ ⟨v, hv, hvc⟩)
    have hcombined : CombinedStableColoring Tn base.closure Dn phi sigma := by
      rcases hsplit with ⟨hvaT, hvaR⟩ | ⟨hvaR, hvaT⟩
      · have hn := noMissing base.closure hRA hvaR
        have hi := (interchange G k e0 input T phi phi ett C.maximum C.positive hlower
          terminalPE base hproper hone hidentity alpha beta).2.1
          (Finset.mem_biUnion.mpr ⟨va, hvaT, ha.1⟩)
        exact ⟨stableOutside Tn Dn (outsideFromInterchange Tn hvaT hi),
          stableNoMissing base.closure ∅ hn.1 hn.2 (by simp) (by simp)⟩
      · have hn := noMissing Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA) hvaT
        have hd : Disjoint ({alpha, beta} : Finset (Fin k)) Dn :=
          hbranch.2.2.resolve_left hn.1
        have hi := (interchange G k e0 input T phi phi ett C.maximum C.positive hlower
          terminalPE base hproper hone hidentity alpha beta).1
          (Finset.mem_biUnion.mpr ⟨va, hvaR, ha.1⟩)
        exact ⟨stableNoMissing Tn Dn hn.1 hn.2
            (fun hm => Finset.disjoint_left.mp hd (by simp) hm)
            (fun hm => Finset.disjoint_left.mp hd (by simp) hm),
          stableOutside base.closure ∅ (outsideFromInterchange base.closure hvaR hi)⟩
    have segmentTrans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y) (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      clear * - hXY hYZ
      exact ⟨le_trans hXY.1 hYZ.1,
        fun i => (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i),
        fun i => (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)⟩
    have commonPrefix {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z) (hYZ : TreeSequenceInitialSegment Y Z)
        (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
      clear * - hXZ hYZ hXY
      refine ⟨hXY, ?_, ?_⟩
      · intro i
        exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
      · intro i
        exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
    have hAib : A.length < ib.val := by
      have hi := (prefixPosition hAT ib).not.mp hvbA
      omega
    let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
      (Nat.le_of_lt_succ ib.isLt)
    have hBT : TreeSequenceInitialSegment B T :=
      ⟨Nat.le_of_lt_succ ib.isLt, fun _ => rfl, fun _ => rfl⟩
    have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT hBT (by exact Nat.le_of_lt hAib)
    have hTnB : TreeSequenceInitialSegment Tn B := segmentTrans hTnA hAB
    have hBstrict : B.length < T.length := by
      change ib.val < T.length
      have := hb.2.1
      change ib.val ≤ min (A.length + (T.length - A.length - 1)) T.length at this
      omega
    have hroute : TashkinovAugmentationSequence phi Tn
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      clear * - terminalPE
      have cert := ett.series.certified n
      generalize hn : n = target at cert
      cases cert with
      | initial triple sl cc cs ce ck cv co cd cg cl =>
        rw [hn, ck] at terminalPE
        cases terminalPE
      | SE i pp po pc pn nr ch alt cc cs ce ck cv co cd cg ad ae cl oe st =>
        rw [hn, ck] at terminalPE
        cases terminalPE
      | RE i pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
        rw [hn, ck] at terminalPE
        cases terminalPE
      | PE i pp po pc pn nr ch alt gamma gr second sp so sr ew
          cc cp cu cs ce ck cv co cd cg cl oe st =>
        have hfinal : i.succ.succ = Fin.last (ett.rounds + 1) := by
          apply Fin.ext
          have hv := congrArg Fin.val hn
          change ett.rounds = i.val + 1 at hv
          simp only [Fin.val_succ, Fin.val_last]
          omega
        have hphi : phi = ett.series.data.coloring i.succ := ett.generatingColoring.trans
          (congrArg ett.series.data.coloring hn)
        simpa only [Tn, hn, hfinal, ← hphi] using cl.1
    have hrouteB : TashkinovAugmentationSequence phi Tn B :=
      TashkinovAugmentationSequenceRestrict phi Tn B _ hroute hTnB
        (segmentTrans hBT ett.belowFinal)
    have hpreserved := CombinedStableClosurePreserved G k e0 input T phi phi sigma ett
      C.positive base ett.generatingColoring terminalPE hproper hone hsProper hsOne hcombined
    have hfixedA (t : Fin A.length) : sigma (A.edge t) = phi (A.edge t) := by
      by_cases ht : t.val < Tn.length
      · let s : Fin Tn.length := ⟨t.val, ht⟩
        have hi : Fin.castLE hTnA.1 s = t := Fin.ext rfl
        have he : A.edge t = Tn.edge s := by simpa only [hi] using hTnA.2.2 s
        rw [he]
        exact hpreserved.1 s
      · obtain ⟨s, he, hv⟩ := union.newEntryFromRight t (Nat.le_of_not_gt ht)
        rw [he]
        exact hpreserved.2.1 s
    have hmissingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
        MissingColors G sigma v = MissingColors G phi v := by
      rw [union.vertexSet] at hv
      rcases Finset.mem_union.mp hv with ht | hr
      · exact hcombined.1.2 v ht
      · exact hcombined.2.2 v hr
    have hmissingTreeA : TreeMissingColors sigma A = TreeMissingColors phi A := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => hmissingA v hv)
    have hmissingTreeTn : TreeMissingColors sigma Tn = TreeMissingColors phi Tn := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => hcombined.1.2 v hv)
    have hmissingTreeR : TreeMissingColors sigma base.closure = TreeMissingColors phi base.closure := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => hcombined.2.2 v hv)
    have hunused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < ib.val →
        phi (T.edge t) ≠ some alpha := by
      have ho := horderedUnused (by simpa only [hstarC] using Or.inr hbetaA)
      intro t hlo hhi hc
      apply ho.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, by simpa only [hstarC] using hlo, hhi, hc⟩
    have transport : ∀ {X : TreeSequence G e0}, TashkinovAugmentationSequence phi Tn X →
        TreeSequenceInitialSegment X B →
        TashkinovAugmentationSequence sigma Tn X ∧
        ∀ t : Fin X.length, sigma (X.edge t) = phi (X.edge t) := by
      intro X hs
      induction hs with
      | refl => intro _; exact ⟨Relation.ReflTransGen.refl, hpreserved.1⟩
      | @tail Y Z hTY hYZ ih =>
        intro hZB
        obtain ⟨hlen, hseg, c, hcolor, hmiss⟩ := hYZ
        have hYB := segmentTrans hseg hZB
        obtain ⟨hTYs, hfixedY⟩ := ih hYB
        let t : Fin Z.length := Fin.cast hlen.symm (Fin.last Y.length)
        have ht : t.val = Y.length := by simp [t]
        have hfixedLast : sigma (Z.edge t) = phi (Z.edge t) ∧
            c ∈ TreeMissingColors sigma Y := by
          by_cases hyA : Y.length < A.length
          · let a : Fin A.length := ⟨Y.length, hyA⟩
            have he : Z.edge t = A.edge a := by
              have heZ := hZB.2.2 t
              have heA := hAB.2.2 a
              have hi : Fin.castLE hZB.1 t = Fin.castLE hAB.1 a := Fin.ext (by simp [t, a])
              exact heZ.symm.trans ((congrArg B.edge hi).trans heA)
            refine ⟨by rw [he]; exact hfixedA a, ?_⟩
            obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hmiss
            have hvA := TreeSequenceInitialSegmentVertexSetSubset
              (commonPrefix hYB hAB (Nat.le_of_lt hyA)) hv
            exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [hmissingA v hvA]; exact hvm⟩
          · have hZT := segmentTrans hZB hBT
            have hca : c ≠ alpha := by
              intro he
              let tT := Fin.castLE hZT.1 t
              apply hunused tT (by simp [tT, ht]; omega) (by
                have := t.isLt
                have := hZB.1
                change Z.length ≤ ib.val at this
                simp only [tT, Fin.val_castLE]
                omega)
              rw [hZT.2.2 t]
              simpa only [he] using hcolor
            have hcb : c ≠ beta := by
              intro he
              obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hmiss
              obtain ⟨j, _, hj⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
              have hYT := segmentTrans hYB hBT
              have hle := hb.2.2 (Fin.castLE (Nat.succ_le_succ hYT.1) j)
                (by rw [hYT.2.1 j, hj]; simpa only [he] using hvm)
              have := j.isLt
              have := t.isLt
              have := hZB.1
              change Z.length ≤ ib.val at this
              simp only [Fin.val_castLE] at hle
              omega
            refine ⟨?_, ?_⟩
            · have hc : phi (Z.edge t) = some c := hcolor
              by_cases hm : Sum.inr (Z.edge t) ∈ component <;>
                simp [sigma, TwoColorComponentSwap, component, hm, hc, hca, hcb]
            · obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hmiss
              exact Finset.mem_biUnion.mpr ⟨v, hv, (hbehavior.2.2.2 v c hca hcb).2 hvm⟩
        refine ⟨Relation.ReflTransGen.tail hTYs
          ⟨hlen, hseg, c, hfixedLast.1.trans hcolor, hfixedLast.2⟩, ?_⟩
        intro s
        by_cases hsY : s.val < Y.length
        · let y : Fin Y.length := ⟨s.val, hsY⟩
          have hi : Fin.castLE hseg.1 y = s := Fin.ext rfl
          have he : Z.edge s = Y.edge y := by simpa only [hi] using hseg.2.2 y
          rw [he]
          exact hfixedY y
        · have hi : s = t := Fin.ext (by have := s.isLt; simp only [ht]; omega)
          rw [hi]
          exact hfixedLast.1
    obtain ⟨hrouteSigma, hfixedB⟩ := transport hrouteB ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    obtain ⟨ettB, hMPB, hrB, hseriesB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hpositionsB, goodB, hgoodDataB⟩ :=
      GoodHierarchyTerminalPrefixRepackage G k e0 input T phi phi ett C.maximum base H C.good
        B (by simpa only [hstar] using hAB)
        (by simpa only [hstar] using (show A.length < B.length from hAib)) hBT
    have hBdata : ettB.series.data.tree (Fin.last ettB.rounds).castSucc = Tn ∧
        TashkinovStoredColors ettB.series.data (Fin.last ettB.rounds) = Dn ∧
        ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.PE := by
      cases ettB with
      | mk r rp series above strict below generating =>
        dsimp only at hrB hseriesB ⊢
        cases hrB
        have he : series = ett.series := eq_of_heq hseriesB
        cases he
        exact ⟨rfl, rfl, terminalPE⟩
    have hcombinedB : CombinedStableColoring
        (ettB.series.data.tree (Fin.last ettB.rounds).castSucc) baseB.closure
        (TashkinovStoredColors ettB.series.data (Fin.last ettB.rounds)) phi sigma := by
      rw [hBdata.1, hBdata.2.1, hclosureB]
      exact hcombined
    obtain ⟨corr, hMPnew, baseSigma, K, hsame⟩ := HierarchySplitter G k e0 input B phi sigma
      ettB hMPB ettB.roundsPositive
      (fun lower hp hb hm => hlower lower hp (by rwa [hrB] at hb) hm)
      baseB HB hBdata.2.2 hproper hone hsProper hsOne hcombinedB
      (by rw [hBdata.1]; exact hrouteSigma)
    have hnewdata : corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
        TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) = Dn ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          some TashkinovExtensionKind.PE := by
      clear * - hBdata
      rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
        rungAgreement, seriesPresentation, finalGeneratingColoring,
        ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
        extensionKindsAgree, replacementProper, replacementOneUncolored, replacementStable⟩
      cases replacementETT with
      | mk r rp series above strict below generating =>
        cases rungAgreement
        have he : series = replacementSeries := eq_of_heq seriesPresentation
        cases he
        let p : Fin ettB.rounds := ⟨ettB.rounds - 1, by have := ettB.roundsPositive; omega⟩
        have hp : p.succ = Fin.last ettB.rounds := by
          apply Fin.ext
          change p.val + 1 = ettB.rounds
          dsimp [p]
          have := ettB.roundsPositive
          omega
        have htree : replacementSeries.data.tree (Fin.last ettB.rounds).castSucc =
            ettB.series.data.tree (Fin.last ettB.rounds).castSucc := by
          rw [← hp]
          exact ladderTreesAgree p
        have hstable : StableColoring
            (ettB.series.data.tree (Fin.last ettB.rounds).castSucc)
            (TashkinovStoredColors ettB.series.data (Fin.last ettB.rounds))
            (ettB.series.data.coloring (Fin.last ettB.rounds))
            (replacementSeries.data.coloring (Fin.last ettB.rounds)) := by
          simpa only [hp] using replacementStable p
        have hmissing : TreeMissingColors (replacementSeries.data.coloring (Fin.last ettB.rounds))
            (replacementSeries.data.tree (Fin.last ettB.rounds).castSucc) =
            TreeMissingColors (ettB.series.data.coloring (Fin.last ettB.rounds))
              (ettB.series.data.tree (Fin.last ettB.rounds).castSucc) := by
          rw [htree]
          unfold TreeMissingColors
          exact Finset.biUnion_congr rfl (fun v hv => hstable.2 v hv)
        have hstored : TashkinovStoredColors replacementSeries.data (Fin.last ettB.rounds) =
            TashkinovStoredColors ettB.series.data (Fin.last ettB.rounds) := by
          unfold TashkinovStoredColors
          have hn : (Fin.last ettB.rounds).val ≠ 0 := by
            simpa only [Fin.val_last] using Nat.ne_of_gt ettB.roundsPositive
          simp only [if_neg hn]
          rw [hmissing]
          congr 1
          apply Finset.biUnion_congr rfl
          intro i hi
          rw [storedColorsAgree i]
        exact ⟨htree.trans hBdata.1, hstored.trans hBdata.2.1,
          (extensionKindsAgree (Fin.last ettB.rounds)).trans hBdata.2.2⟩
    have hcountHB : HB.dividerCount = 0 := hcountB.trans hzero
    have hcountK : K.dividerCount = 0 := hsame.2.1.symm.trans hcountHB
    have hcoreNew : baseSigma.core = A := hsame.1.symm.trans hcoreB
    have hclosureNew : baseSigma.closure = base.closure :=
      (hsame.2.2.2.2.2 hBdata.2.2).symm.trans hclosureB
    have hstoredEq : HierarchyStoredColorsAt K 0 = HierarchyStoredColorsAt HB 0 := by
      change TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) \ TreeMissingColors sigma baseSigma.core =
        TashkinovStoredColors ettB.series.data (Fin.last ettB.rounds) \
          TreeMissingColors phi baseB.core
      rw [hnewdata.2.1, hBdata.2.1, hcoreNew, hcoreB, hmissingTreeA]
    have hstageMissingEq : HierarchyStageMissingColors K 0 =
        HierarchyStageMissingColors HB 0 := by
      change TreeMissingColors sigma
          (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) =
        TreeMissingColors phi (ettB.series.data.tree (Fin.last ettB.rounds).castSucc)
      rw [hnewdata.1, hBdata.1, hmissingTreeTn]
    have halphaNotStored : alpha ∉ HierarchyStoredColorsAt K 0 := by
      intro hm
      exact (Finset.mem_sdiff.mp hm).2 (by
        change alpha ∈ TreeMissingColors sigma baseSigma.core
        rw [hcoreNew, hmissingTreeA]
        exact halphaA)
    have hBTy : TreeSequenceInitialSegment B Ty := commonPrefix hBT hTyT hb.2.1
    have hbetaNone : beta ∉ TreeMissingColors sigma B := by
      intro hm
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
      have hvTy := TreeSequenceInitialSegmentVertexSetSubset hBTy hv
      by_cases hvc : Sum.inl v ∈ component
      · have hma : alpha ∈ MissingColors G phi v := (hmissingSwap v hvc).2.1 hvm
        have hneVA : va ≠ v := by intro he; exact hvaOutside (he ▸ hvc)
        exact Finset.disjoint_left.mp (hTy hvaTy hvTy hneVA) ha.1 hma
      · have hmb : beta ∈ MissingColors G phi v := by rw [← hbehavior.1 v hvc]; exact hvm
        have hneVB : vb ≠ v := by intro he; exact hvc (he ▸ hself)
        exact Finset.disjoint_left.mp (hTy hvbTy hvTy hneVB) hb.1 hmb
    have hfirstEq (eta : Fin k) (hena : eta ≠ alpha) :
        (HierarchyFirstMissingPosition sigma B eta).val =
          (HierarchyFirstMissingPosition phi B eta).val := by
      clear * - hbetaNone hBT hbehavior hena
      by_cases heb : eta = beta
      · subst eta
        have hempty : ¬ (Finset.univ.filter fun i : Fin (B.length + 1) =>
            beta ∈ MissingColors G sigma (B.vertex i)).Nonempty := by
          rintro ⟨i, hi⟩
          apply hbetaNone
          exact Finset.mem_biUnion.mpr ⟨B.vertex i,
            (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩,
            (Finset.mem_filter.mp hi).2⟩
        have hnew : (HierarchyFirstMissingPosition sigma B beta).val = B.length := by
          simp only [HierarchyFirstMissingPosition, dif_neg hempty, Fin.val_last]
        have hcut := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT beta B.length le_rfl
        have hold : (HierarchyFirstMissingPosition phi B beta).val = B.length := by
          have hi := (HierarchyFirstMissingPosition phi B beta).isLt
          change min (HierarchyFirstMissingPosition phi B beta).val B.length =
            min ib.val B.length at hcut
          change min (HierarchyFirstMissingPosition phi B beta).val ib.val =
            min ib.val ib.val at hcut
          change (HierarchyFirstMissingPosition phi B beta).val < ib.val + 1 at hi
          change (HierarchyFirstMissingPosition phi B beta).val = ib.val
          omega
        exact hnew.trans hold.symm
      · have hcandidates : (Finset.univ.filter fun i : Fin (B.length + 1) =>
            eta ∈ MissingColors G sigma (B.vertex i)) =
            (Finset.univ.filter fun i : Fin (B.length + 1) =>
              eta ∈ MissingColors G phi (B.vertex i)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hbehavior.2.2.2 (B.vertex i) eta hena heb
        unfold HierarchyFirstMissingPosition
        rw [hcandidates]
    have hnextHB : HB.stage (0 : Fin (HB.dividerCount + 1)).succ = B := by
      clear * - hcountHB
      have hi : (0 : Fin (HB.dividerCount + 1)).succ = Fin.last (HB.dividerCount + 1) := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, hcountHB]
      rw [hi, HB.terminalStage]
    have hnextK : K.stage (0 : Fin (K.dividerCount + 1)).succ = B := by
      clear * - hcountK
      have hi : (0 : Fin (K.dividerCount + 1)).succ = Fin.last (K.dividerCount + 1) := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, hcountK]
      rw [hi, K.terminalStage]
    set_option maxHeartbeats 4000000 in
    have hsegmentSubset (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt K 0) :
        HierarchySegmentColors K 0 eta ⊆ HierarchySegmentColors HB 0 eta := by
      clear * - halphaNotStored hnextK hnextHB hcoreNew hcoreB hfirstEq hfixedB heta
      have hena : eta ≠ alpha := by intro he; exact halphaNotStored (he ▸ heta)
      let colors (psi : PartialEdgeColoring E k) (a : ℕ) (W : TreeSequence G e0) :=
        Finset.univ.filter fun c => ∃ t : Fin W.length,
          a ≤ t.val ∧ t.val < min (HierarchyFirstMissingPosition psi B eta).val W.length ∧
          psi (W.edge t) = some c
      have hsegK : HierarchySegmentColors K 0 eta = colors sigma baseSigma.core.length B := by
        change colors sigma baseSigma.core.length (K.stage (0 : Fin (K.dividerCount + 1)).succ) = _
        exact congrArg (colors sigma baseSigma.core.length) hnextK
      have hsegHB : HierarchySegmentColors HB 0 eta = colors phi baseB.core.length B := by
        change colors phi baseB.core.length (HB.stage (0 : Fin (HB.dividerCount + 1)).succ) = _
        exact congrArg (colors phi baseB.core.length) hnextHB
      rw [hsegK, hsegHB]
      dsimp only [colors]
      rw [hcoreNew, hcoreB, hfirstEq eta hena]
      intro c hc
      obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi,
        (hfixedB t).symm.trans hcol⟩
    let reserved := (HierarchyStoredColorsAt HB 0).biUnion (goodB.gamma 0)
    set_option maxHeartbeats 4000000 in
    have hnotMinus : ¬ TreeColorSetMinusClosed G sigma A reserved := by
      intro hclosed
      apply (goodB.parallelBase hBdata.2.2).1
      change TreeColorSetClosed G phi baseB.core (TreeMissingColors phi baseB.core \ reserved)
      rw [hcoreB]
      intro c hc
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hboundary, hcolor⟩ := Finset.mem_filter.mp hf
      have hcs : c ∈ TreeMissingColors sigma A \ reserved := by
        rw [hmissingTreeA]
        exact hc
      have hfixed : sigma f ≠ phi f := by
        intro he
        exact Finset.notMem_empty f (by
          rw [← hclosed c hcs]
          exact Finset.mem_filter.mpr ⟨hboundary, he.trans hcolor⟩)
      have hecomp : Sum.inr f ∈ component := by
        by_contra hn
        exact hfixed (by simp [sigma, TwoColorComponentSwap, component, hn])
      have hcpair : c = alpha ∨ c = beta := by
        by_contra hn
        have hca : c ≠ alpha := fun he => hn (Or.inl he)
        have hcb : c ≠ beta := fun he => hn (Or.inr he)
        exact hfixed (by simp [sigma, TwoColorComponentSwap, component, hecomp, hcolor, hca, hcb])
      have hca : c = alpha := hcpair.resolve_right (by
        intro he
        exact hbetaA (he ▸ (Finset.mem_sdiff.mp hc).1))
      subst c
      have hAlphaClosed : TreeColorSetClosed G sigma A {alpha} := by
        intro c hc'
        have he : c = alpha := Finset.mem_singleton.mp hc'
        subst c
        exact hclosed alpha hcs
      have hAlphaSigmaA : alpha ∈ TreeMissingColors sigma A := by
        rw [hmissingTreeA]
        exact halphaA
      have hInter := (interchange G k e0 input T phi sigma ett C.maximum C.positive hlower
        terminalPE base hsProper hsOne hcombined alpha beta).2.2.1 hAlphaSigmaA hAlphaClosed
      have pathTransport (z : Sum V E) (hp : TwoColorPathComponent G phi alpha beta z) :
          TwoColorPathComponent G sigma alpha beta z := by
        obtain ⟨hne', x, hx, hleaf⟩ := hp
        refine ⟨hne', x, ?_, ?_⟩
        · rw [hcomponents]
          exact hx
        · exact (congrArg (fun g : SimpleGraph (Sum V E) =>
            Set.Subsingleton (g.neighborSet x)) hgraph).mpr hleaf
      have hbnd := hboundary
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hbnd
      obtain ⟨u, hu, w, hw, he⟩ := hbnd
      have huf : Incident G u f := by change u ∈ G.ends f; rw [he]; exact Sym2.mem_mk_left _ _
      have hucomp := edgeVertex f u huf (Or.inl hcolor) hecomp
      have heq := hInter (Sum.inl va) root (pathTransport _ hpathA) (pathTransport _ hpathB)
        ⟨va, hvaA, by rw [hcomponents]; change _ = _; rfl⟩
        ⟨u, hu, by rw [hcomponents]; exact hucomp⟩
      rw [hcomponents, hcomponents] at heq
      exact hdistinct heq
    let goodK : GoodHierarchy K :=
      { gamma := fun _ eta => goodB.gamma 0 eta
        twoColors := by
          intro j eta heta
          have hj : j = 0 := Fin.ext (by have := j.isLt; change j.val = 0; omega)
          subst j
          exact goodB.twoColors 0 eta (hstoredEq ▸ heta)
        avoidance := by
          intro j eta heta c hc
          have hj : j = 0 := Fin.ext (by have := j.isLt; change j.val = 0; omega)
          subst j
          have hold := goodB.avoidance 0 eta (hstoredEq ▸ heta) hc
          exact Finset.mem_sdiff.mpr ⟨hstageMissingEq.symm ▸ (Finset.mem_sdiff.mp hold).1,
            fun hseg => (Finset.mem_sdiff.mp hold).2 (hsegmentSubset eta heta hseg)⟩
        disjointPairs := by
          intro j eta theta heta htheta hne'
          have hj : j = 0 := Fin.ext (by have := j.isLt; change j.val = 0; omega)
          subst j
          exact goodB.disjointPairs 0 eta theta (hstoredEq ▸ heta) (hstoredEq ▸ htheta) hne'
        uniqueRefresh := by intro i; have := i.isLt; omega
        parallelBase := by
          dsimp
          intro hpe
          have hreserved : (HierarchyStoredColorsAt K 0).biUnion
              (fun eta => goodB.gamma 0 eta) = reserved := by rw [hstoredEq]
          rw [hcoreNew, hclosureNew, hnewdata.1, hreserved,
            hmissingTreeTn, hmissingTreeR]
          refine ⟨hnotMinus, ?_⟩
          have hold := (goodB.parallelBase hBdata.2.2).2
          simpa only [hBdata.1, hclosureB] using hold
        minusClosed := by intro i; have := i.isLt; omega }
    have hvaB : va ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hAB hvaA
    have hvbB : vb ∈ TreeSequenceVertexSet B := (prefixPosition hBT ib).2 le_rfl
    have hnotElementaryB : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) := by
      intro he
      exact Finset.disjoint_left.mp (he hvaB hvbB hab) haSigma hbSigma
    let Cnew : HierarchyCounterexample baseSigma :=
      { positive := corr.replacementETT.roundsPositive
        hierarchy := K
        good := goodK
        maximum := hMPnew
        notElementary := hnotElementaryB }
    have hstarK : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
      have hi : Fin.last K.dividerCount = (0 : Fin (K.dividerCount + 1)) := Fin.ext hcountK
      rw [hi]
      exact hcoreNew
    have pathLE : HierarchyPathNumber K ≤ HierarchyPathNumber H := by
      clear * - hstarK hstar hBT hAB hAlen hAib
      let ell := T.length - A.length
      let ellB := B.length - A.length
      let oldCandidates := (Finset.Icc 1 ell).filter fun i =>
        ∀ t : Fin T.length, A.length + i ≤ t.val →
          G.ends (T.edge t) = Sym2.mk (T.vertex t.castSucc) (T.vertex t.succ)
      let newCandidates := (Finset.Icc 1 ellB).filter fun i =>
        ∀ t : Fin B.length, A.length + i ≤ t.val →
          G.ends (B.edge t) = Sym2.mk (B.vertex t.castSucc) (B.vertex t.succ)
      have hell : 1 ≤ ell := by dsimp [ell]; omega
      have hellB : 1 ≤ ellB := by
        change 1 ≤ ib.val - A.length
        omega
      have holdMem : ell ∈ oldCandidates := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hell, le_rfl⟩, ?_⟩
        intro t ht
        have := t.isLt
        dsimp [ell] at ht
        omega
      have hnewMem : ellB ∈ newCandidates := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hellB, le_rfl⟩, ?_⟩
        intro t ht
        have := t.isLt
        have := hAB.1
        dsimp [ellB] at ht
        omega
      have holdNonempty : oldCandidates.Nonempty := ⟨ell, holdMem⟩
      have hnewNonempty : newCandidates.Nonempty := ⟨ellB, hnewMem⟩
      have hpathOld : HierarchyPathNumber H = oldCandidates.min' holdNonempty := by
        unfold HierarchyPathNumber
        simp only [hstar]
        exact dif_pos holdNonempty
      have hpathNew : HierarchyPathNumber K = newCandidates.min' hnewNonempty := by
        unfold HierarchyPathNumber
        simp only [hstarK]
        exact dif_pos hnewNonempty
      rw [hpathOld, hpathNew]
      by_cases hr : oldCandidates.min' holdNonempty ≤ ellB
      · have hmin := Finset.mem_filter.mp (Finset.min'_mem oldCandidates holdNonempty)
        have hcandidate : oldCandidates.min' holdNonempty ∈ newCandidates := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hmin.1).1, hr⟩, ?_⟩
          intro t ht
          let tT := Fin.castLE hBT.1 t
          have he := hmin.2 tT (by exact ht)
          have hv₁ := hBT.2.1 t.castSucc
          have hv₂ := hBT.2.1 t.succ
          have hi₁ : Fin.castLE (Nat.succ_le_succ hBT.1) t.castSucc = tT.castSucc := Fin.ext rfl
          have hi₂ : Fin.castLE (Nat.succ_le_succ hBT.1) t.succ = tT.succ := Fin.ext rfl
          rw [hi₁] at hv₁
          rw [hi₂] at hv₂
          rw [hBT.2.2 t, hv₁, hv₂] at he
          exact he
        exact Finset.min'_le newCandidates _ hcandidate
      · exact le_trans (Finset.min'_le newCandidates ellB hnewMem) (Nat.le_of_lt (Nat.lt_of_not_ge hr))
    have hstageOld : (H.stage ⟨H.dividerCount, by omega⟩).length = Tn.length := by
      have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) = 0 := Fin.ext hzero
      rw [hi, H.baseStage]
    have hstageNew : (K.stage ⟨K.dividerCount, by omega⟩).length = Tn.length := by
      have hi : (⟨K.dividerCount, by omega⟩ : Fin (K.dividerCount + 2)) = 0 := Fin.ext hcountK
      rw [hi, K.baseStage, hnewdata.1]
    have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure Cnew)
        (HierarchyCounterexampleMeasure C) := by
      change HierarchyPathNumber K < HierarchyPathNumber H ∨
        (HierarchyPathNumber K = HierarchyPathNumber H ∧
          B.length - (K.stage ⟨K.dividerCount, by omega⟩).length <
            T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
      by_cases hlt : HierarchyPathNumber K < HierarchyPathNumber H
      · exact Or.inl hlt
      · refine Or.inr ⟨Nat.le_antisymm pathLE (Nat.le_of_not_gt hlt), ?_⟩
        rw [hstageNew, hstageOld]
        have := hTnB.1
        omega
    exact hminimal Cnew (corr.rungAgreement.trans hrB) (hcountK.trans hzero.symm) hless
