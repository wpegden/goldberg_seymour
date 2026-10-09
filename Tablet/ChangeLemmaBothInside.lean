import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyNewMissingClosed
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyLEMStable
import Tablet.HierarchyPathNumber
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
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
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeInterchangeable
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
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
import Tablet.rutcor
import Tablet.sc2
import Tablet.step1
import Tablet.ElementarySingleBoundaryInterchangeable
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Mathlib.Tactic.ClearExcept

-- [TABLET NODE: ChangeLemmaBothInside]
theorem ChangeLemmaBothInside {V E : Type*}
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
        vb ∈ TreeSequenceVertexSet A) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    (0 < H.dividerCount ∧
        (alpha ∈ TreeMissingColors phi Tnq ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dnq) →
      sameComponent) ∧
    (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn) →
      sameComponent) ∧
    (alpha ∈ TreeMissingColors phi A ∧
        TreeColorSetClosed G phi A {alpha} →
      sameComponent ∧ TreeInterchangeable G A phi alpha beta) := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let a := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let b := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans {U W Z : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W)
      (hWZ : TreeSequenceInitialSegment W Z) :
      TreeSequenceInitialSegment U Z := by
    clear * - hUW hWZ
    refine ⟨hUW.1.trans hWZ.1, ?_, ?_⟩
    · intro j
      exact (hWZ.2.1 (Fin.castLE (Nat.succ_le_succ hUW.1) j)).trans
        (hUW.2.1 j)
    · intro j
      exact (hWZ.2.2 (Fin.castLE hUW.1 j)).trans (hUW.2.2 j)
  have stageChain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    clear * - H trans
    intro j
    induction j with
    | zero =>
        intro hj i hi
        have hi0 : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ j ih =>
        intro hj i hi
        by_cases heq : i.val = j + 1
        · have heq' : i = ⟨j + 1, hj⟩ := Fin.ext heq
          subst i
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · exact trans (ih (by omega) i (by omega))
            (H.nested ⟨j, by omega⟩)
  have starStage (r : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ) := by
    clear * - H r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have starChain (r s : Fin (H.dividerCount + 1)) (hrs : r ≤ s) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (HierarchyStarredStage H s) := by
    clear * - H r s hrs stageChain starStage trans
    by_cases heq : r = s
    · subst s
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · have hrlt : r.val < s.val := by
        have := Fin.le_iff_val_le_val.mp hrs
        have : r.val ≠ s.val := fun h => heq (Fin.ext h)
        omega
      have hs : s ≠ 0 := by intro hs; subst s; simp at hrlt
      have hstar : HierarchyStarredStage H s = H.stage s.castSucc := by
        rw [← Fin.succ_pred s hs]
        rfl
      rw [hstar]
      exact trans (starStage r)
        (stageChain s.val (by omega) r.succ (by simp; omega))
  have hAT : TreeSequenceInitialSegment A T := by
    have hh := starStage q
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa [hlast, H.terminalStage] using hh
  have hATy : TreeSequenceInitialSegment A Ty := by
    clear * - hAT A Ty
    have hlen : A.length ≤ Ty.length := by
      change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
      exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro j
      change T.vertex _ = A.vertex j
      exact hAT.2.1 j
    · intro j
      change T.edge _ = A.edge j
      exact hAT.2.2 j
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have helemA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv hne'
    exact hprefixElementary
      (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) hne'
  have helemStar (r : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)) := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset
      (starChain r q (Fin.le_last r))
    intro u hu v hv hne'
    exact helemA (hsub hu) (hsub hv) hne'
  have missingFirst (c : Fin k) (hc : c ∈ TreeMissingColors phi Ty) :
      c ∈ MissingColors G phi
        (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
    clear * - c hc hTyT
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hTyT hv
    obtain ⟨j, hj⟩ : ∃ j, T.vertex j = v := by
      simpa [TreeSequenceVertexSet] using hvT
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G phi (T.vertex j)
    have hcandidates : candidates.Nonempty := by
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa [hj] using hcv
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hcandidates]
    exact (Finset.mem_filter.mp (Finset.min'_mem candidates hcandidates)).2
  have haMissing : alpha ∈ MissingColors G phi a :=
    missingFirst alpha hmissingPrefix.1
  have hbMissing : beta ∈ MissingColors G phi b :=
    missingFirst beta hmissingPrefix.2
  have haA : a ∈ TreeSequenceVertexSet A := hlocation.1
  have hbA : b ∈ TreeSequenceVertexSet A := hlocation.2
  have pathMissing (c d : Fin k) (hcd : c ≠ d) (v : V)
      (hc : c ∈ MissingColors G phi v) :
      TwoColorPathComponent G phi c d (Sum.inl v) := by
    clear * - c d hcd v hc hproper
    refine ⟨hcd, Sum.inl v, ?_, ?_⟩
    · change (TwoColorIncidenceGraph G phi c d).connectedComponentMk
          (Sum.inl v) =
        (TwoColorIncidenceGraph G phi c d).connectedComponentMk (Sum.inl v)
      rfl
    · letI : Fintype
          ((TwoColorIncidenceGraph G phi c d).neighborSet (Sum.inl v)) :=
        Fintype.ofFinite _
      have hcard : Fintype.card
          ((TwoColorIncidenceGraph G phi c d).neighborSet (Sum.inl v)) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact MissingColorIncidenceEndpoint G phi c d hcd hproper v hc
      intro x hx y hy
      exact congrArg Subtype.val
        (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
  have graphSwap (c d : Fin k) :
      TwoColorIncidenceGraph G phi c d = TwoColorIncidenceGraph G phi d c := by
    clear * - G phi c d
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  have componentSwap (c d : Fin k) (z : Sum V E) :
      TwoColorComponent G phi c d z = TwoColorComponent G phi d c z := by
    unfold TwoColorComponent
    rw [graphSwap]
  have interchangeableSwap (B : TreeSequence G e0) (c d : Fin k)
      (hi : TreeInterchangeable G B phi c d) :
      TreeInterchangeable G B phi d c := by
    clear * - hi componentSwap graphSwap
    intro z w hz hw hzB hwB
    have pathSwap (z : Sum V E)
        (hz : TwoColorPathComponent G phi d c z) :
        TwoColorPathComponent G phi c d z := by
      refine ⟨hz.1.symm, ?_⟩
      simpa only [componentSwap c d, graphSwap c d] using hz.2
    rw [← componentSwap c d z, ← componentSwap c d w]
    apply hi z w (pathSwap z hz) (pathSwap w hw)
    · simpa only [componentSwap c d] using hzB
    · simpa only [componentSwap c d] using hwB
  have equalFromInterchange (B : TreeSequence G e0)
      (haB : a ∈ TreeSequenceVertexSet B) (hbB : b ∈ TreeSequenceVertexSet B)
      (hi : TreeInterchangeable G B phi alpha beta) :
      TwoColorComponent G phi alpha beta (Sum.inl a) =
        TwoColorComponent G phi alpha beta (Sum.inl b) := by
    have hpb : TwoColorPathComponent G phi alpha beta (Sum.inl b) := by
      have hh := pathMissing beta alpha hne.symm b hbMissing
      refine ⟨hne, ?_⟩
      simpa only [componentSwap alpha beta, graphSwap alpha beta] using hh.2
    apply hi _ _ (pathMissing alpha beta hne a haMissing) hpb
    · exact ⟨a, haB, rfl⟩
    · exact ⟨b, hbB, rfl⟩
  have bothClosed (B : TreeSequence G e0)
      (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B))
      (hc : TreeColorSetClosed G phi B {alpha})
      (hd : TreeColorSetClosed G phi B {beta}) :
      TreeInterchangeable G B phi alpha beta := by
    apply ElementarySingleBoundaryInterchangeable G phi B alpha beta
      hproper helem (hc alpha (Finset.mem_singleton_self _))
    rw [hd beta (Finset.mem_singleton_self _)]
    simp
  have stableRefl (B : TreeSequence G e0) (D : Finset (Fin k)) :
      StableColoring B D phi phi :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hcombined : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi phi :=
    ⟨stableRefl _ _, stableRefl _ _⟩
  have hnonPEClosed
      (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE) :
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) := by
    have hp : 0 < ett.rounds := C.positive
    clear * - ett phi n Tn G hproper hone hnonPE hp
    have stableClosed (B : TreeSequence G e0) (D : Finset (Fin k))
        (psi : PartialEdgeColoring E k)
        (hppsi : IsProperEdgeColoring G psi)
        (hopsi : IsOneEdgeUncolored psi e0)
        (hcpsi : ColoredVertexSetClosed G psi (TreeSequenceVertexSet B))
        (hs : StableColoring B D psi phi) :
        ColoredVertexSetClosed G phi (TreeSequenceVertexSet B) := by
      clear * - G phi e0 hproper hone B D psi hppsi hopsi hcpsi hs
      intro f c x hf hx hfc hcm
      have hincident : TreeIncidentEdge B f := by
        obtain ⟨u, hu, v, hv, huv⟩ := by
          simpa [BoundaryEdges] using hf
        refine ⟨u, hu, ?_⟩
        change u ∈ G.ends f
        rw [huv]
        exact Sym2.mem_mk_left _ _
      have hcmPrev : c ∈ MissingColors G psi x := by
        rw [← hs.2 x hx]
        exact hcm
      have hcTree : c ∈ TreeMissingColors psi B :=
        Finset.mem_biUnion.mpr ⟨x, hx, hcmPrev⟩
      have hfixed : phi f = psi f :=
        (sc1 G e0 B D psi phi hppsi hopsi hproper hone).mp hs
          f hincident (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hfc⟩)
      exact hcpsi hf hx (hfixed.symm.trans hfc) hcmPrev
    have hphi : phi = ett.series.data.coloring n := ett.generatingColoring
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hn : n ≠ 0 := by
          intro hh
          have hv := congrArg Fin.val hh
          simp [n] at hv
          omega
        exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        exact (hnonPE (by rw [targetEq]; exact currentKind)).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hi : i.succ = n := targetEq.symm
        have htree : ett.series.data.tree i.succ.castSucc = Tn := by
          simp [Tn, hi]
        have hselected : choice.selected = phi :=
          currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans hphi.symm)
        have hs : StableColoring Tn
            (TashkinovStoredColors ett.series.data i.castSucc)
            (ett.series.data.coloring i.castSucc) phi := by
          simpa only [htree, hselected] using choice.selectedStable
        exact @stableClosed Tn _ _ previousProper previousOneUncolored
          (by rw [← htree]; exact previousClosed) hs
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hi : i.succ = n := targetEq.symm
        have htree : ett.series.data.tree i.succ.castSucc = Tn := by
          simp [Tn, hi]
        have hcol : ett.series.data.coloring i.castSucc = phi :=
          currentColoring.symm.trans
            ((congrArg ett.series.data.coloring hi).trans hphi.symm)
        have hc : ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
            (TreeSequenceVertexSet Tn) := by
          rw [← htree]
          exact previousClosed
        exact @Eq.mp _ _
          (congrArg (fun psi => ColoredVertexSetClosed G psi
            (TreeSequenceVertexSet Tn)) hcol) hc
  have nonPEMissingClosed
      (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE)
      (c : Fin k) (hc : c ∈ TreeMissingColors phi Tn) :
      TreeColorSetClosed G phi Tn {c} := by
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨x, hx, hcx⟩ := Finset.mem_biUnion.mp hc
    have hfd : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
        phi f = some c := by simpa [BoundaryColorEdges] using hf
    exact hnonPEClosed hnonPE hfd.1 hx hfd.2 hcx
  have closedStar (r : Fin (H.dividerCount + 1))
      (c d : Fin k) (hcd : c ≠ d)
      (hc : c ∈ TreeMissingColors phi (HierarchyStarredStage H r))
      (hd : d ∈ TreeMissingColors phi (HierarchyStarredStage H r))
      (hclosed : TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}) :
      TreeInterchangeable G (HierarchyStarredStage H r) phi c d := by
    cases r using Fin.cases with
    | zero =>
      change c ∈ TreeMissingColors phi base.core at hc
      change d ∈ TreeMissingColors phi base.core at hd
      change TreeColorSetClosed G phi base.core {c} at hclosed
      change TreeInterchangeable G base.core phi c d
      by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
      · exact (interchange G k e0 input T phi phi ett C.maximum C.positive
          hlower hPE base hproper hone hcombined c d).2.2.1 hc hclosed
      · have hcore : base.core = Tn := base.nonparallel hPE
        have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Tn) := by
          rw [← hcore]
          exact helemStar 0
        have hempty : BoundaryColorEdges G phi (TreeSequenceVertexSet Tn) d = ∅ :=
          nonPEMissingClosed hPE d (by simpa only [hcore] using hd)
            d (Finset.mem_singleton_self _)
        rw [hcore]
        exact ElementarySingleBoundaryInterchangeable G phi Tn c d hproper helem
          (by simpa only [hcore] using hclosed c (Finset.mem_singleton_self _))
          (by rw [hempty]; simp)
    | succ i =>
      exact step1 G k e0 input T phi ett C.maximum C.positive hproper hone
        hlower base H C.good hfewer hlarge i c d hc hcd hclosed
  have coreSame (haCore : a ∈ TreeSequenceVertexSet base.core)
      (hbCore : b ∈ TreeSequenceVertexSet base.core) :
      TwoColorComponent G phi alpha beta (Sum.inl a) =
        TwoColorComponent G phi alpha beta (Sum.inl b) := by
    by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨hu⟩⟩ := base.parallel hPE
      have haUnion : a ∈ TreeSequenceVertexSet Tn ∨
          a ∈ TreeSequenceVertexSet base.closure := by
        simpa only [hu.vertexSet, Finset.mem_union] using haCore
      have hbUnion : b ∈ TreeSequenceVertexSet Tn ∨
          b ∈ TreeSequenceVertexSet base.closure := by
        simpa only [hu.vertexSet, Finset.mem_union] using hbCore
      have hi := interchange G k e0 input T phi phi ett C.maximum C.positive
        hlower hPE base hproper hone hcombined alpha beta
      have hj := interchange G k e0 input T phi phi ett C.maximum C.positive
        hlower hPE base hproper hone hcombined beta alpha
      rcases haUnion with haN | haR <;> rcases hbUnion with hbN | hbR
      · exact equalFromInterchange Tn haN hbN
          (hi.2.1 (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩))
      · exact equalFromInterchange base.core haCore hbCore
          (hi.2.2.2 (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩)
            (Finset.mem_biUnion.mpr ⟨b, hbR, hbMissing⟩))
      · exact equalFromInterchange base.core haCore hbCore
          (interchangeableSwap base.core beta alpha
            (hj.2.2.2 (Finset.mem_biUnion.mpr ⟨b, hbN, hbMissing⟩)
              (Finset.mem_biUnion.mpr ⟨a, haR, haMissing⟩)))
      · exact equalFromInterchange base.closure haR hbR
          (hi.1 (Finset.mem_biUnion.mpr ⟨a, haR, haMissing⟩))
    · have hcore : base.core = Tn := base.nonparallel hPE
      have haN : a ∈ TreeSequenceVertexSet Tn := by simpa only [hcore] using haCore
      have hbN : b ∈ TreeSequenceVertexSet Tn := by simpa only [hcore] using hbCore
      have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Tn) := by
        rw [← hcore]
        exact helemStar 0
      exact equalFromInterchange Tn haN hbN
        (bothClosed Tn helem
          (nonPEMissingClosed hPE alpha (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩))
          (nonPEMissingClosed hPE beta (Finset.mem_biUnion.mpr ⟨b, hbN, hbMissing⟩)))
  have haMissingA : alpha ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨a, haA, haMissing⟩
  have hbMissingA : beta ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨b, hbA, hbMissing⟩
  have hsame : TwoColorComponent G phi alpha beta (Sum.inl a) =
      TwoColorComponent G phi alpha beta (Sum.inl b) := by
    by_cases haClosed : TreeColorSetClosed G phi A {alpha}
    · by_cases hbClosed : TreeColorSetClosed G phi A {beta}
      · exact equalFromInterchange A haA hbA (bothClosed A helemA haClosed hbClosed)
      · exact equalFromInterchange A haA hbA
          (closedStar q alpha beta hne haMissingA hbMissingA haClosed)
    · by_cases hbClosed : TreeColorSetClosed G phi A {beta}
      · exact equalFromInterchange A haA hbA
          (interchangeableSwap A beta alpha
            (closedStar q beta alpha hne.symm hbMissingA haMissingA hbClosed))
      · -- Descend to the least starred stage containing both witnesses.
        let P (r : ℕ) : Prop := ∃ hr : r ≤ H.dividerCount,
          a ∈ TreeSequenceVertexSet (HierarchyStarredStage H ⟨r, by omega⟩) ∧
          b ∈ TreeSequenceVertexSet (HierarchyStarredStage H ⟨r, by omega⟩)
        have hex : ∃ r, P r := ⟨H.dividerCount, le_rfl, haA, hbA⟩
        let r := Nat.find hex
        obtain ⟨hr, har, hbr⟩ : P r := Nat.find_spec hex
        by_cases hr0 : r = 0
        · have hz : (⟨r, by omega⟩ : Fin (H.dividerCount + 1)) = 0 := Fin.ext hr0
          rw [hz] at har hbr
          exact coreSame har hbr
        · let i : Fin H.dividerCount := ⟨r - 1, by omega⟩
          have hri : (⟨r, by omega⟩ : Fin (H.dividerCount + 1)) = i.succ := by
            apply Fin.ext
            simp [i]
            omega
          have haCurrent : a ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) := by
            simpa only [hri, HierarchyStarredStage, Fin.cases_succ] using har
          have hbCurrent : b ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) := by
            simpa only [hri, HierarchyStarredStage, Fin.cases_succ] using hbr
          have hnotPrevious : ¬ (a ∈ TreeSequenceVertexSet
                (HierarchyStarredStage H i.castSucc) ∧
              b ∈ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)) := by
            intro hab
            have hprev : P (r - 1) := ⟨by omega, hab.1, hab.2⟩
            have hmin := Nat.find_min' hex hprev
            change r ≤ r - 1 at hmin
            omega
          have helemCurrent : ColoredVertexSetElementary G phi
              (TreeSequenceVertexSet (H.stage i.succ.castSucc)) := helemStar i.succ
          have ham : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc) :=
            Finset.mem_biUnion.mpr ⟨a, haCurrent, haMissing⟩
          have hbm : beta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) :=
            Finset.mem_biUnion.mpr ⟨b, hbCurrent, hbMissing⟩
          by_cases haPrev : a ∈ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)
          · have hbPrev : b ∉ TreeSequenceVertexSet
                (HierarchyStarredStage H i.castSucc) := fun hb => hnotPrevious ⟨haPrev, hb⟩
            have hnew := GoodHierarchyNewMissingClosed C.good i helemCurrent beta
              (Finset.mem_biUnion.mpr
                ⟨b, Finset.mem_sdiff.mpr ⟨hbCurrent, hbPrev⟩, hbMissing⟩)
            have hclosed : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {beta} := by
              intro d hd
              have hd' := Finset.mem_singleton.mp hd
              simpa only [hd'] using hnew
            exact equalFromInterchange (H.stage i.succ.castSucc) haCurrent hbCurrent
              (interchangeableSwap _ beta alpha
                (closedStar i.succ beta alpha hne.symm hbm ham hclosed))
          · have hnew := GoodHierarchyNewMissingClosed C.good i helemCurrent alpha
              (Finset.mem_biUnion.mpr
                ⟨a, Finset.mem_sdiff.mpr ⟨haCurrent, haPrev⟩, haMissing⟩)
            have hclosed : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {alpha} := by
              intro d hd
              have hd' := Finset.mem_singleton.mp hd
              simpa only [hd'] using hnew
            exact equalFromInterchange (H.stage i.succ.castSucc) haCurrent hbCurrent
              (closedStar i.succ alpha beta hne ham hbm hclosed)
  refine ⟨fun _ => hsame, fun _ => hsame, ?_⟩
  intro hc
  exact ⟨hsame, closedStar q alpha beta hne hc.1 hbMissingA hc.2⟩
