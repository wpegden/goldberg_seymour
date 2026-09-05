import Tablet.ChangeLemmaMixedClosedFinal
import Tablet.ChangeLemmaMixedLargestClosed
import Tablet.ChangeLemmaMixedNoClosed
import Tablet.ChangeLemmaMixedZeroNonclosed

-- [TABLET NODE: ChangeLemmaInsideOutside]
theorem ChangeLemmaInsideOutside {V E : Type*}
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
        vb ∉ TreeSequenceVertexSet A) :
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
  let ell := T.length - A.length
  let prefixLength := min (A.length + (ell - 1)) T.length
  let Ty := TreeSequencePrefix T prefixLength
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
    TwoColorComponent G phi alpha beta (Sum.inl vb)
  have hmissingPrefix' : alpha ∈ TreeMissingColors phi Ty ∧
      beta ∈ TreeMissingColors phi Ty := by
    simpa [H, q, A, ell, prefixLength, Ty] using hmissingPrefix
  have firstMissingIsMissing : ∀ c : Fin k,
      c ∈ TreeMissingColors phi Ty →
        c ∈ MissingColors G phi
          (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
    intro c hc
    unfold TreeMissingColors at hc
    simp only [Finset.mem_biUnion] at hc
    obtain ⟨v, hv, hcv⟩ := hc
    unfold TreeSequenceVertexSet at hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, rfl⟩ := hv
    let iT : Fin (T.length + 1) := Fin.castLE
      (Nat.succ_le_succ (Nat.min_le_right _ _)) i
    have hci : c ∈ MissingColors G phi (T.vertex iT) := by
      simpa [Ty, prefixLength, TreeSequencePrefix, iT] using hcv
    let candidates : Finset (Fin (T.length + 1)) :=
      Finset.univ.filter fun j => c ∈ MissingColors G phi (T.vertex j)
    have hcandidates : candidates.Nonempty := by
      refine ⟨iT, ?_⟩
      simp [candidates, hci]
    have hmin := Finset.min'_mem candidates hcandidates
    have hmin' : c ∈ MissingColors G phi
        (T.vertex (candidates.min' hcandidates)) :=
      (Finset.mem_filter.mp hmin).2
    simpa [HierarchyFirstMissingPosition, candidates, hcandidates] using hmin'
  have hlocation' : va ∈ TreeSequenceVertexSet A ∧
      vb ∉ TreeSequenceVertexSet A := by
    simpa [H, q, A, va, vb] using hlocation
  have hmissingA : alpha ∈ TreeMissingColors phi A := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr
      ⟨va, hlocation'.1, firstMissingIsMissing alpha hmissingPrefix'.1⟩
  have closedCase (hclosed : TreeColorSetClosed G phi A {alpha}) :
      sameComponent ∧ TreeInterchangeable G A phi alpha beta := by
    simpa [H, q, A, va, vb, sameComponent] using
      (ChangeLemmaMixedClosedFinal G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused hlocation ⟨hmissingA, hclosed⟩)
  have positiveNonclosedCase (hpositive : 0 < H.dividerCount)
      (hnotclosed : ¬ TreeColorSetClosed G phi A {alpha}) :
      sameComponent := by
    by_cases hex : ∃ r : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {alpha}
    · let closedStages : Finset (Fin (H.dividerCount + 1)) :=
        Finset.univ.filter fun r =>
          TreeColorSetClosed G phi (HierarchyStarredStage H r) {alpha}
      have hclosedStages : closedStages.Nonempty := by
        obtain ⟨r, hr⟩ := hex
        exact ⟨r, by simp [closedStages, hr]⟩
      obtain ⟨r, hrmem, hrmax⟩ :=
        Finset.exists_max_image closedStages (fun s => s.val) hclosedStages
      have hrclosed : TreeColorSetClosed G phi
          (HierarchyStarredStage H r) {alpha} := by
        exact (Finset.mem_filter.mp hrmem).2
      have hrne : r.val ≠ H.dividerCount := by
        intro hre
        apply hnotclosed
        have hrq : r = q := by
          apply Fin.ext
          simpa [q, Fin.last] using hre
        simpa [A, hrq] using hrclosed
      have hrlt : r.val < H.dividerCount := by omega
      have hlater : ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
          ¬ TreeColorSetClosed G phi
            (HierarchyStarredStage H s) {alpha} := by
        intro s hrs hsclosed
        have hsmem : s ∈ closedStages := by
          simp [closedStages, hsclosed]
        have hle := hrmax s hsmem
        omega
      simpa [H, q, A, va, vb, sameComponent] using
        (ChangeLemmaMixedLargestClosed G k e0 input T phi ett base C hproper hone
          hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
          hmissingPrefix horderedUnused hlocation r
          ⟨hpositive, hrlt, hrclosed, hlater⟩)
    · have hnone : ∀ s : Fin (H.dividerCount + 1),
          ¬ TreeColorSetClosed G phi
            (HierarchyStarredStage H s) {alpha} := by
        intro s hs
        exact hex ⟨s, hs⟩
      simpa [H, q, A, va, vb, sameComponent] using
        (ChangeLemmaMixedNoClosed G k e0 input T phi ett base C hproper hone
          hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
          hmissingPrefix horderedUnused hlocation ⟨hpositive, hnone⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hpositive, halt⟩
    by_cases hclosed : TreeColorSetClosed G phi A {alpha}
    · exact (closedCase hclosed).1
    · exact positiveNonclosedCase hpositive hclosed
  · rintro ⟨hzero, halt⟩
    by_cases hclosed : TreeColorSetClosed G phi A {alpha}
    · exact (closedCase hclosed).1
    · simpa [H, q, A, va, vb, sameComponent] using
        (ChangeLemmaMixedZeroNonclosed G k e0 input T phi ett base C hproper hone
          hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
          hmissingPrefix horderedUnused hlocation ⟨hzero, hclosed, halt⟩)
  · intro hclosed
    exact closedCase hclosed.2
