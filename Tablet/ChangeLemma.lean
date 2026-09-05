import Tablet.ChangeLemmaBothInside
import Tablet.ChangeLemmaBothOutside
import Tablet.ChangeLemmaInsideOutside
import Tablet.HierarchyCounterexample
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.TashkinovHierarchy
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: ChangeLemma]
theorem ChangeLemma {V E : Type*}
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
                phi (T.edge t) = some c)) :
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
  have segmentTrans : ∀ X Y Z : TreeSequence G e0,
      TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z →
        TreeSequenceInitialSegment X Z := by
    intro X Y Z hxy hyz
    rcases hxy with ⟨hxy, hvxy, hexy⟩
    rcases hyz with ⟨hyz, hvyz, heyz⟩
    have h : X.length ≤ Z.length := by omega
    refine ⟨h, ?_, ?_⟩
    · intro i
      have hi := hvyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      have hj := hvxy i
      have he : Fin.castLE (Nat.succ_le_succ h) i =
          Fin.castLE (Nat.succ_le_succ hyz) (Fin.castLE (Nat.succ_le_succ hxy) i) := by
        apply Fin.ext
        rfl
      rw [he]
      exact hi.trans hj
    · intro i
      have hi := heyz (Fin.castLE hxy i)
      have hj := hexy i
      have he : Fin.castLE h i = Fin.castLE hyz (Fin.castLE hxy i) := by
        apply Fin.ext
        rfl
      rw [he]
      exact hi.trans hj
  have stageToEnd : ∀ i : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage i.castSucc)
        (H.stage (Fin.last (H.dividerCount + 1))) := by
    have forward : ∀ i : Fin (H.dividerCount + 1), ∀ r : ℕ,
        ∀ hbound : i.val + r ≤ H.dividerCount + 1,
        TreeSequenceInitialSegment (H.stage i.castSucc)
          (H.stage ⟨i.val + r, by omega⟩) := by
      intro i r
      induction r with
      | zero =>
          intro h
          exact ⟨Nat.le_refl _, by intro j; rfl, by intro j; rfl⟩
      | succ r ih =>
          intro hbound
          let j : Fin (H.dividerCount + 1) := ⟨i.val + r, by omega⟩
          have hfirst := ih (by omega)
          have hstep := H.nested j
          have hmid : H.stage j.castSucc = H.stage ⟨i.val + r, by omega⟩ := by
            congr 1
          have hlast : H.stage j.succ =
              H.stage ⟨i.val + Nat.succ r, by omega⟩ := by
            apply congrArg H.stage
            apply Fin.ext
            rfl
          rw [← hmid] at hfirst
          rw [hlast] at hstep
          exact segmentTrans _ _ _ hfirst hstep
    intro i
    have hf := forward i (H.dividerCount + 1 - i.val) (by omega)
    simpa [Fin.last] using hf
  have hAsegment : TreeSequenceInitialSegment A T := by
    rw [show T = H.stage (Fin.last (H.dividerCount + 1)) from H.terminalStage.symm]
    by_cases hq : H.dividerCount = 0
    · have hA : A = base.core := by
        dsimp [A, q, HierarchyStarredStage]
        have hz : Fin.last H.dividerCount =
            (0 : Fin (H.dividerCount + 1)) := by
          apply Fin.ext
          simp [hq]
        rw [hz]
        rfl
      have hs : H.stage (Fin.last (H.dividerCount + 1)) = H.stage 1 := by
        apply congrArg H.stage
        apply Fin.ext
        simp [hq]
      simpa [hA, hs] using H.coreInsideFirst
    · have hs : A = H.stage q.castSucc := by
        have hqsucc : ∃ r : Fin H.dividerCount, q = r.succ := by
          refine ⟨⟨H.dividerCount - 1, by omega⟩, ?_⟩
          apply Fin.ext
          simp [q]
          omega
        rcases hqsucc with ⟨r, hr⟩
        change HierarchyStarredStage H q = H.stage q.castSucc
        rw [hr]
        dsimp [HierarchyStarredStage]
      rw [hs]
      exact stageToEnd q
  have missing_to_vertex : ∀ c : Fin k,
      c ∈ TreeMissingColors phi A →
        T.vertex (HierarchyFirstMissingPosition phi T c) ∈
          TreeSequenceVertexSet A := by
    intro c hc
    unfold TreeMissingColors at hc
    simp only [Finset.mem_biUnion] at hc
    rcases hc with ⟨v, hv, hvc⟩
    unfold HierarchyFirstMissingPosition
    unfold TreeSequenceVertexSet at hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨ia, hia⟩
    rcases hAsegment with ⟨hlen, hvseg, heseg⟩
    let iaT : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hlen) ia
    have hvertex : T.vertex iaT = A.vertex ia := by
      exact hvseg ia
    have hca : c ∈ MissingColors G phi (T.vertex iaT) := by
      rw [hvertex, hia]
      exact hvc
    let candidates : Finset (Fin (T.length + 1)) :=
      Finset.univ.filter fun i => c ∈ MissingColors G phi (T.vertex i)
    have hcand : candidates.Nonempty := ⟨iaT, by simp [candidates, hca]⟩
    have hpos : HierarchyFirstMissingPosition phi T c = candidates.min' hcand := by
      simp [HierarchyFirstMissingPosition, candidates, hcand]
    have hmin : HierarchyFirstMissingPosition phi T c ≤ iaT := by
      rw [hpos]
      exact Finset.min'_le candidates iaT (by simp [candidates, hca])
    have hbound : (HierarchyFirstMissingPosition phi T c).val ≤ A.length := by
      dsimp [iaT] at hmin
      change (HierarchyFirstMissingPosition phi T c).val ≤ iaT.val at hmin
      exact le_trans hmin (Nat.le_of_lt_succ ia.isLt)
    let x : Fin (A.length + 1) :=
      ⟨(HierarchyFirstMissingPosition phi T c).val, Nat.lt_succ_of_le hbound⟩
    have hx : T.vertex (Fin.castLE (Nat.succ_le_succ hlen) x) =
        T.vertex (HierarchyFirstMissingPosition phi T c) := by
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    rw [← hvseg x]
    simpa [HierarchyFirstMissingPosition, candidates, hcand] using hx
  have prefixClosed : ∀ u v : V, TreeVertexOrder T u v →
      v ∈ TreeSequenceVertexSet A → u ∈ TreeSequenceVertexSet A := by
    intro u v huv hv
    rcases huv with ⟨i, j, hi, hj, hij⟩
    unfold TreeSequenceVertexSet at hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨x, hx⟩
    rcases hAsegment with ⟨hlen, hvseg, heseg⟩
    have heq : T.vertex j = T.vertex (Fin.castLE (Nat.succ_le_succ hlen) x) := by
      exact hj.trans (hx.symm.trans (hvseg x).symm)
    have hijx := T.vertex_injective heq
    have hib : i.val ≤ A.length := by
      have : i.val < j.val := hij
      have : j.val = x.val := congrArg Fin.val hijx
      omega
    let y : Fin (A.length + 1) := ⟨i.val, Nat.lt_succ_of_le hib⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨y, Finset.mem_univ _, ?_⟩
    have heqy : T.vertex (Fin.castLE (Nat.succ_le_succ hlen) y) = T.vertex i := by
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    rw [← hvseg y]
    exact heqy.symm.trans hi
  by_cases ha : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
      TreeSequenceVertexSet A
  · by_cases hb : T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet A
    · exact ChangeLemmaBothInside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
    · exact ChangeLemmaInsideOutside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
  · by_cases hb : T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet A
    · have hna : alpha ∉ TreeMissingColors phi A := by
        intro h
        exact ha (missing_to_vertex alpha h)
      have ho := horderedUnused (Or.inl hna)
      exact (ha (prefixClosed _ _ ho.1 hb)).elim
    · have hmain := ChangeLemmaBothOutside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
      refine ⟨hmain.1, hmain.2, ?_⟩
      intro h
      exact (ha (missing_to_vertex alpha h.1)).elim
