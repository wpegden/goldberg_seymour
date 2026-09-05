import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleOneAdditionPositiveDividerImpossible
import Tablet.HierarchyCounterexampleOneAdditionZeroDividerImpossible

-- [TABLET NODE: HierarchyCounterexampleTailAtLeastTwo]
theorem HierarchyCounterexampleTailAtLeastTwo {V E : Type*}
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
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card) :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    2 ≤ T.length - A.length := by
-- BODY
  have hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      hproper hone hlower hfewer hminimal hlarge
  dsimp only
  by_contra hnotTwo
  have hpositiveTail :
      0 < T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length := by
    have lastStage : ∀ (d : ℕ) (s : Fin (d + 2) → TreeSequence G e0)
        (core : TreeSequence G e0), 0 < d →
        Fin.cases core (fun i : Fin d => s i.castSucc.succ) (Fin.last d) =
          s (Fin.last d).castSucc := by
      intro d s core hd
      cases d with
      | zero => omega
      | succ n =>
        have hi : Fin.last (n + 1) = (Fin.last n).succ := by
          apply Fin.ext
          rfl
        rw [hi]
        rfl
    have zeroStage : ∀ (d : ℕ) (s : Fin (d + 2) → TreeSequence G e0)
        (core : TreeSequence G e0), d = 0 →
        Fin.cases core (fun i : Fin d => s i.castSucc.succ) (Fin.last d) =
          core := by
      intro d s core hd
      subst d
      rfl
    by_cases hq : 0 < C.hierarchy.dividerCount
    · have hAeq : HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount) =
          C.hierarchy.stage (Fin.last C.hierarchy.dividerCount).castSucc := by
        unfold HierarchyStarredStage
        exact lastStage _ _ _ hq
      have hstep := C.hierarchy.strict (Fin.last C.hierarchy.dividerCount)
      have hlenA := congrArg TreeSequence.length hAeq
      have hterm : C.hierarchy.stage (Fin.last C.hierarchy.dividerCount).succ = T := by
        rw [show (Fin.last C.hierarchy.dividerCount).succ =
            Fin.last (C.hierarchy.dividerCount + 1) by
              apply Fin.ext
              rfl]
        exact C.hierarchy.terminalStage
      have hlenT := congrArg TreeSequence.length hterm
      omega
    · have hzero : C.hierarchy.dividerCount = 0 := Nat.eq_zero_of_not_pos hq
      have hAeq : HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount) = base.core := by
        unfold HierarchyStarredStage
        exact zeroStage _ _ _ hzero
      have hseg : TreeSequenceInitialSegment
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)) T := by
        have hc := C.hierarchy.coreInsideFirst
        rw [show (⟨1, by omega⟩ : Fin (C.hierarchy.dividerCount + 2)) =
            Fin.last (C.hierarchy.dividerCount + 1) by
              apply Fin.ext
              simp [hzero]] at hc
        rw [hAeq]
        simpa [C.hierarchy.terminalStage, hzero] using hc
      by_contra hnon
      have hle :
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length ≤ T.length := hseg.1
      have heq :
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length = T.length := by
        omega
      have equalTrees : ∀ {X Y : TreeSequence G e0},
          TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y := by
        intro X Y hXY hlen
        rcases hXY with ⟨hle, hv, he⟩
        cases X with
        | mk lx px vx ex vix eix fx ax =>
          cases Y with
          | mk ly py vy ey viy eiy fy ay =>
            simp only at hlen
            subst ly
            rw [TreeSequence.mk.injEq]
            refine ⟨rfl, ?_, ?_⟩
            · apply heq_of_eq
              funext j
              simpa only [Fin.castLE] using (hv j).symm
            · apply heq_of_eq
              funext j
              simpa only [Fin.castLE] using (he j).symm
      have htrees :
          HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount) = T := by
        exact equalTrees hseg heq
      have htailzero : T.length -
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length = 0 :=
        Nat.eq_zero_of_not_pos hnon
      have prefixFull : ∀ (X : TreeSequence G e0) (hp : 1 ≤ X.length)
          (hq : X.length ≤ X.length),
          TreeSequencePrefix X X.length hp hq = X := by
        intro X hp hq
        apply equalTrees
        refine ⟨le_rfl, ?_, ?_⟩
        · intro i
          apply congrArg X.vertex
          apply Fin.ext
          rfl
        · intro i
          apply congrArg X.edge
          apply Fin.ext
          rfl
        · rfl
      have helem : ColoredVertexSetElementary G phi
          (TreeSequenceVertexSet T) := by
        dsimp only at hprefixElementary
        intro u hu v hv huv
        apply hprefixElementary (u := u) (v := v)
        · simpa [htailzero, htrees, prefixFull] using hu
        · simpa [htailzero, htrees, prefixFull] using hv
        · exact huv
      exact C.notElementary helem
  have honeAddition :
      T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length = 1 := by
    omega
  rcases Nat.eq_zero_or_pos C.hierarchy.dividerCount with hzero | hpositive
  · exact HierarchyCounterexampleOneAdditionZeroDividerImpossible
      G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      honeAddition hprefixElementary hzero
  · exact HierarchyCounterexampleOneAdditionPositiveDividerImpossible
      G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      honeAddition hprefixElementary hpositive
