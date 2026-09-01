import Tablet.ColoredVertexSetElementary
import Tablet.GoodHierarchy
import Tablet.HierarchyPathNumber
import Tablet.HierarchyStoredColorsCardinality
import Tablet.TreeSequencePrefix

-- [TABLET NODE: NineN]
theorem NineN {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hprefixElementary :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let p := HierarchyPathNumber H
      let Ty := fun i : ℕ =>
        TreeSequencePrefix T (min (A.length + i) T.length)
          (by have hA := A.positive; have hT := T.positive; omega)
          (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (Ty (p - 1))))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let p := HierarchyPathNumber H
    let Ty := fun i : ℕ =>
      TreeSequencePrefix T (min (A.length + i) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G phi v)
    let tailUsed := fun i : ℕ =>
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < A.length + i ∧
            phi (T.edge r) = some c
    let available := fun i : ℕ =>
      (TreeMissingColors phi (Ty i) \ baseExtraMissing) \ tailUsed i
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (good.gamma q)
    ∀ i : ℕ, i < p →
      2 * ett.rounds + 11 ≤ (available i).card ∧
      ((available i \ (Gamma ∪ D)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h : Fin 7,
            eta h ∈ D ∧ eta h ∈ TreeMissingColors phi (Ty i) ∧
              Disjoint (good.gamma q (eta h) ∪ {eta h}) (tailUsed i)) := by
-- BODY
  sorry
