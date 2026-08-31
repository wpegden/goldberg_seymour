import Tablet.HierarchyBase
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix

-- [TABLET NODE: TashkinovHierarchy]
structure TashkinovHierarchy {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (base : HierarchyBase ett phi) where
-- BODY
  dividerCount : ℕ
  stage : Fin (dividerCount + 2) → TreeSequence G e0
  baseStage : stage 0 =
    ett.series.data.tree (Fin.last ett.rounds).castSucc
  terminalStage : stage (Fin.last (dividerCount + 1)) = T
  nested : ∀ j : Fin (dividerCount + 1),
    TreeSequenceInitialSegment (stage j.castSucc) (stage j.succ)
  strict : ∀ j : Fin (dividerCount + 1),
    (stage j.castSucc).length < (stage j.succ).length
  dividerPosition : Fin dividerCount → Fin (T.length + 1)
  dividerPositive : ∀ i, 1 ≤ (dividerPosition i).val
  dividerIncreasing : ∀ i j, i.val < j.val →
    (dividerPosition i).val < (dividerPosition j).val
  dividerStage : ∀ i : Fin dividerCount,
    stage ⟨i.val + 1, by omega⟩ =
      TreeSequencePrefix T (dividerPosition i).val (dividerPositive i)
        (Nat.le_of_lt_succ (dividerPosition i).isLt)
  coreInsideFirst : TreeSequenceInitialSegment base.core (stage ⟨1, by omega⟩)
