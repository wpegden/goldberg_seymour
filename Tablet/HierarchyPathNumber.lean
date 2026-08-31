import Mathlib.Order.Interval.Finset.Nat
import Tablet.HierarchyStarredStage

open scoped Sym2

-- [TABLET NODE: HierarchyPathNumber]
noncomputable def HierarchyPathNumber {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base) : ℕ := by
-- BODY
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let tailLength := T.length - A.length
  let candidates := (Finset.Icc 1 tailLength).filter fun i =>
    ∀ r : Fin T.length, A.length + i ≤ r.val →
      G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)
  exact if h : candidates.Nonempty then candidates.min' h else tailLength
